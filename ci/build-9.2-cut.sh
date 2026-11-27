#!/usr/bin/env bash
# ci/build-9.2-cut.sh: build Rocq at one fixed commit (the "cut"), build the rocq-lean-import plugin against
# it, and run the test suite. The GitHub workflow .github/workflows/build-9.2-cut.yml and batch Jobs call this
# one script; `ci/build-9.2-cut.sh --help` lists its modes.
#
# Layout: settings, helpers, main. The pins and settings build_switch builds the opam root from are in
# ci/cut-settings.sh, which this script sources, and the self-test (--self-test) is in
# ci/build-9.2-cut-selftest.sh. main is the only function that decides an outcome: which verdict line to print
# and which status to exit with. The helpers (check_inventory, revert_fix_prepare, stack_check, ...) gather facts
# and hand them back; they decide nothing.
#
# Exit status: 0 success; 1 a check, the build or a test failed; 2 usage error. --source-at: 3 a bad commit
# or test (or any other setup failure), 4 the plugin build failed, otherwise the test's own status.

set -u -o pipefail

SELF=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/$(basename -- "${BASH_SOURCE[0]}")
ROOT=$(cd -- "$(dirname -- "$SELF")/.." && pwd)

# ---- Settings -------------------------------------------------------------------------------------------------

# The inputs of build_switch, CUT_ROCQ_COMMIT among them: the workflow keys its cache of the opam root on that
# file alone.
SETTINGS=${SELF%/*}/cut-settings.sh
# shellcheck source=ci/cut-settings.sh
source "$SETTINGS" || exit 1
# The git-LFS batch endpoint of this repository; it answers download requests without authentication.
LFS_BATCH_URL=https://github.com/theorem-labs/rocq-lean-import.git/info/lfs/objects/batch

# CUT_STACK_KIB: the head's soft stack size, in KiB, for tests, --import and --check. Only a commit sets it
# by adding the line below; no line keeps the default soft stack. --revert-fix uses that setting on both
# sides unless the inventory row states a stack or the control reverts a change to the stack setting itself.
# Read the line from the file, not the shell variable: the environment variable of that name is ignored.
# The CUT_STACK_KIB=<integer> line, when a commit adds one, goes right below this line.
CUT_STACK_KIB=131072

CUT_ROOT=${CUT_ROOT:-/scratch/cs/cut} # opam root $CUT_ROOT/opam (switch "cut"), sources $CUT_ROOT/src
JOBS=${CUT_JOBS:-$(nproc 2>/dev/null || echo 2)}
export OPAMROOT=$CUT_ROOT/opam OPAMSWITCH=cut OPAMYES=1 OPAMCONFIRMLEVEL=unsafe-yes OPAMNODEPEXTS=1 \
  OPAMCOLOR=never OPAMROOTISOK=1 OPAMJOBS=$JOBS

SCRIPT_REL=ci/build-9.2-cut.sh
INVENTORY=tests/lean434_features.txt
PREDECLARED_TEST=tests/predeclared.v
PREDECLARED_TABLES=(get_predeclared_ind_any get_predeclared_def_any get_predeclared_ind_as_def_any)
GVISOR_STACK_CAP_KIB=131072 # gVisor caps the stack at 128 MiB
RT_BUILD_FAILED=125         # RUN_TEST's status when the plugin build, not the test, failed
# Rocq's message when `Set <Option Name>` names an option that does not exist (an error once
# `Set Warnings "+unknown-option".` precedes it); the quoted option name follows it. The cut prints it
# (theorem-labs/rocq 07e45e36 library/goptions.ml:435; seen in the suite's log of tests/entry_timeout.v).
UNKNOWN_OPTION_MSG='There is no flag or option with this name'
STACK_ANCHOR='# The CUT_STACK_KIB=<integer> line, when a commit adds one, goes right below this line.'
LFS_POINTER_HEAD='version https://git-lfs.github.com/spec/v1'
# A Redirect command at the start of a line of a test, its name captured; a commented-out one is none, as for
# REDIRECT in tests/check_expect.py. The one pattern of planted_cases, redirect_logs and r5_lines.
REDIRECT_RE='^[[:space:]]*Redirect[[:space:]]+"([^"]+)"'

# ---- Self-test stubs ------------------------------------------------------------------------------------------
# --self-test runs copies of this script with CUT_SELF_TEST_STUBS=1 set; only then are the variables below
# read. Each one names a command that replaces one real step:
#   CUT_STUB_RUN_TEST  replaces run_test_real (RUN_TEST): called as `<cmd> suite <tree>` or
#                      `<cmd> one <tree> <test name>`; exit 0 = pass, 125 = the plugin build failed, any
#                      other status = the test failed.
#   CUT_STUB_ULIMIT    replaces the stack read-back `ulimit -Ss` / `ulimit -Hs`: called as
#                      `<cmd> soft|hard <want>`, <want> being the KiB the setter was asked for or "-"; it
#                      prints the value. With it the real setter is skipped, since the limits it would set
#                      are not the ones the stub reports.
#   CUT_STUB_UNAME_R   replaces `uname -r`.
#   CUT_STUB_COMPILE   replaces `opam exec -- rocq compile` (--import).
#   CUT_STUB_CHECK     replaces `opam exec -- rocqchk` (--check).
# With CUT_SELF_TEST_STUBS=1 a missing switch is an error, never a build. The Rocq commit needs no stub: the
# self-test points CUT_ROOT at a directory whose rocq-commit file it writes for each case, and puts on PATH, for
# --source-at, a stand-in rocq in a root of its own with its own rocq-commit file.
stubbed() { [[ ${CUT_SELF_TEST_STUBS:-} == 1 && -n ${!1:-} ]]; }

# RUN_TEST: the one command that builds the plugin and runs the tests (see run_test_real).
RUN_TEST=run_test_real
if stubbed CUT_STUB_RUN_TEST; then RUN_TEST=$CUT_STUB_RUN_TEST; fi

WORK=           # this run's scratch directory, under $TMPDIR
WORKTREES=()    # git worktrees to remove on exit
SCRATCH_DIRS=() # directories to delete on exit
TOOLCHAIN='cut' # the toolchain run_test_real builds with: cut (the switch at $CUT_ROOT) or path (--source-at)
OPAM_BIN=
FAIL_PREFIX='FAIL: '
FAIL_CODE=1

usage() {
  cat <<'EOF'
Usage:
  ci/build-9.2-cut.sh
      Check the inventory, build Rocq at the cut (once per $CUT_ROOT, again after a build that did not
      finish), build the plugin, run the suite.
  ci/build-9.2-cut.sh --handoff
      The same, and fail while an inventory row is still open.
  ci/build-9.2-cut.sh --revert-fix <test>
      Run <test> in two builds with the head's tests/ and dumps/: it must pass on the head side and fail
      on the parent side at its inventory entry or as its r5 lines say ("R5 negative"). Revert only the
      source or only the stack. A stack stated in the inventory applies to both sides of a source control.
  ci/build-9.2-cut.sh --import <file.v> [-- <rocq compile flags>]
      Compile one file with the cut, in the file's directory; writes <file.v>.stack.
  ci/build-9.2-cut.sh --check <file.vo>... [-- <rocqchk flags>]
      Run the cut's rocqchk -silent -o on the files; writes <first file>.stack.
  ci/build-9.2-cut.sh --source-at <commit> <test>
      Build the plugin from <commit>'s src/ with the head's tests/ and dumps/, with the rocq, make and OCaml
      of PATH (no opam switch; $CUT_ROOT is not used), run <test>, report that toolchain's rocq-commit (or
      unknown) and each planted entry its own case accepted. Exit 3: bad commit or test, no rocq on PATH;
      4: plugin build failed; else the test's.
  ci/build-9.2-cut.sh --self-test
      Check this script's rules (rows S0 to S27, S7l-A2 to S7l-A8e and V1 to V16 of
      ci/build-9.2-cut-selftest.sh) with stubs, and the repository's Redirect logs, build settings and
      workflow (needs git, bash and python3).
Environment: CUT_ROOT (default /scratch/cs/cut) holds the opam root, the sources and the rocq-commit file
(not read by --source-at); CUT_JOBS (default: nproc) is the build parallelism.
EOF
}

# Print one verdict line and exit; main is its only caller and chooses the line.
fail() {
  printf '%s%s\n' "$FAIL_PREFIX" "$*" >&2
  exit "$FAIL_CODE"
}

# <test> <entry> <parent commit>: print the verdict of a --revert-fix control whose parent side failed as its row or
# its r5 lines say, and exit 0; main is its only caller.
negative_met() {
  printf 'R5 NEGATIVE MET: %s at %s (src/ of %s)\n' "$1" "$2" "$3"
  exit 0
}

cleanup() {
  local wt d
  for wt in "${WORKTREES[@]}"; do
    git -C "$ROOT" worktree remove --force --force "$wt" >/dev/null 2>&1
  done
  if ((${#WORKTREES[@]})); then git -C "$ROOT" worktree prune >/dev/null 2>&1; fi
  for d in "${SCRATCH_DIRS[@]}"; do rm -rf -- "$d"; done
}

# ---- Inventory facts ------------------------------------------------------------------------------------------

is_comment_line() { [[ $1 == '#'* || $1 =~ ^[[:space:]]*$ ]]; }

project_tests() { # <root>: the .v files tests/_CoqProject lists, as tests/<name>.v, one per line
  local line tok
  local -a toks
  [[ -f $1/tests/_CoqProject ]] || return 0
  while IFS= read -r line || [[ -n $line ]]; do
    line=${line%%#*}
    read -r -a toks <<<"$line"
    for tok in "${toks[@]}"; do
      if [[ $tok == *.v ]]; then printf 'tests/%s\n' "${tok#./}"; fi
    done
  done <"$1/tests/_CoqProject"
  return 0
}

# <lean.ml>: one fact per member of the three predeclared tables, "member<TAB><Lean name><TAB><function>",
# or "table-error<TAB><function><TAB><why>" when a table cannot be found or an entry cannot be parsed.
# A table is the list that opens on a line holding only "[" after `let <function>` and closes on a line
# starting with "]"; each entry is `(<Kind>, [ "A"; "B" ]...` on one line, and its Lean name is A.B.
predeclared_members() {
  local file=$1 line fn='' state=seek n=0 count=0 name parts p joined bad
  local let_re='^let[[:space:]]+(rec[[:space:]]+)?([A-Za-z_][A-Za-z0-9_]*)'
  local entry_re='^[[:space:]]*\(([A-Za-z_][A-Za-z0-9_]*),[[:space:]]*\[[[:space:]]*("[^"]*"([[:space:]]*;[[:space:]]*"[^"]*")*)[[:space:]]*\][[:space:]]*(,|\))'
  local -a ps
  local -A done_fn=()
  if [[ ! -r $file ]]; then
    for fn in "${PREDECLARED_TABLES[@]}"; do printf 'table-error\t%s\tcannot read %s\n' "$fn" "$file"; done
    return 0
  fi
  while IFS= read -r line || [[ -n $line ]]; do
    n=$((n + 1))
    if [[ $line =~ $let_re ]]; then
      name=${BASH_REMATCH[2]}
      if [[ $state != seek ]]; then
        printf 'table-error\t%s\tno complete list before line %s\n' "$fn" "$n"
        done_fn[$fn]=error
      fi
      state=seek fn=
      for p in "${PREDECLARED_TABLES[@]}"; do
        if [[ $name == "$p" && -z ${done_fn[$p]:-} ]]; then state=open fn=$p count=0; fi
      done
      continue
    fi
    case $state in
      open)
        if [[ $line =~ ^[[:space:]]*\[[[:space:]]*$ ]]; then state=list; fi
        ;;
      list)
        if [[ $line =~ ^[[:space:]]*$ ]]; then continue; fi
        if [[ $line =~ ^[[:space:]]*\] ]]; then
          if ((count == 0)); then
            printf 'table-error\t%s\tits list is empty\n' "$fn"
            done_fn[$fn]=error
          else
            done_fn[$fn]=$count
          fi
          state=seek fn=
        elif [[ $line =~ $entry_re ]]; then
          parts=${BASH_REMATCH[2]} joined='' bad=0
          IFS=';' read -r -a ps <<<"$parts"
          for p in "${ps[@]}"; do
            p=${p//[[:space:]]/}
            p=${p#\"} p=${p%\"}
            if [[ -z $p || $p == *\"* ]]; then bad=1; fi
            joined+=${joined:+.}$p
          done
          if ((bad)); then
            printf 'table-error\t%s\tcannot parse line %s: %s\n' "$fn" "$n" "${line#"${line%%[![:space:]]*}"}"
            done_fn[$fn]=error state=seek fn=
          else
            printf 'member\t%s\t%s\n' "$joined" "$fn"
            count=$((count + 1))
          fi
        else
          printf 'table-error\t%s\tcannot parse line %s: %s\n' "$fn" "$n" "${line#"${line%%[![:space:]]*}"}"
          done_fn[$fn]=error state=seek fn=
        fi
        ;;
    esac
  done <"$file"
  if [[ $state != seek ]]; then
    printf 'table-error\t%s\tno complete list before the end of %s\n' "$fn" "$file"
    done_fn[$fn]=error
  fi
  for fn in "${PREDECLARED_TABLES[@]}"; do
    if [[ -z ${done_fn[$fn]:-} ]]; then printf 'table-error\t%s\tnot found in %s\n' "$fn" "$file"; fi
  done
  return 0
}

# <root>: the inventory facts, one per line, tab-separated:
#   inventory <missing|unreadable|empty|present>    (empty: no row, only comments or blank lines)
#   unreadable <line no> <why> <line text, tabs shown as \t>
#   row <line no> <file> <base_entry> <own_entry> <status> <in tests/_CoqProject: yes|no> <commits> <stack>
#   commit <line no> <file> <commit> <yes|no|malformed>   (yes: an ancestor of HEAD; fixed rows only)
#   lean434 <tests/lean434_*.v file> <has a row: yes|no>
#   predeclared-file <present|missing>
#   member <Lean name> <function> <marked in tests/predeclared.v: yes|no>
#   table-error <function> <why>
check_inventory() {
  local root=$1 inv=$1/$INVENTORY line n=0 f state rest file status c verdict kind a b m
  local -a fld lean434=() cs
  local -A project=() has_row=() marked=()
  local marker_re='^[[:space:]]*\(\*[[:space:]]+predeclared member:[[:space:]]+([^[:space:]]+)[[:space:]]+\*\)[[:space:]]*$'
  while IFS= read -r f; do
    if [[ -n $f ]]; then project["$f"]=1; fi
  done <<<"$(project_tests "$root")"
  for f in "$root"/tests/lean434_*.v; do
    if [[ -e $f ]]; then lean434+=("tests/${f##*/}"); fi
  done
  if [[ ! -e $inv ]]; then
    state=missing
  elif [[ ! -f $inv || ! -r $inv ]]; then
    state=unreadable
  else
    state=empty
    while IFS= read -r line || [[ -n $line ]]; do
      if ! is_comment_line "$line"; then
        state=present
        break
      fi
    done <"$inv"
  fi
  printf 'inventory\t%s\n' "$state"
  if [[ $state == present ]]; then
    while IFS= read -r line || [[ -n $line ]]; do
      n=$((n + 1))
      if is_comment_line "$line"; then continue; fi
      # Split on every tab, keeping empty fields (read with IFS=tab would merge them).
      fld=() rest=$line
      while [[ $rest == *$'\t'* ]]; do
        fld+=("${rest%%$'\t'*}")
        rest=${rest#*$'\t'}
      done
      fld+=("$rest")
      if ((${#fld[@]} != 7)); then
        printf 'unreadable\t%s\t%s fields, not 7\t%s\n' "$n" "${#fld[@]}" "${line//$'\t'/\\t}"
        continue
      fi
      # A field of blanks only is empty too: a commits field of blanks names no commit word at all.
      for f in 0 1 2 3 4 5 6; do
        if [[ -z ${fld[f]//[[:space:]]/} ]]; then break; fi
      done
      if [[ -z ${fld[f]//[[:space:]]/} ]]; then
        local -a names=(file features base_entry own_entry status commits stack)
        printf 'unreadable\t%s\tempty %s field\t%s\n' "$n" "${names[f]}" "${line//$'\t'/\\t}"
        continue
      fi
      file=${fld[0]} status=${fld[4]}
      case $status in
        open | fixed | listed) ;;
        *)
          printf 'unreadable\t%s\tunknown status %s\t%s\n' "$n" "$status" "${line//$'\t'/\\t}"
          continue
          ;;
      esac
      if [[ ${fld[6]} != - ]]; then
        if ! stack_is_positive "${fld[6]}"; then
          printf "unreadable\t%s\tstack '%s' is not a positive whole number of KiB\t%s\n" \
            "$n" "${fld[6]}" "${line//$'\t'/\\t}"
          continue
        fi
        if [[ $status != fixed ]]; then
          printf 'unreadable\t%s\ta stack applies only to a fixed row'\''s control\t%s\n' "$n" "${line//$'\t'/\\t}"
          continue
        fi
      fi
      has_row["$file"]=1
      printf 'row\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$n" "$file" "${fld[2]}" "${fld[3]}" "$status" \
        "$([[ -n ${project[$file]:-} ]] && echo yes || echo no)" "${fld[5]}" "${fld[6]}"
      if [[ $status == fixed && ${fld[5]} != - ]]; then
        read -r -a cs <<<"${fld[5]}"
        for c in "${cs[@]}"; do
          if [[ ! $c =~ ^([0-9a-f]{40}|[0-9a-f]{64})$ ]]; then
            verdict=malformed
          elif git -C "$root" merge-base --is-ancestor "$c" HEAD >/dev/null 2>&1; then
            verdict=yes
          else
            verdict=no
          fi
          printf 'commit\t%s\t%s\t%s\t%s\n' "$n" "$file" "$c" "$verdict"
        done
      fi
    done <"$inv"
  fi
  for f in "${lean434[@]}"; do
    printf 'lean434\t%s\t%s\n' "$f" "$([[ -n ${has_row[$f]:-} ]] && echo yes || echo no)"
  done
  if [[ -f $root/$PREDECLARED_TEST ]]; then
    printf 'predeclared-file\tpresent\n'
    while IFS= read -r line || [[ -n $line ]]; do
      if [[ $line =~ $marker_re ]]; then marked["${BASH_REMATCH[1]}"]=1; fi
    done <"$root/$PREDECLARED_TEST"
  else
    printf 'predeclared-file\tmissing\n'
  fi
  while IFS=$'\t' read -r kind a b; do
    case $kind in
      member)
        m=no
        if [[ -n ${marked[$a]:-} ]]; then m=yes; fi
        printf 'member\t%s\t%s\t%s\n' "$a" "$b" "$m"
        ;;
      table-error) printf 'table-error\t%s\t%s\n' "$a" "$b" ;;
    esac
  done <<<"$(predeclared_members "$root/src/lean.ml")"
  return 0
}

# ---- Stack facts ----------------------------------------------------------------------------------------------

read_stack_assignment() { # <script file>: facts STACK_SET (0|1) and STACK_RAW, from its CUT_STACK_KIB= line
  local line
  STACK_SET=0 STACK_RAW=
  [[ -f $1 ]] || return 0
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ $line == CUT_STACK_KIB=* ]]; then
      STACK_SET=1 STACK_RAW=${line#CUT_STACK_KIB=}
      if [[ $STACK_RAW =~ ^\"(.*)\"$ || $STACK_RAW =~ ^\'(.*)\'$ ]]; then STACK_RAW=${BASH_REMATCH[1]}; fi
      return 0
    fi
  done <"$1"
  return 0
}

stack_is_positive() { [[ $1 =~ ^[1-9][0-9]{0,17}$ ]]; } # decimal KiB, within Bash's arithmetic range

stack_read() { # soft|hard <want>: the current soft or hard stack limit
  if stubbed CUT_STUB_ULIMIT; then
    "$CUT_STUB_ULIMIT" "$1" "$2"
  elif [[ $1 == soft ]]; then
    ulimit -Ss
  else
    ulimit -Hs
  fi
}

# <want>: set the soft stack to <want> KiB in the current (sub)shell: soft first, the hard limit lowered only
# when it reads "unlimited". Skipped under the read-back stub.
stack_apply() {
  local want=$1
  if stubbed CUT_STUB_ULIMIT; then return 0; fi
  ulimit -S -s "$want" 2>/dev/null || { ulimit -H -s "$want" 2>/dev/null || true; ulimit -S -s "$want"; } || return 1
  { [ "$(ulimit -Hs)" = unlimited ] && ulimit -H -s "$want" 2>/dev/null; } || true
}

# <side> <want>: enter a run at <want> KiB, "-" keeping the default, and export the request for the stubs.
stack_enter() {
  export CUT_RUN_SIDE=$1 CUT_RUN_STACK_WANT=$2
  [[ $2 == - ]] && return 0
  stack_apply "$2" || {
    echo "cannot set the soft stack to $2 KiB" >&2
    return 1
  }
}

# <side> <set:0|1> <raw> <setting name>: check any stack source, then set and read it back in a subshell.
# Facts: STACK_WANT (KiB or "-" for the default), STACK_LINE, STACK_ERR (empty on success).
stack_check() {
  local side=$1 set=$2 raw=$3 setting=$4 probe soft hard un_out
  STACK_WANT=- STACK_LINE='' STACK_ERR=''
  if ((set)); then
    if ! stack_is_positive "$raw"; then
      STACK_ERR="$setting='$raw' is not a positive whole number of KiB"
      return 0
    fi
    STACK_WANT=$raw
    hard=$(stack_read hard -)
    if [[ $hard != unlimited ]]; then
      if [[ ! $hard =~ ^[0-9]+$ ]]; then
        STACK_ERR="cannot read the hard stack limit (read '$hard')"
        return 0
      elif ((raw > hard)); then
        STACK_ERR="$setting=$raw is above the hard stack limit of $hard KiB"
        return 0
      fi
    fi
    if ((raw > GVISOR_STACK_CAP_KIB)); then
      if ! un_out=$(uname_r 2>/dev/null) || [[ -z $un_out || ${un_out,,} == *gvisor* ]]; then
        STACK_ERR="$setting=$raw is above $GVISOR_STACK_CAP_KIB KiB, and gVisor caps the stack at 128 MiB (uname -r: ${un_out:-failed or printed nothing})"
        return 0
      fi
    fi
  fi
  if ! probe=$(stack_enter "$side" "$STACK_WANT" &&
    printf '%s %s\n' "$(stack_read soft "$STACK_WANT")" "$(stack_read hard "$STACK_WANT")"); then
    STACK_ERR="cannot set the soft stack to $STACK_WANT KiB"
    return 0
  fi
  read -r soft hard <<<"$probe"
  if ((!set)); then
    if [[ $soft == unlimited ]]; then
      STACK_ERR="the default soft stack is unlimited, which gVisor turns into 8 MiB; a commit must set CUT_STACK_KIB"
    elif [[ ! $soft =~ ^[0-9]+$ ]]; then
      STACK_ERR="cannot read the soft stack limit (read '$soft')"
    fi
  elif [[ $soft != "$STACK_WANT" ]]; then
    STACK_ERR="the soft stack read back is $soft KiB, not $setting=$STACK_WANT"
  fi
  STACK_LINE="STACK soft=$soft hard=${hard:-unknown}"
}

uname_r() { # `uname -r`, or its stub; the status is theirs
  if stubbed CUT_STUB_UNAME_R; then "$CUT_STUB_UNAME_R"; else uname -r; fi
}

# ---- Switch ---------------------------------------------------------------------------------------------------

read_rocq_commit() { # <root>: fact RC_SHA, the commit in <root>/rocq-commit; empty when missing, unreadable or empty
  local f=$1/rocq-commit
  RC_SHA=
  if [[ -f $f && -r $f ]]; then IFS= read -r RC_SHA <"$f"; fi
  RC_SHA=${RC_SHA//[[:space:]]/}
}

# The toolchain of --source-at, the caller's: the rocq on PATH. Facts: TC_ROCQ, the real path of that executable
# (empty when PATH has none), and TC_SHA, the commit of the rocq-commit file of the root that holds it, read only
# when the executable is <root>/opam/<switch>/bin/rocq, the layout build_switch makes under $CUT_ROOT; empty for
# any other layout, or when that root has no readable, non-empty rocq-commit file. $CUT_ROOT is never read.
path_toolchain() {
  local exe bin prefix opam_root
  TC_ROCQ='' TC_SHA=''
  exe=$(command -v rocq) && [[ $exe == /* ]] || return 0
  TC_ROCQ=$(readlink -f -- "$exe") || TC_ROCQ=$exe
  bin=${TC_ROCQ%/*} prefix=${bin%/*}
  opam_root=${prefix%/*}
  [[ ${bin##*/} == bin && ${opam_root##*/} == opam ]] || return 0
  read_rocq_commit "${opam_root%/*}"
  TC_SHA=$RC_SHA
}

# Downloads with python3's standard library. `file <url> <dest> <sha256>` fetches a URL; `lfs <batch url>
# <dest> <oid> <size>` asks the git-LFS batch API for the object and fetches it. Either way the sha256 (and
# the size, when known) is checked before <dest> is replaced; any failure exits non-zero.
py_fetch() {
  python3 - "$@" <<'PY'
import hashlib, json, os, sys, tempfile, urllib.request

def download(url, headers, dest, sha256, size):
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(os.path.abspath(dest)), prefix=".download-")
    try:
        digest, got = hashlib.sha256(), 0
        request = urllib.request.Request(url, headers=headers)
        with os.fdopen(fd, "wb") as out, urllib.request.urlopen(request, timeout=600) as response:
            while True:
                chunk = response.read(1 << 20)
                if not chunk:
                    break
                digest.update(chunk)
                got += len(chunk)
                out.write(chunk)
        if digest.hexdigest() != sha256 or (size is not None and got != size):
            sys.exit(f"{dest}: downloaded {got} bytes with sha256 {digest.hexdigest()}, "
                     f"expected {'any number of' if size is None else size} bytes with sha256 {sha256}")
        os.chmod(tmp, 0o644)
        os.replace(tmp, dest)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise

if sys.argv[1] == "file":
    _, _, url, dest, sha256 = sys.argv
    download(url, {}, dest, sha256, None)
else:
    _, _, batch, dest, oid, size = sys.argv
    body = json.dumps({"operation": "download", "transfers": ["basic"],
                       "objects": [{"oid": oid, "size": int(size)}]}).encode()
    lfs_json = "application/vnd.git-lfs+json"
    request = urllib.request.Request(batch, data=body, method="POST",
                                     headers={"Accept": lfs_json, "Content-Type": lfs_json})
    with urllib.request.urlopen(request, timeout=120) as response:
        obj = json.load(response)["objects"][0]
    action = obj.get("actions", {}).get("download")
    if action is None:
        sys.exit(f"{dest}: the LFS server gives no download for {oid}: {obj.get('error')}")
    download(action["href"], action.get("header", {}), dest, oid, int(size))
PY
}

ensure_opam() { # sets OPAM_BIN: opam on PATH, else the pinned release at $CUT_ROOT/bin/opam (downloaded once)
  local bin=$CUT_ROOT/bin/opam sum
  [[ -z $OPAM_BIN ]] || return 0
  if command -v opam >/dev/null 2>&1; then
    OPAM_BIN=opam
    return 0
  fi
  if [[ -x $bin ]] && sum=$(sha256sum -- "$bin") && [[ ${sum%% *} == "$OPAM_SHA256_X86_64" ]]; then
    OPAM_BIN=$bin
    return 0
  fi
  if [[ $(uname -m) != x86_64 ]]; then
    echo "no opam on PATH, and no pinned opam download for $(uname -m)" >&2
    return 1
  fi
  mkdir -p -- "$CUT_ROOT/bin" || return 1
  py_fetch file "$OPAM_URL_X86_64" "$bin" "$OPAM_SHA256_X86_64" || {
    echo "cannot download $OPAM_URL_X86_64" >&2
    return 1
  }
  chmod +x -- "$bin" || return 1
  OPAM_BIN=$bin
}

shallow_fetch() { # <url> <sha> <dir>: <dir> is a repository with exactly <sha> checked out (detached)
  local url=$1 sha=$2 dir=$3 head
  if head=$(git -C "$dir" rev-parse HEAD 2>/dev/null) && [[ $head == "$sha" ]]; then return 0; fi
  rm -rf -- "$dir"
  if ! { mkdir -p -- "$dir" &&
    git -C "$dir" init -q &&
    git -C "$dir" remote add origin "$url" &&
    git -C "$dir" fetch -q --depth 1 origin "$sha" &&
    git -C "$dir" -c advice.detachedHead=false checkout -q FETCH_HEAD; }; then
    echo "cannot fetch $sha from $url" >&2
    return 1
  fi
  head=$(git -C "$dir" rev-parse HEAD) || return 1
  if [[ $head != "$sha" ]]; then
    echo "$dir: HEAD is $head, not $sha" >&2
    return 1
  fi
}

step() { # <command...>: run one build step, naming it when it fails
  "$@" || {
    echo "build step failed: $*" >&2
    return 1
  }
}

build_switch() { # build the opam root at $OPAMROOT with the switch "cut" holding Rocq at the cut
  local cmd pkg pin version config line want=''
  local -a missing=()
  for cmd in gcc make m4 git rsync pkg-config python3 unzip tar patch; do
    command -v "$cmd" >/dev/null 2>&1 || missing+=("$cmd")
  done
  if command -v gcc >/dev/null 2>&1 && ! printf '#include <gmp.h>\n' | gcc -E -x c - >/dev/null 2>&1; then
    missing+=("libgmp (gmp.h)")
  fi
  if ((${#missing[@]})); then
    echo "missing system prerequisites: ${missing[*]}" >&2
    return 1
  fi
  ensure_opam || return 1
  # The switch is missing or unfinished, so whatever else is under the root is an earlier, unfinished build.
  rm -rf -- "$OPAMROOT" "$CUT_ROOT/rocq-commit"
  step mkdir -p -- "$CUT_ROOT/src" || return 1
  shallow_fetch "$OPAM_REPOSITORY_URL" "$OPAM_REPOSITORY_COMMIT" "$CUT_ROOT/src/opam-repository" || return 1
  shallow_fetch "$ROCQ_OPAM_URL" "$ROCQ_OPAM_COMMIT" "$CUT_ROOT/src/rocq-opam" || return 1
  step env -u OPAMSWITCH "$OPAM_BIN" init --bare --disable-sandboxing --no-setup default \
    "$CUT_ROOT/src/opam-repository" || return 1
  # A local repository carries no archive mirror, and some hosts regenerate their archives.
  step env -u OPAMSWITCH "$OPAM_BIN" option --global 'archive-mirrors=["https://opam.ocaml.org/cache"]' || return 1
  step env -u OPAMSWITCH "$OPAM_BIN" switch create cut --packages="$OCAML_SWITCH_PACKAGES" || return 1
  config=$("$OPAM_BIN" exec -- ocamlopt -config) || return 1
  for line in "${OCAML_SWITCH_CONFIG[@]}"; do want+="${want:+, }${line/: / }"; done
  for line in "${OCAML_SWITCH_CONFIG[@]}"; do
    if ! grep -qxF -e "$line" <<<"$config"; then
      echo "the switch's ocamlopt -config does not report $want" >&2
      return 1
    fi
  done
  step "$OPAM_BIN" repo add --this-switch coq-released "$CUT_ROOT/src/rocq-opam/released" || return 1
  shallow_fetch "$CUT_ROCQ_REPO" "$CUT_ROCQ_COMMIT" "$CUT_ROOT/src/rocq" || return 1
  for pkg in "${ROCQ_SOURCE_PINS[@]}"; do
    step "$OPAM_BIN" pin add -yn --with-version "$ROCQ_VERSION" "$pkg" "$CUT_ROOT/src/rocq" || return 1
  done
  for pin in "${VERSION_PINS[@]}"; do
    read -r pkg version <<<"$pin"
    step "$OPAM_BIN" pin add -yn --kind=version "$pkg" "$version" || return 1
  done
  step "$OPAM_BIN" install "${SWITCH_INSTALL[@]}" || return 1
  # `rocq --version` prints only 9.2+rc2 at this commit and at older ones: this file is the only record.
  git -C "$CUT_ROOT/src/rocq" rev-parse HEAD >"$CUT_ROOT/rocq-commit" || return 1
  step "$OPAM_BIN" clean -a -c -s --logs || return 1
}

# ---- Tree facts -----------------------------------------------------------------------------------------------

# <tree>: replace each git-LFS pointer the suite reads (dumps/*.ndjson.zip, and any other file
# .gitattributes marks filter=lfs that a test of tests/_CoqProject names) by its object. Non-zero on failure.
fetch_lfs() {
  local tree=$1 path attr value t line oid size head
  local -a tests=()
  local -A wanted=()
  git -C "$tree" ls-files -z >"$WORK/lfs-files" || return 1
  git -C "$tree" check-attr -z --stdin filter <"$WORK/lfs-files" >"$WORK/lfs-attrs" || return 1
  while IFS= read -r t; do
    if [[ -n $t && -f $tree/$t ]]; then tests+=("$tree/$t"); fi
  done <<<"$(project_tests "$tree")"
  while IFS= read -r -d '' path && IFS= read -r -d '' attr && IFS= read -r -d '' value; do
    [[ $attr == filter && $value == lfs ]] || continue
    if [[ $path == dumps/*.ndjson.zip ]]; then
      wanted[$path]=1
    elif ((${#tests[@]})) && grep -qF -e "../$path" -- "${tests[@]}"; then
      wanted[$path]=1
    fi
  done <"$WORK/lfs-attrs"
  for path in "${!wanted[@]}"; do
    [[ -f $tree/$path ]] || continue
    head=$(head -c ${#LFS_POINTER_HEAD} -- "$tree/$path" | tr -d '\0')
    [[ $head == "$LFS_POINTER_HEAD" ]] || continue
    oid='' size=''
    while IFS= read -r line || [[ -n $line ]]; do
      case $line in
        'oid sha256:'*) oid=${line#oid sha256:} ;;
        'size '*) size=${line#size } ;;
      esac
    done <"$tree/$path"
    if [[ ! $oid =~ ^[0-9a-f]{64}$ || ! $size =~ ^[0-9]+$ ]]; then
      echo "git-LFS: $path: cannot parse the pointer" >&2
      return 1
    fi
    echo "git-LFS: fetching $path ($size bytes)" >&2
    py_fetch lfs "$LFS_BATCH_URL" "$tree/$path" "$oid" "$size" || {
      echo "git-LFS: $path: the download failed" >&2
      return 1
    }
  done
  return 0
}

# RUN_TEST, real: `suite <tree>` or `one <tree> <name>`. Builds the plugin (status 125 when that fails),
# then runs `make -k test`, so that every test runs and the log names each one that fails, or
# `make tests/<name>.vo` (the root Makefile forwards tests/% goals). With TOOLCHAIN=cut, under `opam exec` on the
# cut's switch ($OPAMROOT, $OPAMSWITCH); with TOOLCHAIN=path (--source-at), the plain make, rocq and OCaml tools of
# the caller's PATH, main having unset OPAMROOT and OPAMSWITCH.
run_test_real() {
  local kind=$1 tree=$2 name=${3:-}
  local -a run=()
  if [[ $TOOLCHAIN == cut ]]; then
    ensure_opam || return "$RT_BUILD_FAILED"
    run=("$OPAM_BIN" exec --)
  fi
  cd -- "$tree" || return "$RT_BUILD_FAILED"
  "${run[@]}" make || return "$RT_BUILD_FAILED"
  if [[ $kind == suite ]]; then
    "${run[@]}" make -k test
  else
    "${run[@]}" make "tests/$name.vo"
  fi
}

# <log> <side> <want> <RUN_TEST args...>: run RUN_TEST in a subshell, output copied to <log> and stderr.
# Fact RUN_RC: RUN_TEST's status.
run_logged() {
  local log=$1 side=$2 want=$3
  shift 3
  (
    stack_enter "$side" "$want" || exit 1
    "$RUN_TEST" "$@"
  ) 2>&1 </dev/null | tee "$log" >&2
  RUN_RC=${PIPESTATUS[0]}
}

# <errlog> <want> <dir or -> <command...>: run the command at the soft stack <want> in <dir>, in a subshell.
# Its stdout passes straight through; its stderr passes through too, a copy kept in <errlog>. Fact RUN_RC.
run_passthrough() {
  local errlog=$1 want=$2 dir=$3
  shift 3
  {
    (
      if [[ $dir != - ]]; then cd -- "$dir" || exit 1; fi
      stack_enter suite "$want" || exit 1
      exec "$@"
    ) 2>&1 1>&3 3>&- | tee "$errlog" >&2 3>&-
    RUN_RC=${PIPESTATUS[0]}
  } 3>&1
}

# <root> <work> <test> <row stack> <fix commits...>: RV_STATUS ok|error, RV_MSG, RV_FIRST, RV_PARENT,
# RV_SRC head|parent, RV_STACK head|parent|row, RV_PARENT_SET and RV_PARENT_RAW (the first fix's parent's setting).
revert_fix_prepare() {
  local root=$1 work=$2 test=$3 stack=$4 c history parent paths before after parent_set parent_raw src=0 changed=0
  shift 4
  local -A want=() seen=()
  local -a missing=() ids
  RV_STATUS=error RV_FIRST='' RV_PARENT='' RV_MSG=''
  RV_SRC=head RV_STACK=head RV_PARENT_SET=0 RV_PARENT_RAW=
  for c in "$@"; do want[$c]=1; done
  history=$(git -C "$root" rev-list --topo-order HEAD) || {
    RV_MSG="git rev-list HEAD failed"
    return 0
  }
  # rev-list lists a commit before its parents: the last commit of the row it lists is the earliest.
  while IFS= read -r c; do
    if [[ -n $c && -n ${want[$c]:-} ]]; then RV_FIRST=$c seen[$c]=1; fi
  done <<<"$history"
  for c in "$@"; do
    if [[ -z ${seen[$c]:-} ]]; then missing+=("$c"); fi
  done
  if ((${#missing[@]})); then
    RV_MSG="a fix commit of its row is not an ancestor of HEAD: ${missing[*]}"
    return 0
  fi
  for c in "$@"; do
    read -r -a ids <<<"$(git -C "$root" rev-list --parents -n 1 "$c")"
    if ((${#ids[@]} != 2)); then
      RV_MSG="fix commit $c is a merge or has no parent; a control needs one parent"
      return 0
    fi
    parent=${ids[1]}
    paths=$(git -C "$root" diff --no-renames --name-only "$c^1" "$c" -- src/) || {
      RV_MSG="cannot inspect src/ changes at $c"
      return 0
    }
    if [[ -n $paths ]]; then src=1; fi
    before=$work/stack-before after=$work/stack-after
    if ! stack_script_at "$root" "$parent" "$before" || ! stack_script_at "$root" "$c" "$after"; then
      return 0
    fi
    read_stack_assignment "$before"
    parent_set=$STACK_SET parent_raw=$STACK_RAW
    read_stack_assignment "$after"
    if [[ $parent_set != "$STACK_SET" || $parent_raw != "$STACK_RAW" ]]; then changed=1; fi
    if [[ $c == "$RV_FIRST" ]]; then
      RV_PARENT=$parent RV_PARENT_SET=$parent_set RV_PARENT_RAW=$parent_raw
    fi
  done
  if ((src)); then RV_SRC=parent; fi
  if ((changed)); then RV_STACK=parent; elif [[ $stack != - ]]; then RV_STACK=row; fi
  if [[ $RV_SRC == parent && $RV_STACK == parent ]]; then
    RV_MSG="the fix commits of $test change src/ and CUT_STACK_KIB; a control reverts one of them; split the fix"
  elif ((!src && !changed)); then
    RV_MSG="the fix commits of $test change neither src/ nor CUT_STACK_KIB; there is nothing to revert"
  elif ((changed)) && [[ $stack != - ]]; then
    RV_MSG="a row that states a stack cannot revert a stack fix"
  else
    RV_STATUS=ok
  fi
}

# An absent script has no stack line. Truncate the scratch file for each commit, even when absent.
stack_script_at() {
  local root=$1 commit=$2 file=$3 path
  if path=$(git -C "$root" ls-tree "$commit" -- "$SCRIPT_REL"); then
    if [[ -n $path ]]; then
      if git -C "$root" show "$commit:$SCRIPT_REL" >"$file"; then return 0; fi
    elif : >"$file"; then
      return 0
    fi
  fi
  RV_MSG="cannot read $SCRIPT_REL at $commit"
  return 1
}

# <root> <tree> <commit> <name>: a detached worktree of HEAD at <tree> (the head's tests/ and dumps/) whose
# src/, Makefile and _CoqProject come from <commit>. Facts: SA_STATUS ok|error, SA_CAUSE.
source_at_prepare() {
  local root=$1 tree=$2 commit=$3 name=$4 sha out
  SA_STATUS=error SA_CAUSE=
  sha=$(git -C "$root" rev-parse --verify --quiet "$commit^{commit}") || {
    SA_CAUSE="commit $commit not found"
    return 0
  }
  git -C "$root" cat-file -e "HEAD:tests/$name.v" 2>/dev/null || {
    SA_CAUSE="test tests/$name.v is not in the head's tests/"
    return 0
  }
  out=$(git -C "$root" worktree add --detach "$tree" HEAD 2>&1) || {
    SA_CAUSE="git worktree add failed: ${out//$'\n'/ }"
    return 0
  }
  WORKTREES+=("$tree")
  rm -rf -- "$tree/src" "$tree/Makefile" "$tree/_CoqProject"
  out=$(git -C "$tree" checkout "$sha" -- src Makefile _CoqProject 2>&1) || {
    SA_CAUSE="cannot take src/, Makefile and _CoqProject from $sha: ${out//$'\n'/ }"
    return 0
  }
  SA_STATUS=ok
}

# ---- Log facts ------------------------------------------------------------------------------------------------

entry_error_name() { # <line>: sets ENTRY_NAME to X when the line holds "Error at line N (for X)"; else status 1
  local re='Error at line [0-9]+ \(for (.*)$' rest
  [[ $1 =~ $re ]] || return 1
  rest=${BASH_REMATCH[1]}
  ENTRY_NAME=${rest%%'): '*}
  if [[ $ENTRY_NAME == "$rest" ]]; then
    ENTRY_NAME=${rest%"${rest##*[![:space:]]}"}
    ENTRY_NAME=${ENTRY_NAME%')'}
  fi
}

first_entry_error() { # <files...>: the X of the first "Error at line N (for X)" of the files, in order; or nothing
  local f line
  for f in "$@"; do
    [[ -f $f ]] || continue
    while IFS= read -r line || [[ -n $line ]]; do
      if entry_error_name "$line"; then
        printf '%s' "$ENTRY_NAME"
        return 0
      fi
    done <"$f"
  done
  return 0
}

# <log> <entry>: fact CASE_OUTCOME, how the Redirect log of one planted case ended for <entry>:
#   unreached   no log: Rocq stopped before the case's Redirect, or never ran it
#   refused     a line "Error at line N (for <entry>)"
#   unseen      no line "line N: <entry>" (exactly that name: a longer name is another entry)
#   unfinished  "line N: <entry>", but no line "Done!" after it: the import did not complete
#   accepted    "line N: <entry>", no refusal of it, and a line "Done!" after it
case_outcome() {
  local log=$1 want=$2 line t seen=0 done_after=0 refused=0 re='^[[:space:]]*line [0-9]+: (.*[^[:space:]])[[:space:]]*$'
  CASE_OUTCOME=unreached
  [[ -f $log ]] || return 0
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ $line =~ $re ]]; then
      if [[ ${BASH_REMATCH[1]} == "$want" ]]; then seen=1 done_after=0; fi
    elif entry_error_name "$line"; then
      if [[ $ENTRY_NAME == "$want" ]]; then refused=1; fi
    elif ((seen)); then
      t=${line#"${line%%[![:space:]]*}"}
      if [[ ${t%"${t##*[![:space:]]}"} == 'Done!' ]]; then done_after=1; fi
    fi
  done <"$log"
  if ((refused)); then
    CASE_OUTCOME=refused
  elif ((!seen)); then
    CASE_OUTCOME=unseen
  elif ((!done_after)); then
    CASE_OUTCOME=unfinished
  else
    CASE_OUTCOME=accepted
  fi
}

first_error_line() { # <log>: its first line starting "Error", else the first naming an error, else its last line
  local line last=
  if line=$(grep -m1 -E '^Error' -- "$1" 2>/dev/null) || line=$(grep -m1 -E 'Error|error:' -- "$1" 2>/dev/null); then
    printf '%s' "$line"
    return 0
  fi
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ -n ${line//[[:space:]]/} ]]; then last=$line; fi
  done <"$1"
  printf '%s' "${last:-no output}"
}

# <log> <option name>: status 0 when the log holds Rocq's unknown-option message followed by the quoted
# option name (line breaks inside the message do not matter).
option_failure_seen() {
  local text rest window
  text=$(tr -s '[:space:]' ' ' <"$1") || return 1
  rest=$text window=$((${#2} + 16))
  while [[ $rest == *"$UNKNOWN_OPTION_MSG"* ]]; do
    rest=${rest#*"$UNKNOWN_OPTION_MSG"}
    if [[ ${rest:0:window} == *"\"$2\""* ]]; then return 0; fi
  done
  return 1
}

# <test file>: the planted cases of the test, one fact per "(* planted: <name> *)" line, whose case is the first
# Redirect command after it (REDIRECT_RE):
#   case<TAB><name><TAB><redirect>
#   orphan<TAB><line no><TAB><name>    no Redirect follows the planted line
planted_cases() {
  local line n=0 i planted_re='^[[:space:]]*\(\*[[:space:]]+planted:[[:space:]]+([^[:space:]]+)[[:space:]]+\*\)[[:space:]]*$'
  local -a pending=() marker_lines=()
  while IFS= read -r line || [[ -n $line ]]; do
    n=$((n + 1))
    if [[ $line =~ $planted_re ]]; then
      pending+=("${BASH_REMATCH[1]}") marker_lines+=("$n")
    elif [[ $line =~ $REDIRECT_RE ]]; then
      for i in "${!pending[@]}"; do printf 'case\t%s\t%s\n' "${pending[i]}" "${BASH_REMATCH[1]}"; done
      pending=() marker_lines=()
    fi
  done <"$1"
  for i in "${!pending[@]}"; do printf 'orphan\t%s\t%s\n' "${marker_lines[i]}" "${pending[i]}"; done
  return 0
}

# <test file> <dir>: <dir>/<name>.out for each Redirect "<name>" of the test (REDIRECT_RE; Rocq adds .out)
redirect_logs() {
  local line
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ $line =~ $REDIRECT_RE ]]; then printf '%s/%s.out\n' "$2" "${BASH_REMATCH[1]}"; fi
  done <"$1"
  return 0
}

squeeze() { # <text>: its words, joined by single spaces
  local IFS=$' \t\n\v\f\r'
  local -a w=()
  read -r -d '' -a w <<<"$1"
  printf '%s' "${w[*]}"
}

names_token() { # <text> <name>: status 0 when <name> occurs in <text> with no name character right before or after
  local rest=$1 before after namech="[[:alnum:]_.']"
  while [[ $rest == *"$2"* ]]; do
    before=${rest%%"$2"*} after=${rest#*"$2"}
    if [[ ! ${before: -1} =~ $namech && ! ${after:0:1} =~ $namech ]]; then return 0; fi
    rest=$after
  done
  return 1
}

# <file> <text> [prefix]: status 0 when a line of the file, its trailing blanks removed, is <text> (with "prefix":
# starts with <text>, its leading blanks removed too)
log_has_line() {
  local line t
  while IFS= read -r line || [[ -n $line ]]; do
    t=${line%"${line##*[![:space:]]}"}
    if [[ ${3:-} == prefix ]]; then
      t=${t#"${t%%[![:space:]]*}"}
      if [[ $t == "$2"* ]]; then return 0; fi
    elif [[ $t == "$2" ]]; then
      return 0
    fi
  done <"$1"
  return 1
}

# <line>: sets ENTRY_NAME (entry_error_name) when the line is a refusal header as src/lean.ml's refusal prints it:
# it starts "Skipping: Error at line " (Skip mode) or "Error at line " (Stop mode, and Fail mode under Rocq's
# "The command has indeed failed with message:"); else status 1
refusal_header_name() {
  [[ $1 == 'Skipping: Error at line '* || $1 == 'Error at line '* ]] && entry_error_name "$1"
}

# <file> <text> <entry>: status 0 when some line of the file that starts with <text>, its leading and trailing blanks
# removed (as log_has_line ... prefix reads it), has right before it (one line above, in the same file) a refusal
# header (refusal_header_name) of exactly <entry>
after_refusal_header() {
  local line t prev=''
  while IFS= read -r line || [[ -n $line ]]; do
    t=${line%"${line##*[![:space:]]}"} t=${t#"${t%%[![:space:]]*}"}
    if [[ $t == "$2"* ]] && refusal_header_name "$prev" && [[ $ENTRY_NAME == "$3" ]]; then return 0; fi
    prev=$line
  done <"$1"
  return 1
}

# <log> <test name> <line>: fact RE_MSG, the message of the Rocq error the log reports at that line of tests/<name>.v
# (the line 'File "./<name>.v", line <line>, characters A-B:' right before a line starting "Error:"), its lines up
# to the next blank line squeezed into one; empty when the log reports no error there.
rocq_error_at() {
  local log=$1 name=$2 at=$3 line state=seek msg=''
  RE_MSG=''
  [[ -f $log ]] || return 0
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ $state == msg ]]; then
      if [[ -z ${line//[[:space:]]/} || $line == make:* || $line == 'make['* || $line == 'File "'* ]]; then break; fi
      msg+=" $line"
    elif [[ $state == loc && $line == Error:* ]]; then
      state=msg msg=${line#Error:}
    elif [[ $line == "File \"./$name.v\", line $at, characters "* || $line == "File \"$name.v\", line $at, characters "* ]]; then
      state=loc
    else
      state=seek
    fi
  done <"$log"
  if [[ $state == msg ]]; then RE_MSG=$(squeeze "$msg"); fi
}

# <log> <test name> <redirect> <text>: status 0 when the log has the line
# "EXPECT FAIL: tests/<name>.expect:<n>: <redirect>.out: unexpected '<text>'" that tests/check_expect.py prints
expect_failure_seen() {
  local line mid pre="EXPECT FAIL: tests/$2.expect:" post=": $3.out: unexpected '$4'"
  while IFS= read -r line || [[ -n $line ]]; do
    [[ $line == "$pre"*"$post" ]] || continue
    mid=${line#"$pre"} mid=${mid%"$post"}
    if [[ $mid =~ ^[0-9]+$ ]]; then return 0; fi
  done <"$1"
  return 1
}

# <test file>: the r5 lines of the test. A test whose failure before its fix the first entry error of its logs does
# not name ("R5 negative", --revert-fix) says what that failure is in comment lines of these kinds:
#   (* r5 error: <text> *)                   the run's Rocq error at the command right after it (only blank lines
#                                            and other r5 lines between) holds <text> and the row's entry
#   (* r5 log: "<redirect>" <text> *)        the .out log of that Redirect of the test has the line <text>
#   (* r5 log lacks: "<redirect>" <text> *)  that log exists and has no line <text>
#   (* r5 assertion: "<redirect>" <text> *)  the run's log has the failure "unexpected '<text>'" of the test's .expect
#                                            on that Redirect's log, that log has a line starting with <text>, and
#                                            <text> names the row's entry, or some line of that log starting with
#                                            <text> comes right after a refusal header of the entry
#                                            (after_refusal_header): src/lean.ml's refusal prints the header, a
#                                            line break, then the message, whose first line can name no entry
# One fact per r5 line: "error<TAB><line no of the command><TAB><text>", "log|lacks|assertion<TAB><redirect><TAB>
# <text>", or "bad<TAB><line no><TAB><why>" for a line starting "(* r5 " that is none of these, or that names a
# Redirect the test does not have.
r5_lines() {
  local line kind rest i j n
  local marker_re='^[[:space:]]*\(\*[[:space:]]+r5[[:space:]]' comment_re='^[[:space:]]*\(\*'
  local line_re='^[[:space:]]*\(\*[[:space:]]+r5 (error|log|log lacks|assertion):[[:space:]]+(.*[^[:space:]])[[:space:]]+\*\)[[:space:]]*$'
  local named_re='^"([^"]+)"[[:space:]]+(.+)$'
  local -a lines=()
  local -A redirects=()
  mapfile -t lines <"$1"
  for line in "${lines[@]}"; do
    if [[ $line =~ $REDIRECT_RE ]]; then redirects[${BASH_REMATCH[1]}]=1; fi
  done
  n=${#lines[@]}
  for ((i = 0; i < n; i++)); do
    line=${lines[i]}
    [[ $line =~ $marker_re ]] || continue
    if [[ ! $line =~ $line_re ]]; then
      printf 'bad\t%s\tan r5 line of no known kind: %s\n' "$((i + 1))" "${line#"${line%%[![:space:]]*}"}"
      continue
    fi
    kind=${BASH_REMATCH[1]} rest=${BASH_REMATCH[2]}
    if [[ $kind == error ]]; then
      for ((j = i + 1; j < n; j++)); do
        [[ -z ${lines[j]//[[:space:]]/} || ${lines[j]} =~ $marker_re ]] || break
      done
      if ((j >= n)) || [[ ${lines[j]} =~ $comment_re ]]; then
        printf 'bad\t%s\tno command right after this r5 error line\n' "$((i + 1))"
      else
        printf 'error\t%s\t%s\n' "$((j + 1))" "$rest"
      fi
    elif [[ ! $rest =~ $named_re ]]; then
      printf 'bad\t%s\tno "<redirect>" and text after "r5 %s:"\n' "$((i + 1))" "$kind"
    elif [[ -z ${redirects[${BASH_REMATCH[1]}]:-} ]]; then
      printf 'bad\t%s\tno Redirect "%s" in the test\n' "$((i + 1))" "${BASH_REMATCH[1]}"
    else
      if [[ $kind == 'log lacks' ]]; then kind=lacks; fi
      printf '%s\t%s\t%s\n' "$kind" "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}"
    fi
  done
  return 0
}

# <test file> <entry> <run log> <dir of its Redirect logs>: one line per r5 line of the test (r5_lines; a bad one is
# skipped) that the logs of a failed run do not meet; nothing when each one is met.
r5_unmet() {
  local file=$1 entry=$2 log=$3 dir=$4 name kind a text out
  name=${file##*/} name=${name%.v}
  while IFS=$'\t' read -r kind a text; do
    out=$dir/$a.out
    case $kind in
      error)
        rocq_error_at "$log" "$name" "$a"
        if [[ -z $RE_MSG ]]; then
          printf 'no Rocq error at tests/%s.v line %s\n' "$name" "$a"
        elif [[ $RE_MSG != *"$(squeeze "$text")"* ]]; then
          printf "the Rocq error at tests/%s.v line %s does not hold '%s': %s\n" "$name" "$a" "$text" "${RE_MSG:0:240}"
        elif ! names_token "$RE_MSG" "$entry"; then
          printf 'the Rocq error at tests/%s.v line %s does not name %s: %s\n' "$name" "$a" "$entry" "${RE_MSG:0:240}"
        fi
        ;;
      log | lacks)
        if [[ ! -f $out ]]; then
          printf '%s.out does not exist\n' "$a"
        elif [[ $kind == log ]] && ! log_has_line "$out" "$text"; then
          printf "%s.out has no line '%s'\n" "$a" "$text"
        elif [[ $kind == lacks ]] && log_has_line "$out" "$text"; then
          printf "%s.out has the line '%s'\n" "$a" "$text"
        fi
        ;;
      assertion)
        if ! expect_failure_seen "$log" "$name" "$a" "$text"; then
          printf "the run's log has no line \"EXPECT FAIL: tests/%s.expect:<n>: %s.out: unexpected '%s'\"\n" "$name" "$a" "$text"
        fi
        # The text names the entry, or follows its refusal header; a missing or unreadable log is reported alone.
        if [[ ! -f $out ]]; then
          printf '%s.out does not exist\n' "$a"
        elif [[ ! -r $out ]]; then
          printf '%s.out cannot be read\n' "$a"
        else
          if ! log_has_line "$out" "$text" prefix; then
            printf "%s.out has no line starting '%s'\n" "$a" "$text"
          fi
          if ! names_token "$text" "$entry" && ! after_refusal_header "$out" "$text" "$entry"; then
            printf "'%s' does not name %s, and no line right before it in %s.out is a refusal header of %s\n" \
              "$text" "$entry" "$a" "$entry"
          fi
        fi
        ;;
    esac
  done <<<"$(r5_lines "$file")"
  return 0
}

# ---- main: every decision ---------------------------------------------------------------------------------------

main() {
  local mode=suite handoff=0 test_arg='' commit_arg='' name='' f i
  local -a files=() flags=()
  trap cleanup EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM

  # Arguments: a mode with a missing or extra argument prints the usage and exits 2 (S8).
  case ${1-} in
    '')
      if (($# > 1)); then usage >&2; exit 2; fi
      ;;
    --handoff)
      if (($# != 1)); then usage >&2; exit 2; fi
      handoff=1
      ;;
    --revert-fix)
      if (($# != 2)) || [[ -z $2 ]]; then usage >&2; exit 2; fi
      mode=revert test_arg=$2
      ;;
    --source-at)
      if (($# != 3)) || [[ -z $2 || -z $3 ]]; then usage >&2; exit 2; fi
      mode=source commit_arg=$2 test_arg=$3
      ;;
    --import | --check)
      mode=${1#--}
      shift
      while (($#)) && [[ $1 != -- ]]; do
        files+=("$1")
        shift
      done
      if (($#)); then
        shift
        flags=("$@")
      fi
      if [[ $mode == import ]] && ((${#files[@]} != 1)); then usage >&2; exit 2; fi
      if [[ $mode == check ]] && ((${#files[@]} == 0)); then usage >&2; exit 2; fi
      ;;
    --self-test)
      if (($# != 1)); then usage >&2; exit 2; fi
      # shellcheck source=ci/build-9.2-cut-selftest.sh
      source "${SELF%/*}/build-9.2-cut-selftest.sh" || fail "cannot read ${SELF%/*}/build-9.2-cut-selftest.sh"
      self_test
      exit $?
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      usage >&2
      exit 2
      ;;
  esac
  # --source-at keeps its own exit codes: every failure before the test is a SOURCE-AT ERROR, status 3. It builds
  # with the caller's toolchain, the one its PATH gives (S24): no opam root or switch of this script is selected,
  # and nothing under $CUT_ROOT is read, built or used.
  if [[ $mode == source ]]; then
    FAIL_PREFIX='SOURCE-AT ERROR: ' FAIL_CODE=3 TOOLCHAIN=path
    unset OPAMROOT OPAMSWITCH
  else
    [[ $CUT_ROOT == /* ]] || fail "CUT_ROOT must be an absolute path (an opam root is not relocatable): $CUT_ROOT"
  fi
  WORK=$(mktemp -d "${TMPDIR:-/tmp}/build-9.2-cut.XXXXXX") || fail "cannot create a scratch directory under ${TMPDIR:-/tmp}"
  SCRATCH_DIRS+=("$WORK")

  # Inventory checks, in the default mode, --handoff and --revert-fix (S1-S4, S3b, S10-S13): every row of the
  # inventory is readable and agrees with tests/_CoqProject (every row's test is listed there: a listed row's
  # test checks that its feature's entry is refused, so the suite passes), a fixed row names commits that are ancestors of HEAD, every tests/lean434_*.v has a
  # row, and every member of the predeclared tables of src/lean.ml has its marker in tests/predeclared.v;
  # --handoff also fails on an open row. A missing or empty inventory skips the checks while the head has no
  # tests/lean434_*.v. --import and --check run on trees without history (S23), and --source-at measures an
  # old src/ with only its own exit codes (S24): neither checks the inventory.
  local -a row_line=() row_file=() row_base=() row_own=() row_status=() row_inproj=() row_commits=() row_stack=()
  if [[ $mode == suite || $mode == revert ]]; then
    local facts kind a b c d e g h inv_state=missing pred_state=missing where st
    local -a fails=() lean434=() lean434_norow=() commit_fails=() table_errors=() unmarked=() unreadable=()
    local -A first_line=()
    facts=$(check_inventory "$ROOT") || fail "the inventory checks could not run"
    while IFS=$'\t' read -r kind a b c d e f g h; do
      case $kind in
        inventory) inv_state=$a ;;
        unreadable) unreadable+=("$INVENTORY line $a cannot be read ($b): $c") ;;
        row)
          row_line+=("$a") row_file+=("$b") row_base+=("$c") row_own+=("$d") row_status+=("$e")
          row_inproj+=("$f") row_commits+=("$g") row_stack+=("$h")
          ;;
        commit)
          if [[ $d == malformed ]]; then
            commit_fails+=("$INVENTORY line $a ($b): '$c' is not a full commit hash")
          elif [[ $d != yes ]]; then
            commit_fails+=("$INVENTORY line $a ($b): commit $c is not an ancestor of HEAD (or not in this clone)")
          fi
          ;;
        lean434)
          lean434+=("$a")
          if [[ $b != yes ]]; then lean434_norow+=("$a"); fi
          ;;
        predeclared-file) pred_state=$a ;;
        table-error) table_errors+=("src/lean.ml, $a: $b") ;;
        member)
          if [[ $c != yes ]]; then unmarked+=("$a"$'\t'"$b"); fi
          ;;
      esac
    done <<<"$facts"
    case $inv_state in
      missing | empty)
        if ((${#lean434[@]})); then
          fails+=("$INVENTORY is $inv_state, but the head has tests/lean434_*.v files: ${lean434[*]}")
        fi
        ;;
      unreadable) fails+=("cannot read $INVENTORY") ;;
      present)
        fails+=("${unreadable[@]}")
        for i in "${!row_file[@]}"; do
          where="$INVENTORY line ${row_line[i]} (${row_file[i]})"
          st=${row_status[i]}
          if [[ -n ${first_line[${row_file[i]}]:-} ]]; then
            fails+=("$where: a second row for ${row_file[i]}; the first is line ${first_line[${row_file[i]}]}")
          else
            first_line[${row_file[i]}]=${row_line[i]}
          fi
          if [[ ${row_inproj[i]} != yes ]]; then
            fails+=("${row_file[i]}: status $st, but tests/_CoqProject does not list it ($where)")
          fi
          if [[ $st == fixed && ${row_commits[i]} == - ]]; then
            fails+=("$where: status fixed, but the row names no commit")
          fi
          if [[ $st != fixed && ${row_commits[i]} != - ]]; then
            fails+=("$where: status $st, but the row names commits (only a fixed row does)")
          fi
          if ((handoff)) && [[ $st == open ]]; then
            fails+=("--handoff: $where is still open")
          fi
        done
        fails+=("${commit_fails[@]}")
        for f in "${lean434_norow[@]}"; do fails+=("$f has no row in $INVENTORY"); done
        if [[ $pred_state == missing ]]; then
          fails+=("$PREDECLARED_TEST is missing; it is required once $INVENTORY exists")
        else
          fails+=("${table_errors[@]}")
          for f in "${unmarked[@]}"; do
            fails+=("predeclared member ${f%%$'\t'*} (src/lean.ml, ${f#*$'\t'}) has no line '(* predeclared member: ${f%%$'\t'*} *)' in $PREDECLARED_TEST")
          done
        fi
        ;;
    esac
    if ((${#fails[@]})); then
      for f in "${fails[@]}"; do printf '%s%s\n' "$FAIL_PREFIX" "$f" >&2; done
      exit "$FAIL_CODE"
    fi
    if [[ $inv_state != present ]]; then
      printf 'INVENTORY CHECKS SKIPPED: %s is missing or empty and the head has no tests/lean434_*.v file\n' \
        "$INVENTORY" >&2
    fi
  fi

  # The scratch tree and the inputs of each mode.
  local expected='' run_tree=$ROOT stack_out='' idx=-1 r5_facts='' cases='' head_src parent_src
  local -a commits=()
  if [[ $mode == revert ]]; then
    name=${test_arg#tests/} name=${name%.v}
    for i in "${!row_file[@]}"; do
      if [[ ${row_file[i]} == "tests/$name.v" ]]; then
        idx=$i
        break
      fi
    done
    ((idx >= 0)) || fail "--revert-fix: $INVENTORY has no row for $test_arg (looked for tests/$name.v)"
    case ${row_status[idx]} in
      open) fail "--revert-fix $test_arg: $INVENTORY line ${row_line[idx]} (${row_file[idx]}) is open; it names no fix to revert" ;;
      listed)
        printf 'SKIPPED, LISTED: %s\n' "$test_arg"
        exit 0
        ;;
    esac
    expected=${row_own[idx]}
    if [[ $expected == - ]]; then expected=${row_base[idx]}; fi
    # An inventory name may quote a component as Lean does (Nat.«Internal».Linear…), since a push check of
    # our tooling reads some dotted names as host names; the log prints the name unquoted.
    expected=${expected//«/} expected=${expected//»/}
    read -r -a commits <<<"${row_commits[idx]}"
    revert_fix_prepare "$ROOT" "$WORK" "tests/$name.v" "${row_stack[idx]}" "${commits[@]}"
    [[ $RV_STATUS == ok ]] || fail "--revert-fix $test_arg: $RV_MSG"
    head_src=$(git -C "$ROOT" rev-parse HEAD) || fail "--revert-fix $test_arg: cannot resolve HEAD"
    parent_src=$head_src
    if [[ $RV_SRC == parent ]]; then parent_src=$RV_PARENT; fi
    source_at_prepare "$ROOT" "$WORK/head" "$head_src" "$name"
    [[ $SA_STATUS == ok ]] || fail "--revert-fix $test_arg: head side: $SA_CAUSE"
    # The r5 lines of the head's test (r5_lines), checked before it runs (S7k): a test that has them is decided by
    # them, with exactly one error or assertion line, and never on an option row.
    r5_facts=$(r5_lines "$WORK/head/tests/$name.v")
    if [[ -n $r5_facts ]]; then
      local verdicts=0
      local -a r5_bad=()
      while IFS=$'\t' read -r kind a b; do
        case $kind in
          bad) r5_bad+=("tests/$name.v line $a: $b") ;;
          error | assertion) verdicts=$((verdicts + 1)) ;;
        esac
      done <<<"$r5_facts"
      if ((${#r5_bad[@]})); then
        for f in "${r5_bad[@]}"; do printf '%s--revert-fix %s: %s\n' "$FAIL_PREFIX" "$test_arg" "$f" >&2; done
        exit "$FAIL_CODE"
      fi
      [[ $expected != option:* ]] || fail "--revert-fix $test_arg: an option row is decided at its Set line, but tests/$name.v has r5 lines"
      ((verdicts == 1)) || fail "--revert-fix $test_arg: tests/$name.v has $verdicts r5 error or assertion lines; it needs exactly one"
    fi
  fi
  if [[ $mode == source ]]; then
    local kind a b
    name=${test_arg#tests/} name=${name%.v}
    source_at_prepare "$ROOT" "$WORK/tree" "$commit_arg" "$name"
    [[ $SA_STATUS == ok ]] || fail "$SA_CAUSE"
    run_tree=$WORK/tree
    # Each planted line's case is the first Redirect after it (planted_cases); a planted line with none is no case.
    cases=$(planted_cases "$run_tree/tests/$name.v")
    while IFS=$'\t' read -r kind a b; do
      if [[ $kind == orphan ]]; then fail "tests/$name.v line $a: no Redirect after the planted line of $b"; fi
    done <<<"$cases"
  fi
  if [[ $mode == import || $mode == check ]]; then
    for f in "${files[@]}"; do
      [[ -f $f ]] || fail "--$mode: no such file: $f"
    done
    stack_out=${files[0]}.stack
  fi

  # Check and read back each side's stack before any test runs.
  local want stack_line parent_want parent_stack_line stack_side=suite setting=CUT_STACK_KIB
  read_stack_assignment "$SELF"
  if [[ $mode == revert ]]; then
    stack_side=head
    if [[ $RV_STACK == row ]]; then
      STACK_SET=1 STACK_RAW=${row_stack[idx]} setting="$INVENTORY line ${row_line[idx]} stack"
    fi
  fi
  local head_set=$STACK_SET head_raw=$STACK_RAW
  stack_check "$stack_side" "$head_set" "$head_raw" "$setting"
  if [[ $mode == revert ]]; then
    [[ -z $STACK_ERR ]] || fail "--revert-fix $test_arg: head side: $STACK_ERR"
  else
    [[ -z $STACK_ERR ]] || fail "$STACK_ERR"
  fi
  want=$STACK_WANT stack_line=$STACK_LINE
  if [[ $mode == revert ]]; then
    if [[ $RV_STACK == parent ]]; then
      stack_check parent "$RV_PARENT_SET" "$RV_PARENT_RAW" CUT_STACK_KIB
    else
      stack_check parent "$head_set" "$head_raw" "$setting"
    fi
    [[ -z $STACK_ERR ]] || fail "--revert-fix $test_arg: parent side (fix parent $RV_PARENT): $STACK_ERR"
    parent_want=$STACK_WANT parent_stack_line=$STACK_LINE
    printf 'R5 CONTROL head: src/ of %s, %s; parent: src/ of %s, %s\n' \
      "$head_src" "$stack_line" "$parent_src" "$parent_stack_line"
  fi

  # The switch: built when missing or unfinished (no Rocq commit in $CUT_ROOT/rocq-commit, which build_switch
  # writes once the switch is complete; S9b), except where a packed root must have been unpacked; --source-at uses
  # none.
  if [[ $mode != source ]]; then
    local switch_state=''
    read_rocq_commit "$CUT_ROOT"
    if [[ ! -d $OPAMROOT/cut ]]; then
      switch_state="no switch at $OPAMROOT/cut"
    elif [[ -z $RC_SHA ]]; then
      switch_state="the switch at $OPAMROOT/cut is unfinished: $CUT_ROOT/rocq-commit is missing, unreadable or empty"
    fi
    if [[ -n $switch_state ]]; then
      if [[ $mode == import || $mode == check ]]; then
        fail "$switch_state; unpack the packed opam root at $CUT_ROOT first"
      fi
      if [[ ${CUT_SELF_TEST_STUBS:-} == 1 ]]; then fail "$switch_state, and the self-test never builds one"; fi
      build_switch || fail "building the switch at $OPAMROOT/cut failed (see the output above)"
    fi
  fi

  # The Rocq commit: the switch's, read from $CUT_ROOT/rocq-commit, must be readable and be the cut's
  # CUT_ROCQ_COMMIT (S9, S9b). --source-at reports the rocq on the caller's PATH and the commit of that toolchain's
  # rocq-commit file, or unknown (path_toolchain), and fails when PATH has no rocq.
  if [[ $mode == source ]]; then
    path_toolchain
    [[ -n $TC_ROCQ ]] || fail "no rocq on PATH; --source-at builds with the caller's toolchain"
    printf 'ROCQ EXECUTABLE %s\n' "$TC_ROCQ"
    printf 'ROCQ COMMIT %s\n' "${TC_SHA:-unknown}"
  else
    read_rocq_commit "$CUT_ROOT"
    [[ -n $RC_SHA ]] || fail "cannot read the Rocq commit of the switch from $CUT_ROOT/rocq-commit (missing, unreadable or empty); the cut is never assumed"
    [[ $RC_SHA == "$CUT_ROCQ_COMMIT" ]] || fail "the switch's Rocq is commit $RC_SHA, not the cut $CUT_ROCQ_COMMIT"
    if [[ $mode != import && $mode != check ]]; then printf 'ROCQ COMMIT %s\n' "$RC_SHA" >&2; fi
  fi

  if [[ $mode == suite || $mode == source ]]; then
    fetch_lfs "$run_tree" || fail "fetching the git-LFS fixtures failed (see the output above)"
  fi

  # Run, and the verdict of each mode.
  local log=$WORK/test.log actual n unmet
  local -a cmd=() logs=()
  case $mode in
    suite)
      printf '%s\n' "$stack_line" >&2
      run_logged "$log" suite "$want" suite "$ROOT"
      if ((RUN_RC == 0)); then
        printf 'SUITE PASS\n'
        exit 0
      fi
      if ((RUN_RC == RT_BUILD_FAILED)); then fail "the plugin build failed: $(first_error_line "$log")"; fi
      fail "the suite failed (status $RUN_RC): $(first_error_line "$log")"
      ;;
    revert)
      fetch_lfs "$WORK/head" || fail "--revert-fix $test_arg: head side: fetching the git-LFS fixtures failed"
      run_logged "$WORK/head.log" head "$want" one "$WORK/head" "$name"
      if ((RUN_RC != 0)); then
        fail "--revert-fix $test_arg: R5 negative not met: the head side fails at $expected (src/ of $head_src, $stack_line)"
      fi
      run_tree=$WORK/tree
      source_at_prepare "$ROOT" "$run_tree" "$parent_src" "$name"
      local at="src/ of $parent_src, $parent_stack_line"
      [[ $SA_STATUS == ok ]] || fail "--revert-fix $test_arg: parent side ($at): $SA_CAUSE"
      fetch_lfs "$run_tree" || fail "--revert-fix $test_arg: parent side ($at): fetching the git-LFS fixtures failed"
      run_logged "$log" parent "$parent_want" one "$run_tree" "$name"
      # Check the parent side's failure: r5 lines, an option's Set line, or the first entry error of the
      # run's log followed by Redirect logs in the order of the test's Redirect commands (S7c-S7f).
      if ((RUN_RC == RT_BUILD_FAILED)); then
        fail "--revert-fix $test_arg: the parent side's plugin build failed ($at): $(first_error_line "$log"); a failed build is not \"R5 negative\""
      fi
      if ((RUN_RC == 0)); then
        fail "--revert-fix $test_arg: R5 negative not met: the test passes ($at)"
      fi
      if [[ -n $r5_facts ]]; then
        unmet=$(r5_unmet "$run_tree/tests/$name.v" "$expected" "$log" "$run_tree/tests")
        if [[ -z $unmet ]]; then
          while IFS=$'\t' read -r kind a b; do printf 'R5 CASE MET: tests/%s.v, r5 %s %s: %s\n' "$name" "$kind" "$a" "$b" >&2; done <<<"$r5_facts"
          negative_met "$test_arg" "$expected" "$parent_src"
        fi
        fail "--revert-fix $test_arg: R5 negative not met: the test fails, but not as the r5 lines of tests/$name.v say: ${unmet//$'\n'/; }; its row names $expected ($at)"
      fi
      logs=("$log")
      while IFS= read -r n; do
        if [[ -n $n ]]; then logs+=("$n"); fi
      done <<<"$(redirect_logs "$run_tree/tests/$name.v" "$run_tree/tests")"
      actual=$(first_entry_error "${logs[@]}")
      if [[ -z $actual ]]; then actual='no "Error at line N (for X)" line of its log or its Redirect .out files'; fi
      if [[ $expected == option:* ]]; then
        if option_failure_seen "$log" "${expected#option:}"; then negative_met "$test_arg" "$expected" "$parent_src"; fi
        fail "--revert-fix $test_arg: R5 negative not met: the test fails at $actual, not at its Set line for \"${expected#option:}\"; its row names $expected ($at)"
      fi
      if [[ $actual == "$expected" ]]; then negative_met "$test_arg" "$expected" "$parent_src"; fi
      fail "--revert-fix $test_arg: R5 negative not met: the test fails at $actual, but its row names $expected ($at)"
      ;;
    source)
      printf '%s\n' "$stack_line" >&2
      run_logged "$log" suite "$want" one "$run_tree" "$name"
      if ((RUN_RC == RT_BUILD_FAILED)); then
        printf 'SOURCE-AT BUILD FAILED: %s\n' "$(first_error_line "$log")" >&2
        exit 4
      fi
      if ((RUN_RC == 0)); then printf 'SOURCE-AT TEST pass\n'; else printf 'SOURCE-AT TEST fail\n'; fi
      while IFS=$'\t' read -r kind a b; do
        [[ $kind == case ]] || continue
        case_outcome "$run_tree/tests/$b.out" "$a"
        if [[ $CASE_OUTCOME == accepted ]]; then
          printf 'SOURCE-AT ACCEPTED %s in %s\n' "$a" "$b"
        else
          printf 'SOURCE-AT CASE %s in %s: %s\n' "$a" "$b" "$CASE_OUTCOME" >&2
        fi
      done <<<"$cases"
      exit "$RUN_RC"
      ;;
    import | check)
      { printf '%s\n' "$stack_line" && printf 'ROCQ COMMIT %s\n' "$RC_SHA"; } >"$stack_out" || fail "cannot write $stack_out"
      if [[ $mode == import ]]; then
        if stubbed CUT_STUB_COMPILE; then
          cmd=("$CUT_STUB_COMPILE")
        else
          ensure_opam || fail "no opam to run rocq compile with"
          cmd=("$OPAM_BIN" exec -- rocq compile)
        fi
        run_passthrough "$WORK/stderr.log" "$want" "$(dirname -- "${files[0]}")" \
          "${cmd[@]}" "${flags[@]}" "$(basename -- "${files[0]}")"
      else
        if stubbed CUT_STUB_CHECK; then
          cmd=("$CUT_STUB_CHECK")
        else
          ensure_opam || fail "no opam to run rocqchk with"
          cmd=("$OPAM_BIN" exec -- rocqchk)
        fi
        run_passthrough "$WORK/stderr.log" "$want" - "${cmd[@]}" -silent -o "${flags[@]}" "${files[@]}"
      fi
      if ((RUN_RC == 0)); then exit 0; fi
      fail "--$mode ${files[0]}: $(first_error_line "$WORK/stderr.log")"
      ;;
  esac
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then main "$@"; fi
