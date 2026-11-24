#!/usr/bin/env bash
# ci/build-9.2-cut.sh: build Rocq at one fixed commit (the "cut"), build the rocq-lean-import plugin against
# it, and run the test suite. The GitHub workflow .github/workflows/build-9.2-cut.yml and batch Jobs call this
# one script; `ci/build-9.2-cut.sh --help` lists its modes.
#
# Layout: settings, helpers, main. The pins and settings build_switch builds the opam root from are in
# ci/cut-settings.sh, which this script sources, and the self-test (--self-test) is in
# ci/build-9.2-cut-selftest.sh. main is the only function that decides an outcome: which verdict line to print
# and which status to exit with. The helpers (check_inventory, revert_fix_prepare, stack_probe, ...) gather facts
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

# CUT_STACK_KIB: the soft stack size, in KiB, for every test run, --import and --check. Only a commit sets
# it, by adding the line CUT_STACK_KIB=<integer> (at the start of the line) right below the last line of this
# comment; no such line means "unset", which keeps the default soft stack. The script reads that line from
# its own file instead of using the shell variable, so that --revert-fix can read the value the reverted
# copy of this file holds (reverting the commit that set it unsets it). The environment variable of that
# name is ignored.
# The CUT_STACK_KIB=<integer> line, when a commit adds one, goes right below this line.

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
# self-test points CUT_ROOT at a directory whose rocq-commit file it writes for each case.
stubbed() { [[ ${CUT_SELF_TEST_STUBS:-} == 1 && -n ${!1:-} ]]; }

# RUN_TEST: the one command that builds the plugin and runs the tests (see run_test_real).
RUN_TEST=run_test_real
if stubbed CUT_STUB_RUN_TEST; then RUN_TEST=$CUT_STUB_RUN_TEST; fi

WORK=           # this run's scratch directory, under $TMPDIR
WORKTREES=()    # git worktrees to remove on exit
SCRATCH_DIRS=() # directories to delete on exit
OPAM_BIN=
FAIL_PREFIX='FAIL: '
FAIL_CODE=1

usage() {
  cat <<'EOF'
Usage:
  ci/build-9.2-cut.sh
      Check the inventory, build Rocq at the cut (once per $CUT_ROOT), build the plugin, run the suite.
  ci/build-9.2-cut.sh --handoff
      The same, and fail while an inventory row is still open.
  ci/build-9.2-cut.sh --revert-fix <test>
      In a scratch copy, revert the fix commits of <test>'s inventory row, then check that <test> fails at
      the entry its row names ("R5 negative").
  ci/build-9.2-cut.sh --import <file.v> [-- <rocq compile flags>]
      Compile one file with the cut, in the file's directory; writes <file.v>.stack.
  ci/build-9.2-cut.sh --check <file.vo>... [-- <rocqchk flags>]
      Run the cut's rocqchk -silent -o on the files; writes <first file>.stack.
  ci/build-9.2-cut.sh --source-at <commit> <test>
      Build the plugin from <commit>'s src/ with the head's tests/ and dumps/, run <test>, report the
      planted entries it accepted. Exit 3: bad commit or test; 4: plugin build failed; else the test's.
  ci/build-9.2-cut.sh --self-test
      Check this script's rules (rows S0 to S24c of ci/build-9.2-cut-selftest.sh) with stubs (needs git and
      bash only).
Environment: CUT_ROOT (default /scratch/cs/cut) holds the opam root, the sources and the rocq-commit file;
CUT_JOBS (default: nproc) is the build parallelism.
EOF
}

# Print one verdict line and exit; main is its only caller and chooses the line.
fail() {
  printf '%s%s\n' "$FAIL_PREFIX" "$*" >&2
  exit "$FAIL_CODE"
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
#   row <line no> <file> <base_entry> <own_entry> <status> <in tests/_CoqProject: yes|no> <commits>
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
      if ((${#fld[@]} != 6)); then
        printf 'unreadable\t%s\t%s fields, not 6\t%s\n' "$n" "${#fld[@]}" "${line//$'\t'/\\t}"
        continue
      fi
      for f in 0 1 2 3 4 5; do
        if [[ -z ${fld[f]} ]]; then break; fi
      done
      if [[ -z ${fld[f]} ]]; then
        local -a names=(file features base_entry own_entry status commits)
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
      has_row["$file"]=1
      printf 'row\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$n" "$file" "${fld[2]}" "${fld[3]}" "$status" \
        "$([[ -n ${project[$file]:-} ]] && echo yes || echo no)" "${fld[5]}"
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

# <want>: in the subshell of a run, set the soft stack to <want> KiB, "-" keeping the default; non-zero, with a
# message on stderr, when it cannot be set.
stack_enter() {
  [[ $1 == - ]] && return 0
  stack_apply "$1" || {
    echo "cannot set the soft stack to $1 KiB" >&2
    return 1
  }
}

stack_probe() { # <want or ->: prints "<soft> <hard>" as read back after setting <want>; non-zero if setting failed
  (
    if [[ $1 != - ]]; then stack_apply "$1" || exit 1; fi
    printf '%s %s\n' "$(stack_read soft "$1")" "$(stack_read hard "$1")"
  )
}

uname_r() { # `uname -r`, or its stub; the status is theirs
  if stubbed CUT_STUB_UNAME_R; then "$CUT_STUB_UNAME_R"; else uname -r; fi
}

# ---- Switch ---------------------------------------------------------------------------------------------------

read_rocq_commit() { # fact RC_SHA: the commit in $CUT_ROOT/rocq-commit; empty when missing, unreadable or empty
  local f=$CUT_ROOT/rocq-commit
  RC_SHA=
  if [[ -f $f && -r $f ]]; then IFS= read -r RC_SHA <"$f"; fi
  RC_SHA=${RC_SHA//[[:space:]]/}
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
  local cmd pkg config
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
  # The switch is missing, so whatever else is under the root is an earlier, unfinished build.
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
  if ! grep -qx 'version: 4.14.2' <<<"$config" || ! grep -qx 'flambda: true' <<<"$config" ||
    ! grep -qx 'naked_pointers: false' <<<"$config"; then
    echo "the switch's ocamlopt -config does not report version 4.14.2, flambda true, naked_pointers false" >&2
    return 1
  fi
  step "$OPAM_BIN" repo add --this-switch coq-released "$CUT_ROOT/src/rocq-opam/released" || return 1
  shallow_fetch "$CUT_ROCQ_REPO" "$CUT_ROCQ_COMMIT" "$CUT_ROOT/src/rocq" || return 1
  # All five: an unpinned one resolves to the upstream release.
  for pkg in rocq-runtime rocq-core coq-core coqide-server coq; do
    step "$OPAM_BIN" pin add -yn --with-version "$ROCQ_VERSION" "$pkg" "$CUT_ROOT/src/rocq" || return 1
  done
  step "$OPAM_BIN" pin add -yn --kind=version coq-stdlib "$ROCQ_STDLIB_VERSION" || return 1
  step "$OPAM_BIN" pin add -yn --kind=version rocq-stdlib "$ROCQ_STDLIB_VERSION" || return 1
  step "$OPAM_BIN" pin add -yn --kind=version dune "$DUNE_VERSION" || return 1
  step "$OPAM_BIN" install coq coq-stdlib yojson || return 1
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
# `make tests/<name>.vo` (the root Makefile forwards tests/% goals).
run_test_real() {
  local kind=$1 tree=$2 name=${3:-}
  ensure_opam || return "$RT_BUILD_FAILED"
  cd -- "$tree" || return "$RT_BUILD_FAILED"
  "$OPAM_BIN" exec -- make || return "$RT_BUILD_FAILED"
  if [[ $kind == suite ]]; then
    "$OPAM_BIN" exec -- make -k test
  else
    "$OPAM_BIN" exec -- make "tests/$name.vo"
  fi
}

# <log> <want> <RUN_TEST args...>: run RUN_TEST at the soft stack <want> ("-": the default) in a subshell,
# its output copied to <log> and to stderr. Fact RUN_RC: RUN_TEST's status.
run_logged() {
  local log=$1 want=$2
  shift 2
  (
    stack_enter "$want" || exit 1
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
      stack_enter "$want" || exit 1
      exec "$@"
    ) 2>&1 1>&3 3>&- | tee "$errlog" >&2 3>&-
    RUN_RC=${PIPESTATUS[0]}
  } 3>&1
}

# <root> <tree> <commit...>: a detached worktree of HEAD at <tree>, with the commits reverted newest first
# (git revert --no-commit). Facts: RV_STATUS ok|conflict|error, RV_ORDER, RV_FILES (unmerged), RV_MSG.
revert_fix_prepare() {
  local root=$1 tree=$2 c out history
  shift 2
  local -A want=()
  local -a order=()
  RV_STATUS=error RV_ORDER='' RV_FILES='' RV_MSG=''
  for c in "$@"; do want[$c]=1; done
  history=$(git -C "$root" rev-list --topo-order HEAD) || {
    RV_MSG="git rev-list HEAD failed"
    return 0
  }
  while IFS= read -r c; do
    if [[ -n $c && -n ${want[$c]:-} ]]; then order+=("$c"); fi
  done <<<"$history"
  RV_ORDER=${order[*]}
  if ((${#order[@]} != ${#want[@]})); then
    RV_ORDER=$*
    RV_MSG="not every commit of the row is in HEAD's history"
    return 0
  fi
  out=$(git -C "$root" worktree add --detach "$tree" HEAD 2>&1) || {
    RV_MSG="git worktree add failed: ${out//$'\n'/ }"
    return 0
  }
  WORKTREES+=("$tree")
  if out=$(git -C "$tree" -c user.name=build-9.2-cut -c user.email=build-9.2-cut@localhost \
    revert --no-commit "${order[@]}" 2>&1); then
    RV_STATUS=ok
    return 0
  fi
  RV_MSG=${out//$'\n'/ }
  RV_FILES=$(git -C "$tree" diff --name-only --diff-filter=U 2>/dev/null)
  RV_FILES=${RV_FILES//$'\n'/ }
  if [[ -n $RV_FILES ]]; then RV_STATUS=conflict; fi
  return 0
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

first_entry_error() { # <log>: the X of the log's first "Error at line N (for X)", or nothing
  local line
  while IFS= read -r line || [[ -n $line ]]; do
    if entry_error_name "$line"; then
      printf '%s' "$ENTRY_NAME"
      return 0
    fi
  done <"$1"
  return 0
}

# <files...>: "seen<TAB>X" for each line "line N: X", "error<TAB>X" for each "Error at line N (for X)".
entry_scan() {
  local f line re='^[[:space:]]*line [0-9]+: (.*[^[:space:]])[[:space:]]*$'
  for f in "$@"; do
    [[ -f $f ]] || continue
    while IFS= read -r line || [[ -n $line ]]; do
      if [[ $line =~ $re ]]; then
        printf 'seen\t%s\n' "${BASH_REMATCH[1]}"
      elif entry_error_name "$line"; then
        printf 'error\t%s\n' "$ENTRY_NAME"
      fi
    done <"$f"
  done
  return 0
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

planted_entries() { # <test file>: the Lean name of each "(* planted: <name> *)" line
  local line re='^[[:space:]]*\(\*[[:space:]]+planted:[[:space:]]+([^[:space:]]+)[[:space:]]+\*\)[[:space:]]*$'
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ $line =~ $re ]]; then printf '%s\n' "${BASH_REMATCH[1]}"; fi
  done <"$1"
  return 0
}

redirect_logs() { # <test file> <dir>: <dir>/<name>.out for each Redirect "<name>" of the test (Rocq adds .out)
  local line re='Redirect[[:space:]]+"([^"]+)"'
  while IFS= read -r line || [[ -n $line ]]; do
    if [[ $line =~ $re ]]; then printf '%s/%s.out\n' "$2" "${BASH_REMATCH[1]}"; fi
  done <"$1"
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
  # --source-at keeps its own exit codes: every failure before the test is a SOURCE-AT ERROR, status 3.
  if [[ $mode == source ]]; then FAIL_PREFIX='SOURCE-AT ERROR: ' FAIL_CODE=3; fi
  [[ $CUT_ROOT == /* ]] || fail "CUT_ROOT must be an absolute path (an opam root is not relocatable): $CUT_ROOT"
  WORK=$(mktemp -d "${TMPDIR:-/tmp}/build-9.2-cut.XXXXXX") || fail "cannot create a scratch directory under ${TMPDIR:-/tmp}"
  SCRATCH_DIRS+=("$WORK")

  # Inventory checks, in the default mode, --handoff and --revert-fix (S1-S4, S3b, S10-S13): every row of the
  # inventory is readable and agrees with tests/_CoqProject (every row's test is listed there: a listed row's
  # test checks that its feature's entry is refused, so the suite passes), a fixed row names commits that are ancestors of HEAD, every tests/lean434_*.v has a
  # row, and every member of the predeclared tables of src/lean.ml has its marker in tests/predeclared.v;
  # --handoff also fails on an open row. A missing or empty inventory skips the checks while the head has no
  # tests/lean434_*.v. --import and --check run on trees without history (S23), and --source-at measures an
  # old src/ with only its own exit codes (S24): neither checks the inventory.
  local -a row_line=() row_file=() row_base=() row_own=() row_status=() row_inproj=() row_commits=()
  if [[ $mode == suite || $mode == revert ]]; then
    local facts kind a b c d e g inv_state=missing pred_state=missing where st
    local -a fails=() lean434=() lean434_norow=() commit_fails=() table_errors=() unmarked=() unreadable=()
    local -A first_line=()
    facts=$(check_inventory "$ROOT") || fail "the inventory checks could not run"
    while IFS=$'\t' read -r kind a b c d e f g; do
      case $kind in
        inventory) inv_state=$a ;;
        unreadable) unreadable+=("$INVENTORY line $a cannot be read ($b): $c") ;;
        row)
          row_line+=("$a") row_file+=("$b") row_base+=("$c") row_own+=("$d") row_status+=("$e")
          row_inproj+=("$f") row_commits+=("$g")
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
  local expected='' run_tree=$ROOT stack_file=$SELF stack_out='' idx=-1
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
    revert_fix_prepare "$ROOT" "$WORK/tree" "${commits[@]}"
    case $RV_STATUS in
      ok) ;;
      conflict) fail "--revert-fix $test_arg: reverting $RV_ORDER conflicts in $RV_FILES; a conflict is not \"R5 negative\"" ;;
      *) fail "--revert-fix $test_arg: git revert --no-commit $RV_ORDER failed: $RV_MSG" ;;
    esac
    # The test runs at the stack the scratch copy's own script holds: reverting the commit that set
    # CUT_STACK_KIB unsets it there (S22).
    run_tree=$WORK/tree stack_file=$WORK/tree/$SCRIPT_REL
  fi
  if [[ $mode == source ]]; then
    name=${test_arg#tests/} name=${name%.v}
    source_at_prepare "$ROOT" "$WORK/tree" "$commit_arg" "$name"
    [[ $SA_STATUS == ok ]] || fail "$SA_CAUSE"
    run_tree=$WORK/tree
  fi
  if [[ $mode == import || $mode == check ]]; then
    for f in "${files[@]}"; do
      [[ -f $f ]] || fail "--$mode: no such file: $f"
    done
    stack_out=${files[0]}.stack
  fi

  # Stack, decided before any test, --import or --check runs (S17-S21, S20b): CUT_STACK_KIB, when this
  # script's file sets it, must be a positive whole number of KiB, at most the hard limit and, under gVisor (or
  # when uname -r cannot tell), at most 128 MiB; the soft stack read back must then equal it. Unset, the default
  # soft stack is kept, and it must be a number: gVisor turns an unlimited one into 8 MiB.
  local want=- probe soft hard un_out un_rc
  read_stack_assignment "$stack_file"
  if ((STACK_SET)); then
    [[ $STACK_RAW =~ ^[1-9][0-9]{0,17}$ ]] || fail "CUT_STACK_KIB='$STACK_RAW' is not a positive whole number of KiB"
    want=$STACK_RAW
    hard=$(stack_read hard "$want")
    if [[ $hard != unlimited ]]; then
      [[ $hard =~ ^[0-9]+$ ]] || fail "cannot read the hard stack limit (read '$hard')"
      ((want <= hard)) || fail "CUT_STACK_KIB=$want is above the hard stack limit of $hard KiB"
    fi
    if ((want > GVISOR_STACK_CAP_KIB)); then
      un_out=$(uname_r 2>/dev/null)
      un_rc=$?
      if ((un_rc != 0)) || [[ -z $un_out || ${un_out,,} == *gvisor* ]]; then
        fail "CUT_STACK_KIB=$want is above $GVISOR_STACK_CAP_KIB KiB, and gVisor caps the stack at 128 MiB (uname -r: ${un_out:-failed or printed nothing})"
      fi
    fi
  fi
  probe=$(stack_probe "$want") || fail "cannot set the soft stack to $want KiB"
  read -r soft hard <<<"$probe"
  if [[ $want == - ]]; then
    [[ $soft != unlimited ]] || fail "the default soft stack is unlimited, which gVisor turns into 8 MiB; a commit must set CUT_STACK_KIB"
    [[ $soft =~ ^[0-9]+$ ]] || fail "cannot read the soft stack limit (read '$soft')"
  else
    [[ $soft == "$want" ]] || fail "the soft stack read back is $soft KiB, not CUT_STACK_KIB=$want"
  fi
  local stack_line="STACK soft=$soft hard=${hard:-unknown}"

  # The switch: built when missing, except where a packed root must have been unpacked.
  if [[ ! -d $OPAMROOT/cut ]]; then
    if [[ $mode == import || $mode == check ]]; then
      fail "no switch at $OPAMROOT/cut; unpack the packed opam root at $CUT_ROOT first"
    fi
    if [[ ${CUT_SELF_TEST_STUBS:-} == 1 ]]; then fail "no switch at $OPAMROOT/cut, and the self-test never builds one"; fi
    build_switch || fail "building the switch at $OPAMROOT/cut failed (see the output above)"
  fi

  # The Rocq commit: the switch's, read from $CUT_ROOT/rocq-commit, must be readable and be the cut's
  # CUT_ROCQ_COMMIT (S9, S9b); --source-at only reports it.
  read_rocq_commit
  if [[ $mode == source ]]; then
    printf 'ROCQ COMMIT %s\n' "${RC_SHA:-unknown}"
  else
    [[ -n $RC_SHA ]] || fail "cannot read the Rocq commit of the switch from $CUT_ROOT/rocq-commit (missing, unreadable or empty); the cut is never assumed"
    [[ $RC_SHA == "$CUT_ROCQ_COMMIT" ]] || fail "the switch's Rocq is commit $RC_SHA, not the cut $CUT_ROCQ_COMMIT"
    if [[ $mode != import && $mode != check ]]; then printf 'ROCQ COMMIT %s\n' "$RC_SHA" >&2; fi
  fi

  if [[ $mode != import && $mode != check ]]; then
    fetch_lfs "$run_tree" || fail "fetching the git-LFS fixtures failed (see the output above)"
  fi

  # Run, and the verdict of each mode.
  local log=$WORK/test.log actual n
  local -a cmd=() logs=()
  local -A seen=() errored=()
  case $mode in
    suite)
      printf '%s\n' "$stack_line" >&2
      run_logged "$log" "$want" suite "$ROOT"
      if ((RUN_RC == 0)); then
        printf 'SUITE PASS\n'
        exit 0
      fi
      if ((RUN_RC == RT_BUILD_FAILED)); then fail "the plugin build failed: $(first_error_line "$log")"; fi
      fail "the suite failed (status $RUN_RC): $(first_error_line "$log")"
      ;;
    revert)
      # "R5 negative": with its row's fix commits reverted, the test fails, and it fails at the entry its row
      # names (its own entry, else its base entry), or for an option row at the Set line of that option; a
      # conflicting revert or a failed plugin build does not count.
      printf '%s\n' "$stack_line" >&2
      run_logged "$log" "$want" one "$run_tree" "$name"
      if ((RUN_RC == RT_BUILD_FAILED)); then
        fail "--revert-fix $test_arg: the plugin build failed after reverting $RV_ORDER: $(first_error_line "$log"); a failed build is not \"R5 negative\""
      fi
      if ((RUN_RC == 0)); then
        fail "--revert-fix $test_arg: R5 negative not met: the test passes with $RV_ORDER reverted"
      fi
      actual=$(first_entry_error "$log")
      if [[ -z $actual ]]; then actual='no "Error at line N (for X)" line'; fi
      if [[ $expected == option:* ]]; then
        if option_failure_seen "$log" "${expected#option:}"; then
          printf 'R5 NEGATIVE MET: %s at %s\n' "$test_arg" "$expected"
          exit 0
        fi
        fail "--revert-fix $test_arg: R5 negative not met: the test fails at $actual, not at its Set line for \"${expected#option:}\"; its row names $expected"
      fi
      if [[ $actual == "$expected" ]]; then
        printf 'R5 NEGATIVE MET: %s at %s\n' "$test_arg" "$expected"
        exit 0
      fi
      fail "--revert-fix $test_arg: R5 negative not met: the test fails at $actual, but its row names $expected"
      ;;
    source)
      printf '%s\n' "$stack_line" >&2
      run_logged "$log" "$want" one "$run_tree" "$name"
      if ((RUN_RC == RT_BUILD_FAILED)); then
        printf 'SOURCE-AT BUILD FAILED: %s\n' "$(first_error_line "$log")" >&2
        exit 4
      fi
      if ((RUN_RC == 0)); then printf 'SOURCE-AT TEST pass\n'; else printf 'SOURCE-AT TEST fail\n'; fi
      logs=("$log")
      while IFS= read -r n; do
        if [[ -n $n ]]; then logs+=("$n"); fi
      done <<<"$(redirect_logs "$run_tree/tests/$name.v" "$run_tree/tests")"
      while IFS=$'\t' read -r kind n; do
        case $kind in
          seen) seen["$n"]=1 ;;
          error) errored["$n"]=1 ;;
        esac
      done <<<"$(entry_scan "${logs[@]}")"
      while IFS= read -r n; do
        if [[ -n $n && -n ${seen[$n]:-} && -z ${errored[$n]:-} ]]; then printf 'SOURCE-AT ACCEPTED %s\n' "$n"; fi
      done <<<"$(planted_entries "$run_tree/tests/$name.v")"
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
