# shellcheck shell=bash
# ci/build-9.2-cut-selftest.sh: the self-test of ci/build-9.2-cut.sh, whose --self-test mode sources this file and
# runs self_test. It reads the settings and helpers of that script (SELF, SETTINGS, SCRIPT_REL, INVENTORY, ...).

# ---- Self-test ------------------------------------------------------------------------------------------------
# One row per rule of ci/build-9.2-cut.sh (S0 to S24d, S7l-A2 to S7l-A8e and V1 to V16), stated in the comments
# below. Each case of a row runs on its own copy of a scratch git repository (made with git init and real commits
# under a mktemp -d of $TMPDIR), through a copy of the script with the stubs its "Self-test stubs" section
# describes. A row passes only when every one of its cases shows the exit status and the lines or files the row
# names. Rows S25 to S27 (st_repo_rows) read the repository that holds this file instead: its tests' Redirect logs,
# the inputs of build_switch and the workflow.

ST_MEMBERS=(Eq Nat Nat.le Or And Fin UInt32 BitVec Char ULift UInt32.size Nat.isValidChar Nat.pow)
ST_ROOT='' ST_CASE='' ST_REPO='' ST_LABEL='' ST_WHY='' ST_RC=0 ST_N=0 ST_PASS=0 ST_FAIL=0
ST_BASE='' ST_FIX_A='' ST_FIX_B='' ST_FIX_OPT='' ST_ROW_A='' ST_ROW_B='' ST_ROW_C='' ST_ROW_OPT=''
ST_OTHER_SHA=1111111111111111111111111111111111111111
ST_CALLER_SHA=2222222222222222222222222222222222222222 # the caller toolchain's rocq-commit (st_new)

st_tsv() {
  local IFS=$'\t'
  printf '%s' "$*"
}

st_inventory() { # <rows...>: an inventory with a header comment (line 1) and the rows from line 2
  local r
  printf '# file\tfeatures\tbase_entry\town_entry\tstatus\tcommits\tstack\n'
  for r in "$@"; do printf '%s\n' "$r"; done
}

st_predeclared() { # <members...>: a tests/predeclared.v marking those members
  local m
  printf '(* Stand-in: one marker per predeclared member of src/lean.ml. *)\n'
  for m in "$@"; do printf '(* predeclared member: %s *)\n' "$m"; done
}

st_predeclared_without() { # <member>
  local m
  local -a ms=()
  for m in "${ST_MEMBERS[@]}"; do
    if [[ $m != "$1" ]]; then ms+=("$m"); fi
  done
  st_predeclared "${ms[@]}"
}

st_lean_ml() { # [bad-entry|no-table]: a stand-in src/lean.ml with the three tables laid out as in the real one
  local pow='      (Nat_pow, [ "Nat"; "pow" ], Legacy_path_only);' asdef=get_predeclared_ind_as_def_any
  if [[ ${1:-} == bad-entry ]]; then pow='      (Nat_pow, nat_pow_name, Legacy_path_only);'; fi
  if [[ ${1:-} == no-table ]]; then asdef=get_predeclared_ind_as_def_list; fi
  cat <<EOF
(* Stand-in for the predeclared tables of src/lean.ml. *)
let get_predeclared_ind_any ?(ctors = []) ?(uint32_is_legacy = false) n i =
  let std indh = get_predeclared_ind indh n i in
  let uint32 indh = get_predeclared_uint32 ~ctors indh n i in
  let char indh = get_predeclared_char ~uint32_is_legacy indh n i in
  List.filter_map
    (fun (indk, indh, paths, lookup) ->
      if not (on_current_path paths) then None
      else lookup indh |> Option.map (fun x -> (indk, indh, x)))
    [
      (Eq, [ "Eq" ], Both_paths, std);
      (Nat, [ "Nat" ], Both_paths, std);
      (Nat_le, [ "Nat"; "le" ], Both_paths, std);
      (Or, [ "Or" ], Both_paths, std);
      (And, [ "And" ], Both_paths, std);
      (Fin, [ "Fin" ], Both_paths, std);
      (UInt32, [ "UInt32" ], Legacy_path_only, uint32);
      (BitVec, [ "BitVec" ], Legacy_path_only, std);
      (Char, [ "Char" ], Legacy_path_only, char);
    ]

let get_predeclared_ind_some ?(ctors = []) ?(uint32_is_legacy = false) n i =
  match get_predeclared_ind_any ~ctors ~uint32_is_legacy n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ -> CErrors.user_err Pp.(str "Multiple predeclared inductive types")

let $asdef n i =
  List.filter_map
    (fun (k, h) ->
      get_predeclared_ind_as_def h n i |> Option.map (fun x -> (k, h, x)))
    [
      (ULift_cumul, [ "ULift" ]);
    ]

let get_predeclared_def_any n i =
  List.filter_map
    (fun (defk, defh, paths) ->
      if not (on_current_path paths) then None
      else get_predeclared_def defh n i |> Option.map (fun x -> (defk, defh, x)))
    [
      (UInt32_size, [ "UInt32"; "size" ], Legacy_path_only);
      (Nat_isValidChar, [ "Nat"; "isValidChar" ], Legacy_path_only);
$pow
    ]
EOF
}

st_set_stack() { # <script file> <value|none>: remove its CUT_STACK_KIB= line, then add one below the anchor
  local file=$1 value=$2 line out=
  while IFS= read -r line || [[ -n $line ]]; do
    [[ $line == CUT_STACK_KIB=* ]] && continue
    out+=$line$'\n'
    if [[ $line == "$STACK_ANCHOR" && $value != none ]]; then out+="CUT_STACK_KIB=$value"$'\n'; fi
  done <"$file"
  printf '%s' "$out" >"$file"
}

st_git_commit() { # <repo> <message>
  git -C "$1" add -A && git -C "$1" commit -q -m "$2"
}

st_stubs() {
  local s=$ST_ROOT/stubs
  mkdir -p "$s" || return 1
  cat >"$s/run-test" <<'EOF'
#!/usr/bin/env bash
# Self-test stand-in for RUN_TEST. $1: suite|one, $2: tree, $3: test name. The side selects the outcome.
src_marker=$(<"$2/src/marker") tests_marker=$(<"$2/tests/marker") fixes=$(cd "$2/src" && echo fix_*.ml)
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "${3:--}" "$src_marker" "$tests_marker" "$fixes" \
  "${OPAMROOT-<unset>}" "${OPAMSWITCH-<unset>}" "${CUT_RUN_SIDE-<unset>}" "${CUT_RUN_STACK_WANT-<unset>}" >>"$ST_CALLS"
case ${CUT_RUN_SIDE-} in
  head) ST_OUTCOME=$ST_OUTCOME_HEAD ;;
  parent) ST_OUTCOME=$ST_OUTCOME_PARENT ;;
  suite) ;;
  *) echo "stub: unknown CUT_RUN_SIDE '${CUT_RUN_SIDE-}'" >&2; exit 99 ;;
esac
echo "STUB RUN-TEST $1 ${3:-}"
case $ST_OUTCOME in
  pass) echo "stub: the test passes"; exit 0 ;;
  fail:*)
    printf 'File "./%s.v", line 2, characters 0-50:\n' "${3:-test}"
    printf 'Error: Error at line 7 (for %s): {"def": 1}\nmissing something\n' "${ST_OUTCOME#fail:}"
    printf 'Error at line 9 (for Later.entry): {"def": 2}\n'
    exit 2 ;;
  fail-noentry) printf 'Error: Some other failure\n'; exit 2 ;;
  redirect:*)
    # Each word <name>=<entry>, in the order given: tests/<name>.out, the file of a Redirect, gets the importer's
    # error at <entry>; the name "-" puts it in the run's output instead. The test then fails at a line that
    # names no entry.
    for w in ${ST_OUTCOME#redirect:}; do
      if [[ ${w%%=*} == - ]]; then
        printf 'Error at line 5 (for %s): {"def": 3}\n' "${w#*=}"
      else
        printf 'line 7: %s\nError at line 7 (for %s): {"def": 1}\n' "${w#*=}" "${w#*=}" >"$2/tests/${w%%=*}.out"
      fi
    done
    printf 'File "./%s.v", line 2, characters 0-20:\nError: The reference alpha_check was not found.\n' "${3:-test}"
    exit 1 ;;
  option:*)
    printf 'File "./%s.v", line 3, characters 0-30:\n' "${3:-test}"
    printf 'Error: There is no flag or option with this name:\n"%s".\n' "${ST_OUTCOME#option:}"
    exit 2 ;;
  rocqchk:*)
    # The test compiles, and the rocqchk step of tests/Makefile refuses tests/<name>.vo, <name> the outcome's: the
    # line that step prints.
    printf 'ROCQCHK FAIL: tests/%s.vo: Unhandled code 0018\n' "${ST_OUTCOME#rocqchk:}" >&2
    exit 2 ;;
  build-fail)
    printf 'File "src/lean.ml", line 1, characters 0-5:\nError: Unbound value planted_build_error\n'
    exit 125 ;;
  source:*)
    # The cases of tests/planted_sa.v (st_template), one Redirect log each: Planted.ok accepted; Planted.err
    # refused; Planted.same refused in its first case and accepted in its second; Planted.pre seen only in another
    # case's log, its own log naming longer names; Planted.cut seen with no "Done!" after it; Planted.unstarted's
    # case not reached (no log); Planted.cross accepted in the run's own log only, which is no case.
    t=$2/tests
    printf 'line 1: Planted.cross\nDone!\n'
    printf 'line 2: Planted.pre\nline 3: Planted.ok\n\n\nDone!\n- 3 entries\n' >"$t/planted_ok.log.out"
    printf 'line 4: Planted.err\nError at line 4 (for Planted.err): {"bad": 1}\n\nDone!\n' >"$t/planted_err.log.out"
    printf 'line 5: Planted.same\nSkipping: Error at line 5 (for Planted.same): {"bad": 2}\nDone!\n' >"$t/planted_same_a.log.out"
    printf 'line 5: Planted.same\nDone!\n' >"$t/planted_same_b.log.out"
    printf 'line 6: Planted.prefix\nline 7: Planted.pre.x\nline 8: Planted.pre: 1 argument(s) transported (L)\nDone!\n' >"$t/planted_pre.log.out"
    printf 'Done!\nline 9: Planted.cut\n' >"$t/planted_cut.log.out"
    exit "${ST_OUTCOME#source:}" ;;
  play:*)
    # The case filled ST_FX: run.log is the run's output, the file unreadable names (one per line) the copied logs
    # whose mode is then set to 000, and every other file goes to tests/ of the tree as a Redirect log of the test.
    for f in "$ST_FX"/*; do
      [[ -f $f ]] || continue
      case ${f##*/} in
        run.log) cat -- "$f" ;;
        unreadable) ;;
        *) cp -- "$f" "$2/tests/" ;;
      esac
    done
    if [[ -f $ST_FX/unreadable ]]; then
      while IFS= read -r f; do chmod 000 -- "$2/tests/$f"; done <"$ST_FX/unreadable"
    fi
    exit "${ST_OUTCOME#play:}" ;;
  expect)
    # The case filled ST_FX with the Redirect logs of the test: each goes to tests/ of the tree, and the tree's own
    # tests/check_expect.py checks tests/<test name>.expect on them, as tests/Makefile does after a compile. Its
    # lines are in the run's output, and its status is the test's.
    for f in "$ST_FX"/*; do
      if [[ -f $f ]]; then cp -- "$f" "$2/tests/"; fi
    done
    python3 "$2/tests/check_expect.py" "$2/tests/$3.expect"
    exit ;;
  *) echo "stub: unknown ST_OUTCOME '$ST_OUTCOME'" >&2; exit 99 ;;
esac
EOF
  cat >"$s/ulimit" <<'EOF'
#!/usr/bin/env bash
# Self-test stand-in for the stack read-back. $1: soft|hard, $2: the KiB the setter was asked for, or "-". As the real
# setter (stack_apply) does, a value asked for lowers a hard limit of "unlimited" to it.
soft=$ST_SOFT
case ${CUT_RUN_SIDE-} in
  head) soft=${ST_SOFT_HEAD:-$soft} ;;
  parent) soft=${ST_SOFT_PARENT:-$soft} ;;
esac
case $1 in
  soft) if [[ -n $soft ]]; then echo "$soft"; elif [[ $2 == - ]]; then echo "$ST_DEFAULT_SOFT"; else echo "$2"; fi ;;
  hard) if [[ $ST_HARD == unlimited && $2 != - ]]; then echo "$2"; else echo "$ST_HARD"; fi ;;
esac
EOF
  cat >"$s/uname" <<'EOF'
#!/usr/bin/env bash
# Self-test stand-in for `uname -r`.
case $ST_UNAME in
  gvisor) echo 4.19.0-gvisor ;;
  generic) echo 6.1.0-generic ;;
  fail) exit 1 ;;
  empty) ;;
esac
EOF
  cat >"$s/compile" <<'EOF'
#!/usr/bin/env bash
# Self-test stand-in for `opam exec -- rocq compile`.
printf 'compile\t%s\t%s\t%s\t%s\n' "$PWD" "$*" "${CUT_RUN_SIDE-<unset>}" "${CUT_RUN_STACK_WANT-<unset>}" >>"$ST_CALLS"
echo "stub compile stdout"
echo "stub compile stderr" >&2
if [[ $ST_OUTCOME == fail ]]; then
  printf 'File "./Import.v", line 1, characters 0-9:\nError: planted compile error\n' >&2
  exit 1
fi
EOF
  cat >"$s/check" <<'EOF'
#!/usr/bin/env bash
# Self-test stand-in for `opam exec -- rocqchk`.
printf 'check\t%s\t%s\t%s\t%s\n' "$PWD" "$*" "${CUT_RUN_SIDE-<unset>}" "${CUT_RUN_STACK_WANT-<unset>}" >>"$ST_CALLS"
echo "stub check stdout"
echo "stub check stderr" >&2
if [[ $ST_OUTCOME == fail ]]; then
  printf 'Error: planted check error\n' >&2
  exit 1
fi
EOF
  chmod +x "$s/run-test" "$s/ulimit" "$s/uname" "$s/compile" "$s/check"
}

st_template() { # the repository every case copies: base, three fix commits, then the head with the inventory
  local t=$ST_ROOT/template f
  mkdir -p "$t/ci" "$t/src" "$t/tests" "$t/dumps" || return 1
  cp -- "$SELF" "$t/$SCRIPT_REL" && cp -- "$SETTINGS" "$t/ci/" && cp -- "$ROOT/tests/check_expect.py" "$t/tests/" || return 1
  st_lean_ml >"$t/src/lean.ml"
  printf 'src at base\n' >"$t/src/marker"
  printf '# stand-in\n' >"$t/Makefile"
  printf -- '-Q src LeanImport\n' >"$t/_CoqProject"
  printf 'dumps/*.ndjson.zip filter=lfs diff=lfs merge=lfs -text\n' >"$t/.gitattributes"
  printf '{}\n' >"$t/dumps/small.ndjson"
  printf -- '-Q ../src LeanImport\n-R . Test\n\ncore.v\nlean434_a.v\nlean434_b.v\nlean434_c.v\nlean434_opt.v\n' >"$t/tests/_CoqProject"
  for f in core lean434_a lean434_b lean434_c lean434_opt; do printf '(* stand-in test %s *)\n' "$f" >"$t/tests/$f.v"; done
  printf 'tests at base\n' >"$t/tests/marker"
  st_predeclared "${ST_MEMBERS[@]}" >"$t/$PREDECLARED_TEST"
  git -C "$t" -c init.defaultBranch=main init -q && st_git_commit "$t" base || return 1
  ST_BASE=$(git -C "$t" rev-parse HEAD)
  printf 'let fix_a = 1\n' >"$t/src/fix_a.ml"
  st_git_commit "$t" "fix a" || return 1
  ST_FIX_A=$(git -C "$t" rev-parse HEAD)
  printf 'let fix_b = 1\n' >"$t/src/fix_b.ml"
  st_git_commit "$t" "fix b" || return 1
  ST_FIX_B=$(git -C "$t" rev-parse HEAD)
  printf 'let fix_opt = 1\n' >"$t/src/fix_opt.ml"
  st_git_commit "$t" "fix opt" || return 1
  ST_FIX_OPT=$(git -C "$t" rev-parse HEAD)
  printf 'src at head\n' >"$t/src/marker"
  printf 'tests at head\n' >"$t/tests/marker"
  # One planted case per Redirect (the stub's source:<status> outcome writes their logs); the second marker of
  # Planted.same is separated from its Redirect by a comment.
  printf '%s\n' '(* planted: Planted.ok *)' 'Redirect "planted_ok.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.err *)' 'Redirect "planted_err.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.same *)' 'Redirect "planted_same_a.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.same *)' '(* The same name in a second case. *)' \
    'Redirect "planted_same_b.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.pre *)' 'Redirect "planted_pre.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.cut *)' 'Redirect "planted_cut.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.unstarted *)' 'Redirect "planted_unstarted.log" Lean Import "../dumps/small.ndjson".' \
    '(* planted: Planted.cross *)' 'Redirect "planted_cross.log" Lean Import "../dumps/small.ndjson".' \
    >"$t/tests/planted_sa.v"
  ST_ROW_A=$(st_tsv tests/lean434_a.v F1 Alpha.one - fixed "$ST_FIX_A" -)
  ST_ROW_B=$(st_tsv tests/lean434_b.v 'F2 F3' Beta.base Beta.own fixed "$ST_FIX_B" -)
  ST_ROW_C=$(st_tsv tests/lean434_c.v F4 Gamma.one - listed - -)
  ST_ROW_OPT=$(st_tsv tests/lean434_opt.v F5 'option:Lean Entry Timeout' - fixed "$ST_FIX_OPT" -)
  st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$t/$INVENTORY"
  st_git_commit "$t" "head: inventory" || return 1
}

st_new() { # <label>: a fresh case: a copy of the template, an empty TMPDIR, a switch stand-in at the cut, and the
  # caller's toolchain on PATH (st_toolchain, commit ST_CALLER_SHA)
  ST_LABEL=$1 ST_N=$((ST_N + 1))
  ST_CASE=$ST_ROOT/case$ST_N ST_REPO=$ST_ROOT/case$ST_N/repo
  if ! { mkdir -p "$ST_CASE/tmp" "$ST_CASE/cut/opam/cut" "$ST_CASE/fx" && cp -a "$ST_ROOT/template" "$ST_REPO" &&
    st_toolchain "$ST_CASE/caller" "$ST_CALLER_SHA"; }; then
    ST_WHY=${ST_WHY:-"$ST_LABEL: cannot set up the case"}
    return 1
  fi
  printf '%s\n' "$CUT_ROCQ_COMMIT" >"$ST_CASE/cut/rocq-commit"
  : >"$ST_CASE/calls"
}

st_toolchain() { # <root> <commit|none>: <root>/opam/cut/bin/rocq, the layout build_switch makes, and <root>/rocq-commit
  mkdir -p "$1/opam/cut/bin" && printf '#!/usr/bin/env bash\nexit 0\n' >"$1/opam/cut/bin/rocq" &&
    chmod +x "$1/opam/cut/bin/rocq" || return 1
  if [[ $2 != none ]]; then printf '%s\n' "$2" >"$1/rocq-commit"; fi
}

st_norocq_path() { # prints a PATH with the commands the script and st_run call and no rocq ($ST_ROOT/norocq)
  local d=$ST_ROOT/norocq t p
  if [[ ! -d $d ]]; then
    mkdir -p -- "$d" || return 1
    for t in bash env git mktemp dirname basename rm nproc cat readlink tee grep head tr cut sed ls mkdir cp uname python3; do
      if p=$(command -v "$t") && [[ $p == /* ]]; then ln -s -- "$p" "$d/$t" || return 1; fi
    done
  fi
  printf '%s' "$d"
}

st_fx() { # <file> <text, printf %b>: a file of the case's play:<status> outcome (the stub's run-test)
  printf '%b' "$2" >"$ST_CASE/fx/$1" || st_bad "cannot write fx/$1"
}

st_r5_test() { # <name> <entry>: tests/<name>.v from stdin, listed in tests/_CoqProject, its row fixed by fix a
  { cat >"$ST_REPO/tests/$1.v" && printf '%s.v\n' "$1" >>"$ST_REPO/tests/_CoqProject" &&
    st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" \
      "$(st_tsv "tests/$1.v" F9 "$2" - fixed "$ST_FIX_A" -)" >"$ST_REPO/$INVENTORY"; } || st_bad "cannot write tests/$1.v"
  st_commit "test $1"
}

st_chk_test() { # <name> <base_entry> <own_entry> <listed|unlisted|none>: tests/<name>.v from stdin, listed in
  # tests/_CoqProject, its row fixed by fix a, and a stand-in tests/Makefile: with "listed" its ROCQCHK_TESTS names the
  # test on a line that continues the assignment, before a comment; with "unlisted" it names a longer name only, and
  # a commented-out line names the test; with "none" there is no tests/Makefile
  local mk=$ST_REPO/tests/Makefile
  { cat >"$ST_REPO/tests/$1.v" && printf '%s.v\n' "$1" >>"$ST_REPO/tests/_CoqProject" &&
    st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" \
      "$(st_tsv "tests/$1.v" F10 "$2" "$3" fixed "$ST_FIX_A" -)" >"$ST_REPO/$INVENTORY"; } || st_bad "cannot write tests/$1.v"
  case $4 in
    listed) printf 'EXPECT_TESTS := %s\nROCQCHK_TESTS := other_a \\\n  other_b %s # the test\n' "$1" "$1" >"$mk" ;;
    unlisted) printf 'ROCQCHK_TESTS := other_a \\\n  %s_x\n# ROCQCHK_TESTS += %s\n' "$1" "$1" >"$mk" ;;
    none) rm -f -- "$mk" ;;
  esac || st_bad "cannot write $mk"
  st_commit "check test $1"
}

st_commit() { st_git_commit "$ST_REPO" "$1" >/dev/null || st_bad "cannot commit: $1"; }

st_redirect_test() { # <names...>: tests/lean434_a.v imports under one Redirect per name, in that order
  local n
  for n in "$@"; do printf 'Redirect "%s" Lean Import "../dumps/small.ndjson".\n' "$n"; done >"$ST_REPO/tests/lean434_a.v"
}

st_run() { # [VAR=value...] -- [script args...]: run the case's copy of the script with the stubs
  local -a envs=()
  while (($#)) && [[ $1 != -- ]]; do
    envs+=("$1")
    shift
  done
  shift
  (
    cd -- "$ST_REPO" &&
      exec env CUT_SELF_TEST_STUBS=1 CUT_ROOT="$ST_CASE/cut" TMPDIR="$ST_CASE/tmp" \
        PATH="$ST_CASE/caller/opam/cut/bin:$PATH" \
        CUT_STUB_RUN_TEST="$ST_ROOT/stubs/run-test" CUT_STUB_ULIMIT="$ST_ROOT/stubs/ulimit" \
        CUT_STUB_UNAME_R="$ST_ROOT/stubs/uname" CUT_STUB_COMPILE="$ST_ROOT/stubs/compile" \
        CUT_STUB_CHECK="$ST_ROOT/stubs/check" ST_CALLS="$ST_CASE/calls" ST_OUTCOME=pass \
        ST_OUTCOME_HEAD=pass ST_OUTCOME_PARENT=pass ST_SOFT= ST_SOFT_HEAD= ST_SOFT_PARENT= \
        ST_DEFAULT_SOFT=8192 ST_HARD=unlimited ST_UNAME=generic ST_FX="$ST_CASE/fx" "${envs[@]}" \
        bash "$ST_REPO/$SCRIPT_REL" "$@"
  ) >"$ST_CASE/out" 2>"$ST_CASE/err" </dev/null
  ST_RC=$?
}

st_revert() { # <parent outcome> <test> [VAR=value...]: head passes unless overridden
  local outcome=$1 test=$2
  shift 2
  st_run "ST_OUTCOME_PARENT=$outcome" "$@" -- --revert-fix "$test"
}

st_bad() { if [[ -z $ST_WHY ]]; then ST_WHY="$ST_LABEL: $*"; fi; }

st_rc() { # zero | nonzero | <status>
  case $1 in
    zero) ((ST_RC == 0)) ;;
    nonzero) ((ST_RC != 0)) ;;
    *) ((ST_RC == $1)) ;;
  esac || st_bad "exit status $ST_RC, expected $1"
}

st_has() { grep -qF -e "$1" -- "$ST_CASE/out" "$ST_CASE/err" || st_bad "no output line contains '$1'"; }
st_lacks() { ! grep -qF -e "$1" -- "$ST_CASE/out" "$ST_CASE/err" || st_bad "the output contains '$1'"; }
st_line() { grep -qxF -e "$1" -- "$ST_CASE/out" "$ST_CASE/err" || st_bad "no output line is '$1'"; }
st_count() { # <exact line> <n>
  local got
  got=$(cat -- "$ST_CASE/out" "$ST_CASE/err" | grep -cxF -e "$1")
  [[ $got == "$2" ]] || st_bad "'$1' printed $got times, expected $2"
}
st_ran() { grep -q "^$1"$'\t' -- "$ST_CASE/calls" || st_bad "no test command ran as '$1'"; }
st_not_ran() { [[ ! -s $ST_CASE/calls ]] || st_bad "a test command ran: $(head -n 1 -- "$ST_CASE/calls")"; }
st_file_is() { [[ -f $1 && $(<"$1") == "$2" ]] || st_bad "$1 does not hold exactly: $2"; }
st_call_field() { # <field number> [call number]: that field of the recorded call (the first by default)
  local -a fields
  local n=0
  while IFS=$'\t' read -r -a fields; do
    if ((++n == ${2:-1})); then
      printf '%s' "${fields[$1 - 1]:-}"
      break
    fi
  done <"$ST_CASE/calls"
}

# Check each call's side, requested stack and src/ marker, in order.
st_calls() {
  local kind tree name src tests fixes opam switch side want got=''
  while IFS=$'\t' read -r kind tree name src tests fixes opam switch side want; do
    got+="${got:+; }$side:$want:$src"
  done <"$ST_CASE/calls"
  [[ $got == "$1" ]] || st_bad "calls '$got', expected '$1'"
}

st_two_calls() { # <head want> <parent want> <head marker> <parent marker>
  st_calls "head:$1:$3; parent:$2:$4"
  [[ $(st_call_field 2) != "$(st_call_field 2 2)" && $(st_call_field 2) != "$ST_REPO" &&
    $(st_call_field 2 2) != "$ST_REPO" ]] || st_bad "the sides did not run in separate scratch trees"
  [[ $(st_call_field 5) == 'tests at head' && $(st_call_field 5 2) == 'tests at head' ]] ||
    st_bad "both sides must use the head's tests"
}

st_control_row() { # <commits> <stack> [status]: replace row a
  st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - "${3:-fixed}" "$1" "$2")" \
    "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$INVENTORY"
}

st_stack_fix() { # <parent's stack value|none|absent>: fix the stack, then edit src/ on the head
  if [[ $1 == absent ]]; then
    rm -- "$ST_REPO/$SCRIPT_REL"
  else
    st_set_stack "$ST_REPO/$SCRIPT_REL" "$1"
  fi
  st_commit "set up the stack fix's parent"
  ST_STACK_PARENT=$(git -C "$ST_REPO" rev-parse HEAD)
  if [[ $1 == absent ]]; then cp -- "$SELF" "$ST_REPO/$SCRIPT_REL"; fi
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_commit "fix only the stack"
  ST_STACK_FIX=$(git -C "$ST_REPO" rev-parse HEAD)
  printf 'src after fix\n' >"$ST_REPO/src/marker"
  st_control_row "$ST_STACK_FIX" -
  st_commit "row a and a later source change"
}

st_stack_calls() { # <head want> <parent want>: both sides use the later source
  st_two_calls "$1" "$2" 'src after fix' 'src after fix'
}
st_tree_untouched() { # the caller's repository: clean, HEAD where it was, no worktree, nothing left in TMPDIR
  [[ -z $(git -C "$ST_REPO" status --porcelain) ]] || st_bad "the caller's tree changed"
  [[ $(git -C "$ST_REPO" rev-parse HEAD) == "$1" ]] || st_bad "the caller's HEAD moved"
  [[ $(git -C "$ST_REPO" worktree list --porcelain | grep -c '^worktree ') == 1 ]] || st_bad "a worktree was left behind"
  [[ -z $(ls -A -- "$ST_CASE/tmp") ]] || st_bad "scratch files were left in TMPDIR"
}

st_row() { # <id>: print the row's verdict
  if [[ -z $ST_WHY ]]; then
    printf 'ROW %s PASS\n' "$1"
    ST_PASS=$((ST_PASS + 1))
  else
    printf 'ROW %s FAIL: %s\n' "$1" "$ST_WHY"
    ST_FAIL=$((ST_FAIL + 1))
  fi
  ST_WHY=
}

st_rows() {
  local head v dangling inv=$INVENTORY plain work c
  local stack_head='STACK soft=131072 hard=131072'
  local at_a="src/ of $ST_BASE, $stack_head"
  local stack1='STACK soft=8192 hard=unlimited'

  # S0: a clean tree passes every check and goes on to build and run the suite (SUITE PASS), plain and with
  # --handoff. Its script has no CUT_STACK_KIB line, so the STACK line reads the default soft stack.
  for v in plain --handoff; do
    st_new "S0/$v"
    st_set_stack "$ST_REPO/$SCRIPT_REL" none
    if ! git -C "$ST_REPO" diff --quiet -- "$SCRIPT_REL"; then st_commit "unset CUT_STACK_KIB"; fi
    if [[ $v == plain ]]; then st_run --; else st_run -- --handoff; fi
    st_rc zero
    st_line 'SUITE PASS'
    st_line "ROCQ COMMIT $CUT_ROCQ_COMMIT"
    st_line "$stack1"
    st_lacks 'INVENTORY CHECKS SKIPPED'
    st_ran suite
    [[ $(st_call_field 2) == "$ST_REPO" ]] || st_bad "the suite did not run in the caller's tree"
  done
  st_row S0

  # S1: an open or fixed row whose test tests/_CoqProject does not list fails the checks; no test runs.
  for v in open fixed; do
    st_new "S1/$v"
    printf '(* stand-in *)\n' >"$ST_REPO/tests/lean434_d.v"
    if [[ $v == open ]]; then
      st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_d.v F6 Delta.one - open - -)" >"$ST_REPO/$inv"
    else
      st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_d.v F6 Delta.one - fixed "$ST_FIX_A" -)" >"$ST_REPO/$inv"
    fi
    st_commit "row d"
    st_run --
    st_rc nonzero
    st_has "tests/lean434_d.v: status $v, but tests/_CoqProject does not list it"
    st_not_ran
  done
  st_row S1

  # S1b: a listed row's test checks that its feature's entry is refused, so it runs in the suite too: a listed
  # row whose test tests/_CoqProject does not list fails the checks; no test runs.
  st_new S1b
  sed -i '/^lean434_c\.v$/d' "$ST_REPO/tests/_CoqProject"
  st_commit "unlist c"
  st_run --
  st_rc nonzero
  st_has 'tests/lean434_c.v: status listed, but tests/_CoqProject does not list it'
  st_not_ran
  st_row S1b

  # S2: a tests/lean434_*.v file without a row in the inventory fails the checks; no test runs.
  st_new S2
  printf '(* stand-in *)\n' >"$ST_REPO/tests/lean434_e.v"
  st_commit "test e"
  st_run --
  st_rc nonzero
  st_has "tests/lean434_e.v has no row in $inv"
  st_not_ran
  st_row S2

  # S3: a fixed row naming no commit ("-", or a commits field of blanks, which reads as an empty field), a commit
  # that is not a full hash, a commit that is not an ancestor of HEAD, or a commit that does not exist fails the
  # checks and names the inventory, the row and the cause; no test runs. --revert-fix of that row fails the same
  # way. (S0 is the control: the template's fixed rows pass.)
  dangling=$(git -C "$ST_ROOT/template" commit-tree -m dangling "$ST_BASE^{tree}")
  for v in none blank tab-blank malformed dangling unknown blank-revert; do
    st_new "S3/$v"
    case $v in
      none) c=- ;;
      blank | blank-revert) c='   ' ;;
      tab-blank) c=$' \v ' ;;
      malformed) c=${ST_FIX_A:0:8} ;;
      dangling) c=$dangling ;;
      unknown) c=0123456789abcdef0123456789abcdef01234567 ;;
    esac
    st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - fixed "$c" -)" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
    st_commit "row a: $v"
    if [[ $v == blank-revert ]]; then st_revert fail:Alpha.one tests/lean434_a.v; else st_run --; fi
    st_rc nonzero
    case $v in
      none) st_has "$inv line 2 (tests/lean434_a.v): status fixed, but the row names no commit" ;;
      blank | tab-blank | blank-revert) st_has "$inv line 2 cannot be read (empty commits field): tests/lean434_a.v\\tF1\\tAlpha.one" ;;
      malformed) st_has "$inv line 2 (tests/lean434_a.v): '${ST_FIX_A:0:8}' is not a full commit hash" ;;
      dangling) st_has "$inv line 2 (tests/lean434_a.v): commit $dangling is not an ancestor of HEAD" ;;
      unknown) st_has "$inv line 2 (tests/lean434_a.v): commit 0123456789abcdef0123456789abcdef01234567 is not an ancestor of HEAD" ;;
    esac
    st_lacks 'R5 NEGATIVE MET'
    st_not_ran
  done
  st_row S3

  # S3b: --handoff fails while a row is still open; the plain run of the same tree, the control, passes.
  for v in plain --handoff; do
    st_new "S3b/$v"
    st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - open - -)" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
    st_commit "row a open"
    if [[ $v == plain ]]; then
      st_run --
      st_rc zero
      st_line 'SUITE PASS'
    else
      st_run -- --handoff
      st_rc nonzero
      st_has "--handoff: $inv line 2 (tests/lean434_a.v) is still open"
      st_not_ran
    fi
  done
  st_row S3b

  # S4: a predeclared member (one of each table) without its marker in tests/predeclared.v fails the checks, and
  # so do a table entry that cannot be parsed and a table that cannot be found (failing closed): each failure
  # names the member or the table; no test runs.
  for v in UInt32.size ULift Nat.le; do
    st_new "S4/$v"
    st_predeclared_without "$v" >"$ST_REPO/$PREDECLARED_TEST"
    st_commit "unmark $v"
    st_run --
    st_rc nonzero
    st_has "predeclared member $v (src/lean.ml"
    st_not_ran
  done
  st_new S4/bad-entry
  st_lean_ml bad-entry >"$ST_REPO/src/lean.ml"
  st_commit "bad entry"
  st_run --
  st_rc nonzero
  st_has 'src/lean.ml, get_predeclared_def_any: cannot parse line'
  st_has 'nat_pow_name'
  st_not_ran
  st_new S4/no-table
  st_lean_ml no-table >"$ST_REPO/src/lean.ml"
  st_commit "no table"
  st_run --
  st_rc nonzero
  st_has 'src/lean.ml, get_predeclared_ind_as_def_any: not found'
  st_not_ran
  st_row S4

  # S5: a later commit rewrote the lines of the row's fix commit, so that `git revert` of it would conflict: the
  # control still builds the src/ of the parent of the fix commit, with the head's tests/, and passes at the
  # row's entry; the verdict line names that parent, and the caller's tree is left as it was.
  st_new S5
  printf 'let fix_a = 2\n' >"$ST_REPO/src/fix_a.ml"
  st_commit "change fix a again"
  head=$(git -C "$ST_REPO" rev-parse HEAD)
  st_revert fail:Alpha.one tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_two_calls 131072 131072 'src at head' 'src at base'
  [[ $(st_call_field 6 2) == 'fix_*.ml' ]] || st_bad "src/ is not the parent's of fix a: $(st_call_field 6 2)"
  st_tree_untouched "$head"
  st_row S5

  # S6: --revert-fix fails ("R5 negative not met") when the test passes at the parent's src/, and names it.
  st_new S6
  st_revert pass tests/lean434_a.v
  st_rc nonzero
  st_has "R5 negative not met: the test passes ($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_two_calls 131072 131072 'src at head' 'src at base'
  st_row S6

  # S7: --revert-fix, built from the src/ of the parent of the row's first fix commit, fails when the test fails
  # at another entry than its row names (also a prefix or an extension of the right one, and the base entry where
  # the row names an own entry), when an option test fails elsewhere than its Set line, and when no "Error at
  # line N (for X)" line names an entry; the line names the parent.
  for v in Alpha.two Alpha.on Alpha.one.x; do
    st_new "S7/$v"
    st_revert "fail:$v" tests/lean434_a.v
    st_rc nonzero
    st_has "the test fails at $v, but its row names Alpha.one ($at_a)"
    st_lacks 'R5 NEGATIVE MET'
  done
  st_new S7/own-entry
  st_revert fail:Beta.base tests/lean434_b.v
  st_rc nonzero
  st_has "the test fails at Beta.base, but its row names Beta.own (src/ of $ST_FIX_A, $stack_head)"
  st_lacks 'R5 NEGATIVE MET'
  st_new S7/option
  st_revert fail:Gamma.x tests/lean434_opt.v
  st_rc nonzero
  st_has 'the test fails at Gamma.x, not at its Set line'
  st_has "option:Lean Entry Timeout (src/ of $ST_FIX_B, $stack_head)"
  st_lacks 'R5 NEGATIVE MET'
  st_new S7/no-entry
  st_revert fail-noentry tests/lean434_a.v
  st_rc nonzero
  st_has 'R5 negative not met: the test fails at no "Error at line N (for X)" line'
  st_has "($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_row S7

  # S7b: --revert-fix passes ("R5 NEGATIVE MET ... (src/ of <parent>)") when the test, run in a scratch tree that
  # holds the src/ of the parent of the row's first fix commit and the head's tests/, not in the caller's tree,
  # fails at the entry its row names (base entry, own entry, option, or a name quoted as Lean quotes it); the line
  # names that parent, and the caller's tree is left as it was.
  st_new S7b/base
  head=$(git -C "$ST_REPO" rev-parse HEAD)
  st_revert fail:Alpha.one tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_two_calls 131072 131072 'src at head' 'src at base'
  [[ $(st_call_field 3 2) == lean434_a ]] || st_bad "RUN_TEST did not get the test name lean434_a"
  [[ $(st_call_field 6 2) == 'fix_*.ml' ]] || st_bad "src/ is not the parent's of fix a: $(st_call_field 6 2)"
  [[ $(st_call_field 7 2) == "$ST_CASE/cut/opam" && $(st_call_field 8 2) == cut ]] ||
    st_bad "the test did not run on the cut's switch: OPAMROOT $(st_call_field 7 2), OPAMSWITCH $(st_call_field 8 2)"
  st_tree_untouched "$head"
  st_new S7b/own
  st_revert fail:Beta.own lean434_b
  st_rc zero
  st_line "R5 NEGATIVE MET: lean434_b at Beta.own (src/ of $ST_FIX_A)"
  [[ $(st_call_field 6 2) == fix_a.ml ]] || st_bad "src/ is not the parent's of fix b: $(st_call_field 6 2)"
  st_new S7b/option
  st_revert 'option:Lean Entry Timeout' tests/lean434_opt.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_opt.v at option:Lean Entry Timeout (src/ of $ST_FIX_B)"
  st_new S7b/quoted
  sed -i 's/\tAlpha\.one\t/\t«Alpha».one\t/' "$ST_REPO/tests/lean434_features.txt"
  grep -q '«Alpha».one' "$ST_REPO/tests/lean434_features.txt" || st_bad "the template's row names no Alpha.one to quote"
  st_commit "quote a name component as Lean does"
  st_revert fail:Alpha.one tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_row S7b

  # S7c: a test that imports under Redirect gets the importer's errors in the Redirect's .out file, not in the
  # run's log: --revert-fix reads that file too, and passes when its first entry error is the row's entry.
  st_new S7c
  st_redirect_test lean434_a.log
  st_commit "test a imports under Redirect"
  st_revert redirect:lean434_a.log=Alpha.one tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_lacks 'Error at line 7 (for Alpha.one)'
  st_row S7c

  # S7d: a failure at another entry that only a Redirect's .out file names fails --revert-fix, which names that
  # entry and the parent.
  st_new S7d
  st_redirect_test lean434_a.log
  st_commit "test a imports under Redirect"
  st_revert redirect:lean434_a.log=Alpha.two tests/lean434_a.v
  st_rc nonzero
  st_has "R5 negative not met: the test fails at Alpha.two, but its row names Alpha.one ($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_row S7d

  # S7e: the .out files are read in the order of the test's Redirect lines, not the order they were written: the
  # first names another entry, so --revert-fix fails, although the second names the row's entry.
  st_new S7e
  st_redirect_test lean434_a_1.log lean434_a_2.log
  st_commit "test a imports under two Redirects"
  st_revert 'redirect:lean434_a_2.log=Alpha.one lean434_a_1.log=Alpha.two' tests/lean434_a.v
  st_rc nonzero
  st_has "R5 negative not met: the test fails at Alpha.two, but its row names Alpha.one ($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_row S7e

  # S7f: the run's log is read before the .out files: its entry error, the row's, decides, although the .out file
  # of a Redirect names another entry.
  st_new S7f
  st_redirect_test lean434_a.log
  st_commit "test a imports under Redirect"
  st_revert 'redirect:lean434_a.log=Alpha.two -=Alpha.one' tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_row S7f

  # S7g: a row naming two fix commits, the later one first: its first fix commit is the earlier one in the history
  # of HEAD, and --revert-fix builds the src/ of that commit's parent.
  st_new S7g
  st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - fixed "$ST_FIX_B $ST_FIX_A" -)" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
  st_commit "row a: two fix commits"
  st_revert fail:Alpha.one tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  [[ $(st_call_field 6 2) == 'fix_*.ml' ]] || st_bad "src/ is not the parent's of fix a: $(st_call_field 6 2)"
  st_row S7g

  # S7h: a test whose failure before its fix is a missing binding after a parser refusal says so in r5 lines
  # (r5_lines), and its first entry error (the intentional refusal of line 132) does not decide: the Rocq error at
  # the command right after its "r5 error" line must hold that line's text and the row's entry, and the test's own
  # Redirect log must hold each "r5 log" line and no "r5 log lacks" line. Built from the parent's src/, the test
  # failing that way passes (and names the parent). Each other result fails, with its own line: the test passing
  # (the head's result); the intentional refusal followed by an unrelated error; the error of the prefix test's
  # file at the same line; the error at another line of the test; the successor's refusal in another Redirect's
  # log; a row naming the refused line (the symptom) instead of the binding; and, for the prefix test, the log of
  # a full import, which announces the entry of line 131.
  local p_err='File "./case_p.v", line 6, characters 6-11:\nError: The reference PName was not found in the current\nenvironment.\n\nmake[2]: *** [Makefile.rocq:815: case_p.vo] Error 1\n'
  local p_full='line 131: P.fast\nSkipping: Error at line 132 (for line-132): {"in":32}\nNDJSON parse error at line 132: bad name record\nSkipping: Error at line 133 (for line-133): {"in":33}\nNDJSON parse error at line 133: name id 33 is not the next expected id 32\nDone!\n'
  local p_132='line 131: P.fast\nSkipping: Error at line 132 (for line-132): {"in":32}\nNDJSON parse error at line 132: bad name record\nDone!\n'
  local p_not='R5 negative not met: the test fails, but not as the r5 lines of tests/case_p.v say'
  for v in met pass refusal-then-unrelated unrelated-error other-file other-line other-redirect symptom-row; do
    st_new "S7h/$v"
    if [[ $v == symptom-row ]]; then c='line-133'; else c=PName; fi
    st_r5_test case_p "$c" <<'EOF'
From LeanImport Require Import Lean.
Redirect "case_p.log" Lean Import "../dumps/small.ndjson".
(* r5 log: "case_p.log" line 131: P.fast *)
(* r5 log: "case_p.log" NDJSON parse error at line 133: name id 33 is not the next expected id 32 *)
(* r5 error: The reference PName was not found *)
Check PName.
EOF
    st_fx run.log "$p_err"
    st_fx case_p.log.out "$p_full"
    case $v in
      refusal-then-unrelated)
        st_fx case_p.log.out "$p_132"
        st_fx run.log 'File "./case_p.v", line 6, characters 0-11:\nError: Assertion failed: an unrelated check.\n\n'
        ;;
      unrelated-error) st_fx run.log 'File "./case_p.v", line 6, characters 0-11:\nError: Assertion failed: an unrelated check.\n\n' ;;
      other-file) st_fx run.log "${p_err/case_p.v/case_pp.v}" ;;
      other-line) st_fx run.log "${p_err/line 6,/line 2,}" ;;
      other-redirect) st_fx case_p.log.out "$p_132" && st_fx case_p_other.log.out "$p_full" ;;
    esac
    if [[ $v == pass ]]; then st_revert pass tests/case_p.v; else st_revert play:1 tests/case_p.v; fi
    case $v in
      met)
        st_rc zero
        st_line "R5 NEGATIVE MET: tests/case_p.v at PName (src/ of $ST_BASE)"
        ;;
      pass)
        st_rc nonzero
        st_has "R5 negative not met: the test passes ($at_a)"
        ;;
      *)
        st_rc nonzero
        st_has "$p_not"
        st_has "its row names $c ($at_a)"
        ;;
    esac
    case $v in
      refusal-then-unrelated)
        st_has "case_p.log.out has no line 'NDJSON parse error at line 133: name id 33 is not the next expected id 32'"
        st_has "the Rocq error at tests/case_p.v line 6 does not hold 'The reference PName was not found'"
        ;;
      unrelated-error) st_has "the Rocq error at tests/case_p.v line 6 does not hold 'The reference PName was not found'" ;;
      other-file | other-line) st_has 'no Rocq error at tests/case_p.v line 6' ;;
      other-redirect) st_has "case_p.log.out has no line 'NDJSON parse error at line 133" ;;
      symptom-row) st_has 'the Rocq error at tests/case_p.v line 6 does not name line-133' ;;
    esac
    if [[ $v != met ]]; then st_lacks 'R5 NEGATIVE MET'; fi
    st_two_calls 131072 131072 'src at head' 'src at base'
  done
  for v in prefix-met full-import; do
    st_new "S7h/$v"
    st_r5_test case_pp PName <<'EOF'
Redirect "case_pp.log" Lean Import "../dumps/small.ndjson" 144.
(* r5 log lacks: "case_pp.log" line 131: P.fast *)
(* r5 log: "case_pp.log" NDJSON parse error at line 133: name id 33 is not the next expected id 32 *)

(* r5 error: The reference PName was not found *)
Check PName.
EOF
    st_fx run.log "${p_err//case_p/case_pp}"
    if [[ $v == prefix-met ]]; then st_fx case_pp.log.out "${p_full#line 131: P.fast\\n}"; else st_fx case_pp.log.out "$p_full"; fi
    st_revert play:1 tests/case_pp.v
    if [[ $v == prefix-met ]]; then
      st_rc zero
      st_line "R5 NEGATIVE MET: tests/case_pp.v at PName (src/ of $ST_BASE)"
    else
      st_rc nonzero
      st_has "case_pp.log.out has the line 'line 131: P.fast'"
      st_lacks 'R5 NEGATIVE MET'
    fi
  done
  st_row S7h

  # S7i: a test whose failure before its fix is the kernel's refusal of an entry at one of two imports says so with
  # an "r5 error" line right above that import's Redirect, whose text is the diagnostic that only that import
  # gives (here the unqualified constructor). It passes when that import's Rocq error holds the text and the row's
  # entry; the same entry refused at the first import, the diagnostic of the other test (the constructor qualified
  # by the library it loaded), the entry's refusal with another constructor (the common part alone), and the
  # diagnostic naming another entry each fail.
  local s_err='File "./case_s.v", line 3, characters 0-60:\nError:\nError at line 214 (for S.pair_eq): {"thm":1}\nThe term "eq_refl S_pair" has type "S_pair = S_pair"\nwhile it is expected to have type\n "S_pair =\n  List_cons String\n    (String_mk\n       (List_nil Char))".\n\nmake[2]: *** [Makefile.rocq:815: case_s.vo] Error 1\n'
  for v in met first-import qualified other-constructor other-entry; do
    st_new "S7i/$v"
    st_r5_test case_s S.pair_eq <<'EOF'
Redirect "case_s_old.log" Lean Import "../dumps/small.ndjson".
(* r5 error: S_pair = List_cons String (String_mk *)
Redirect "case_s_new.log" Lean Import "../dumps/small.ndjson".
EOF
    case $v in
      met) st_fx run.log "$s_err" ;;
      first-import) st_fx run.log "${s_err/line 3,/line 1,}" ;;
      qualified) st_fx run.log "${s_err/List_cons String\\n    (String_mk/saved.List_cons saved.String\\n    (saved.String_mk}" ;;
      other-constructor) st_fx run.log "${s_err/String_mk/String_ofList}" ;;
      other-entry) st_fx run.log "${s_err/S.pair_eq/S.other_eq}" ;;
    esac
    st_revert play:1 tests/case_s.v
    if [[ $v == met ]]; then
      st_rc zero
      st_line "R5 NEGATIVE MET: tests/case_s.v at S.pair_eq (src/ of $ST_BASE)"
    else
      st_rc nonzero
      st_has 'R5 negative not met: the test fails, but not as the r5 lines of tests/case_s.v say'
      st_lacks 'R5 NEGATIVE MET'
    fi
    case $v in
      first-import) st_has 'no Rocq error at tests/case_s.v line 3' ;;
      qualified | other-constructor) st_has "the Rocq error at tests/case_s.v line 3 does not hold 'S_pair = List_cons String (String_mk'" ;;
      other-entry) st_has 'the Rocq error at tests/case_s.v line 3 does not name S.pair_eq' ;;
    esac
  done
  st_row S7i

  # S7j: a test whose failure before its fix is an assertion of its .expect file after a successful compile says so
  # with an "r5 assertion" line: the run's log must hold that assertion's failure on the named Redirect's log
  # ("unexpected '<text>'"), the log must hold a line starting with the text, and the text must name the row's
  # entry, or some line of the log starting with the text must come right after a refusal header of exactly that
  # entry (st_r5_header_rows). Another assertion's failure, the failure on another Redirect's log, the failure with
  # no such line in the log (or no log), and a failed run with no assertion failure each fail.
  local u_run="EXPECT FAIL: tests/case_u.expect:7: case_u.log.out: unexpected 'Skipping duplicate declaration for UInt32'\nEXPECT FAIL: tests/case_u.expect:8: case_u.log.out: missing 'Skipping scheme'\n"
  local u_log='Fin is predeclared\nSkipping duplicate declaration for UInt32 (already declared earlier in the export).\nline 20: RLIP.x\nDone!\n'
  for v in met other-assertion other-redirect no-log-line no-log no-assertion; do
    st_new "S7j/$v"
    st_r5_test case_u UInt32 <<'EOF'
(* r5 assertion: "case_u.log" Skipping duplicate declaration for UInt32 *)
Redirect "case_u.log" Lean Import "../dumps/small.ndjson".
EOF
    st_fx run.log "$u_run"
    st_fx case_u.log.out "$u_log"
    case $v in
      other-assertion) st_fx run.log "EXPECT FAIL: tests/case_u.expect:8: case_u.log.out: missing 'Skipping scheme'\n" ;;
      other-redirect) st_fx run.log "${u_run//case_u.log.out/case_u2.log.out}" ;;
      no-log-line) st_fx case_u.log.out 'Fin is predeclared\nline 20: RLIP.x\nDone!\n' ;;
      no-log) rm -f -- "$ST_CASE/fx/case_u.log.out" ;;
      no-assertion) st_fx run.log 'make: *** [Makefile:9: submake] Error 2\n' ;;
    esac
    st_revert play:1 tests/case_u.v
    if [[ $v == met ]]; then
      st_rc zero
      st_line "R5 NEGATIVE MET: tests/case_u.v at UInt32 (src/ of $ST_BASE)"
    else
      st_rc nonzero
      st_has 'R5 negative not met: the test fails, but not as the r5 lines of tests/case_u.v say'
      st_lacks 'R5 NEGATIVE MET'
    fi
    case $v in
      other-assertion | other-redirect | no-assertion)
        st_has "the run's log has no line \"EXPECT FAIL: tests/case_u.expect:<n>: case_u.log.out: unexpected 'Skipping duplicate declaration for UInt32'\""
        ;;
      no-log-line) st_has "case_u.log.out has no line starting 'Skipping duplicate declaration for UInt32'" ;;
      no-log) st_has 'case_u.log.out does not exist' ;;
    esac
  done
  st_row S7j

  # S7k: r5 lines that cannot be read fail --revert-fix before the test runs: an unknown kind, an "r5 error" line
  # with no command right after it, a line naming a Redirect the test does not have, two error lines, a test with
  # only "r5 log" lines, and r5 lines on an option row.
  local m_lines
  for v in kind no-command no-redirect two-verdicts log-only option-row; do
    st_new "S7k/$v"
    case $v in
      kind) m_lines=$(printf '%s\n' 'Redirect "case_m.log" Lean Import "x".' '(* r5 maybe: "case_m.log" x *)' '(* r5 error: The reference M was not found *)' 'Check M.') ;;
      no-command) m_lines=$(printf '%s\n' 'Redirect "case_m.log" Lean Import "x".' '(* r5 error: The reference M was not found *)' '(* a comment *)' 'Check M.') ;;
      no-redirect) m_lines=$(printf '%s\n' 'Redirect "case_m.log" Lean Import "x".' '(* r5 log: "nosuch.log" x *)' '(* r5 error: The reference M was not found *)' 'Check M.') ;;
      two-verdicts) m_lines=$(printf '%s\n' 'Redirect "case_m.log" Lean Import "x".' '(* r5 error: The reference M was not found *)' 'Check M.' '(* r5 error: The reference N was not found *)' 'Check N.') ;;
      log-only) m_lines=$(printf '%s\n' 'Redirect "case_m.log" Lean Import "x".' '(* r5 log: "case_m.log" x *)') ;;
      option-row) m_lines=$(printf '%s\n' 'Redirect "case_m.log" Lean Import "x".' '(* r5 error: The reference M was not found *)' 'Check M.') ;;
    esac
    if [[ $v == option-row ]]; then c='option:Lean Entry Timeout'; else c=M; fi
    st_r5_test case_m "$c" <<<"$m_lines"
    st_revert fail:M tests/case_m.v
    st_rc nonzero
    case $v in
      kind) st_has 'tests/case_m.v line 2: an r5 line of no known kind: (* r5 maybe: "case_m.log" x *)' ;;
      no-command) st_has 'tests/case_m.v line 2: no command right after this r5 error line' ;;
      no-redirect) st_has 'tests/case_m.v line 2: no Redirect "nosuch.log" in the test' ;;
      two-verdicts) st_has 'tests/case_m.v has 2 r5 error or assertion lines; it needs exactly one' ;;
      log-only) st_has 'tests/case_m.v has 0 r5 error or assertion lines; it needs exactly one' ;;
      option-row) st_has 'an option row is decided at its Set line, but tests/case_m.v has r5 lines' ;;
    esac
    st_lacks 'R5 NEGATIVE MET'
    st_not_ran
  done
  st_row S7k

  # S7m: an "r5 assertion" line whose text holds a ' or a \ is met by the failure tests/check_expect.py itself prints:
  # the stub's expect outcome runs the check_expect.py of the tree on the parent side's log, and its line
  # "unexpected '<text>'" holds the text as it is, between plain single quotes, as expect_failure_seen reads it.
  local q entry
  for v in quote backslash; do
    st_new "S7m/$v"
    if [[ $v == quote ]]; then entry="Q.mk'" q="Q.mk' cannot be declared"; else entry=Q.mk q='Q.mk reads C:\lean\x'; fi
    printf 'case_q.log.out\t-\t%s\n' "$q" >"$ST_REPO/tests/case_q.expect"
    st_r5_test case_q "$entry" <<<"(* r5 assertion: \"case_q.log\" $q *)"$'\n''Redirect "case_q.log" Lean Import "../dumps/small.ndjson".'
    printf 'line 7: %s\n%s\nDone!\n' "$entry" "$q" >"$ST_CASE/fx/case_q.log.out"
    st_revert expect tests/case_q.v
    st_rc zero
    st_line "EXPECT FAIL: tests/case_q.expect:1: case_q.log.out: unexpected '$q'"
    st_line "R5 NEGATIVE MET: tests/case_q.v at $entry (src/ of $ST_BASE)"
  done
  st_row S7m

  # S7n: a commented-out Redirect is no Redirect for any reader of REDIRECT_RE: --revert-fix does not read the log a
  # commented-out Redirect would write (redirect_logs), a planted line followed only by a commented-out Redirect has
  # no case (planted_cases), and an r5 line that names only a commented-out Redirect is bad (r5_lines).
  st_new S7n/redirect-logs
  printf '%s\n' '(* Redirect "lean434_a_old.log" Lean Import "../dumps/small.ndjson". *)' \
    'Redirect "lean434_a.log" Lean Import "../dumps/small.ndjson".' >"$ST_REPO/tests/lean434_a.v"
  st_commit "test a: a commented-out Redirect before its own"
  st_revert 'redirect:lean434_a_old.log=Alpha.two lean434_a.log=Alpha.one' tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_new S7n/planted
  printf '%s\n' '(* planted: Planted.hidden *)' '(* Redirect "planted_hidden.log" Lean Import "../dumps/small.ndjson". *)' \
    >>"$ST_REPO/tests/planted_sa.v"
  st_commit "a planted line followed only by a commented-out Redirect"
  st_run ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 3
  st_has 'SOURCE-AT ERROR: tests/planted_sa.v line 18: no Redirect after the planted line of Planted.hidden'
  st_not_ran
  st_new S7n/r5
  st_r5_test case_n N <<<"$(printf '%s\n' '(* Redirect "case_n.log" Lean Import "x". *)' '(* r5 log: "case_n.log" x *)' \
    '(* r5 error: The reference N was not found *)' 'Check N.')"
  st_revert fail:N tests/case_n.v
  st_rc nonzero
  st_has 'tests/case_n.v line 2: no Redirect "case_n.log" in the test'
  st_not_ran
  st_row S7n

  # S7o: a row whose entry is check:rocqchk (both columns) is decided by the rocqchk step of tests/Makefile:
  # --revert-fix passes when the head side passes and the parent side's log has the line "ROCQCHK FAIL:
  # tests/<name>.vo: ..." that the step prints for the test, and names the parent; it fails when the parent side
  # passes, when it fails at an entry with no such line, when the line is another test's, and when the head side
  # fails; r5 lines in the test of a check row fail it before the test runs.
  for v in met pass entry other-vo head r5; do
    st_new "S7o/$v"
    if [[ $v == r5 ]]; then
      st_chk_test case_k check:rocqchk check:rocqchk listed <<<"$(printf '%s\n' 'Redirect "case_k.log" Lean Import "x".' \
        '(* r5 error: The reference K was not found *)' 'Check K.')"
    else
      st_chk_test case_k check:rocqchk check:rocqchk listed <<<'(* stand-in test case_k *)'
    fi
    head=$(git -C "$ST_REPO" rev-parse HEAD)
    case $v in
      met | r5) st_revert rocqchk:case_k tests/case_k.v ;;
      pass) st_revert pass tests/case_k.v ;;
      entry) st_revert fail:K.one tests/case_k.v ;;
      other-vo) st_revert rocqchk:case_kk tests/case_k.v ;;
      head) st_revert rocqchk:case_k tests/case_k.v ST_OUTCOME_HEAD=rocqchk:case_k ;;
    esac
    case $v in
      met)
        st_rc zero
        st_line "R5 NEGATIVE MET: tests/case_k.v at check:rocqchk (src/ of $ST_BASE)"
        st_two_calls 131072 131072 'src at head' 'src at base'
        st_tree_untouched "$head"
        ;;
      pass)
        st_rc nonzero
        st_has "R5 negative not met: the test passes ($at_a)"
        ;;
      entry)
        st_rc nonzero
        st_has 'R5 negative not met: the test fails at K.one, not at the rocqchk step of tests/Makefile'
        st_has "its row names check:rocqchk ($at_a)"
        ;;
      other-vo)
        st_rc nonzero
        st_has "not at the rocqchk step of tests/Makefile (no line 'ROCQCHK FAIL: tests/case_k.vo: ...' in its log)"
        ;;
      head)
        st_rc 1
        st_has "R5 negative not met: the head side fails at check:rocqchk (src/ of $head, $stack_head)"
        st_calls 'head:131072:src at head'
        ;;
      r5)
        st_rc nonzero
        st_has 'a check row is decided by the rocqchk step of tests/Makefile, but tests/case_k.v has r5 lines'
        st_not_ran
        ;;
    esac
    if [[ $v != met ]]; then st_lacks 'R5 NEGATIVE MET'; fi
  done
  st_row S7o

  st_r5_header_rows

  # S8: --revert-fix of a test with no row fails; each mode with no argument or one short prints the usage and
  # exits 2; no test runs.
  st_new S8/no-row
  st_run -- --revert-fix tests/lean434_zz.v
  st_rc nonzero
  st_has "has no row for tests/lean434_zz.v"
  st_not_ran
  for v in --revert-fix --import --check --source-at "--source-at $ST_BASE" '--import -- -Q a b'; do
    st_new "S8/$v"
    # shellcheck disable=SC2086 # the words of $v are the arguments
    st_run -- $v
    st_rc 2
    st_has 'Usage:'
    st_not_ran
  done
  st_row S8

  # S9: a switch whose Rocq is not the cut fails; no test runs.
  st_new S9
  printf '%s\n' "$ST_OTHER_SHA" >"$ST_CASE/cut/rocq-commit"
  st_run --
  st_rc nonzero
  st_has "the switch's Rocq is commit $ST_OTHER_SHA, not the cut $CUT_ROCQ_COMMIT"
  st_not_ran
  st_row S9

  # S9b: a switch whose Rocq commit cannot be read (missing, empty, not a file) is a build that did not finish,
  # since build_switch writes that file once the switch is complete: the script builds the switch again (the
  # self-test never builds one, so it fails there and names the unfinished switch), and --import, which never
  # builds one, fails and says to unpack the root. The cut is never assumed; no test runs.
  local unfinished
  for v in missing empty directory import; do
    st_new "S9b/$v"
    unfinished="the switch at $ST_CASE/cut/opam/cut is unfinished: $ST_CASE/cut/rocq-commit is missing, unreadable or empty"
    rm -f -- "$ST_CASE/cut/rocq-commit"
    case $v in
      empty) : >"$ST_CASE/cut/rocq-commit" ;;
      directory) mkdir -- "$ST_CASE/cut/rocq-commit" ;;
    esac
    if [[ $v == import ]]; then
      work=$ST_CASE/work
      mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v"
      st_run -- --import "$work/Import.v"
      st_has "$unfinished; unpack the packed opam root at $ST_CASE/cut first"
      [[ ! -e $work/Import.v.stack ]] || st_bad "a .stack file was written"
    else
      st_run --
      st_has "$unfinished, and the self-test never builds one"
    fi
    st_rc nonzero
    st_lacks "ROCQ COMMIT $CUT_ROCQ_COMMIT"
    st_not_ran
  done
  st_row S9b

  # S10: with the inventory missing or empty, at a head without tests/lean434_*.v, the checks are skipped (with
  # a notice) and the suite runs.
  for v in missing empty; do
    st_new "S10/$v"
    rm -f -- "$ST_REPO"/tests/lean434_*.v
    if [[ $v == missing ]]; then rm -f -- "$ST_REPO/$inv"; else : >"$ST_REPO/$inv"; fi
    st_commit "no inventory"
    st_run --
    st_rc zero
    st_has 'INVENTORY CHECKS SKIPPED'
    st_line 'SUITE PASS'
    st_ran suite
  done
  st_row S10

  # S11: with the inventory missing or empty, at a head with tests/lean434_*.v files, the checks fail and name
  # those files; no test runs.
  for v in missing empty; do
    st_new "S11/$v"
    if [[ $v == missing ]]; then rm -f -- "$ST_REPO/$inv"; else : >"$ST_REPO/$inv"; fi
    st_commit "no inventory"
    st_run --
    st_rc nonzero
    st_has "$inv is $v, but the head has tests/lean434_*.v files"
    st_has 'tests/lean434_a.v'
    st_not_ran
  done
  st_row S11

  # S12: a row that cannot be read (five fields, an unknown status, an empty file field) fails the checks and
  # names its line; no test runs.
  for v in fields status file; do
    st_new "S12/$v"
    case $v in
      fields) st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_x.v F7 X.one - open)" >"$ST_REPO/$inv" ;;
      status) st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_x.v F7 X.one - 'done' - -)" >"$ST_REPO/$inv" ;;
      file) st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv '' F7 X.one - listed - -)" >"$ST_REPO/$inv" ;;
    esac
    st_commit "bad row: $v"
    st_run --
    st_rc nonzero
    st_has "$inv line 6 cannot be read"
    case $v in
      fields) st_has '5 fields, not 7' ;;
      status) st_has 'unknown status done' ;;
      file) st_has 'empty file field' ;;
    esac
    st_not_ran
  done
  st_row S12

  # S12b: an entry "check:<kind>" other than check:rocqchk, in either entry column, fails the inventory checks and
  # names its line and the kind; so does a check:rocqchk row whose test ROCQCHK_TESTS of tests/Makefile does not name
  # (a longer name or a commented-out line names it not; a head without tests/Makefile names nothing), plain and
  # with --handoff; no test runs. A check:rocqchk row whose test the assignment names on a continued line, before a
  # comment, passes the checks, and the suite runs.
  for v in unknown-own unknown-base unlisted unlisted-handoff no-makefile listed; do
    st_new "S12b/$v"
    case $v in
      unknown-own) st_chk_test case_k check:rocqchk check:rocqchck listed ;;
      unknown-base) st_chk_test case_k check:lint - listed ;;
      unlisted | unlisted-handoff) st_chk_test case_k check:rocqchk check:rocqchk unlisted ;;
      no-makefile) st_chk_test case_k check:rocqchk check:rocqchk none ;;
      listed) st_chk_test case_k check:rocqchk check:rocqchk listed ;;
    esac <<<'(* stand-in test case_k *)'
    if [[ $v == unlisted-handoff ]]; then st_run -- --handoff; else st_run --; fi
    if [[ $v == listed ]]; then
      st_rc zero
      st_line 'SUITE PASS'
      st_ran suite
    else
      st_rc nonzero
      st_not_ran
    fi
    case $v in
      unknown-own)
        st_has "$inv line 6 (tests/case_k.v): unknown entry kind 'check:rocqchck'; the one check kind is check:rocqchk"
        st_lacks 'does not name case_k'
        ;;
      unknown-base) st_has "$inv line 6 (tests/case_k.v): unknown entry kind 'check:lint'" ;;
      unlisted | unlisted-handoff | no-makefile)
        st_has "$inv line 6 (tests/case_k.v): entry check:rocqchk, but ROCQCHK_TESTS of tests/Makefile does not name case_k, so the suite runs no rocqchk on tests/case_k.vo"
        ;;
    esac
  done
  st_row S12b

  # S13: tests/predeclared.v missing at a head with the inventory fails the checks; without the inventory the
  # checks, S4's among them, are skipped and the suite runs.
  st_new S13/with-inventory
  rm -f -- "$ST_REPO/$PREDECLARED_TEST"
  st_commit "no predeclared.v"
  st_run --
  st_rc nonzero
  st_has "$PREDECLARED_TEST is missing"
  st_not_ran
  st_new S13/without-inventory
  rm -f -- "$ST_REPO/$PREDECLARED_TEST" "$ST_REPO/$inv" "$ST_REPO"/tests/lean434_*.v
  st_commit "no predeclared.v, no inventory"
  st_run --
  st_rc zero
  st_has 'INVENTORY CHECKS SKIPPED'
  st_line 'SUITE PASS'
  st_row S13

  # S14: --revert-fix fails, and says the plugin build failed at the parent's src/, when that build fails.
  st_new S14
  st_revert build-fail tests/lean434_a.v
  st_rc nonzero
  st_has "the parent side's plugin build failed ($at_a)"
  st_has 'Error: Unbound value planted_build_error'
  st_lacks 'R5 NEGATIVE MET'
  st_row S14

  # S15: --revert-fix of an open row fails: an open row names no fix to revert; no test runs.
  st_new S15
  st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - open - -)" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
  st_commit "row a open"
  st_run -- --revert-fix tests/lean434_a.v
  st_rc nonzero
  st_has "$inv line 2 (tests/lean434_a.v) is open"
  st_not_ran
  st_row S15

  # S16: --revert-fix of a listed row succeeds without running the test, and says it skipped it.
  st_new S16
  st_revert fail:Gamma.one tests/lean434_c.v
  st_rc zero
  st_line 'SKIPPED, LISTED: tests/lean434_c.v'
  st_lacks 'R5 NEGATIVE MET'
  st_not_ran
  st_row S16

  # S17: CUT_STACK_KIB unset (each case first removes the line from its copy of the script): the default soft stack
  # is read back into one STACK line, on stderr before the test, or in <input>.stack (with the Rocq commit, nothing
  # else printed) for --import and --check; an unlimited default soft stack fails.
  st_new S17/suite
  st_set_stack "$ST_REPO/$SCRIPT_REL" none
  st_run --
  st_rc zero
  st_count "$stack1" 1
  grep -qxF -e "$stack1" -- "$ST_CASE/err" || st_bad "the STACK line is not on stderr"
  [[ $(grep -nxF -e "$stack1" -- "$ST_CASE/err" | cut -d: -f1) -lt $(grep -nF 'STUB RUN-TEST' -- "$ST_CASE/err" | cut -d: -f1) ]] ||
    st_bad "the STACK line does not come before the test run"
  st_new S17/import
  st_set_stack "$ST_REPO/$SCRIPT_REL" none
  work=$ST_CASE/work
  mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v"
  st_run -- --import "$work/Import.v"
  st_rc zero
  st_file_is "$work/Import.v.stack" "$stack1"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_file_is "$ST_CASE/out" 'stub compile stdout'
  st_file_is "$ST_CASE/err" 'stub compile stderr'
  st_new S17/check
  st_set_stack "$ST_REPO/$SCRIPT_REL" none
  work=$ST_CASE/work
  mkdir -p -- "$work" && : >"$work/Import.vo" && : >"$work/Other.vo"
  st_run -- --check "$work/Import.vo" "$work/Other.vo"
  st_rc zero
  st_file_is "$work/Import.vo.stack" "$stack1"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  [[ ! -e $work/Other.vo.stack ]] || st_bad "a .stack file was written for the second file"
  st_file_is "$ST_CASE/out" 'stub check stdout'
  st_file_is "$ST_CASE/err" 'stub check stderr'
  st_new S17/unlimited
  st_set_stack "$ST_REPO/$SCRIPT_REL" none
  st_run ST_DEFAULT_SOFT=unlimited --
  st_rc nonzero
  st_has 'the default soft stack is unlimited'
  st_not_ran
  st_new S17/unlimited-import
  st_set_stack "$ST_REPO/$SCRIPT_REL" none
  work=$ST_CASE/work
  mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v"
  st_run ST_DEFAULT_SOFT=unlimited -- --import "$work/Import.v"
  st_rc nonzero
  st_has 'the default soft stack is unlimited'
  [[ ! -e $work/Import.v.stack ]] || st_bad "a .stack file was written"
  st_not_ran
  st_row S17

  # S18: CUT_STACK_KIB at or below the hard limit (the hard limit itself included) is asked for, read back and
  # reported, for the suite, --import and --check. The read-back stub replaces the setter, stack_apply, which then
  # does nothing; the stub reports the soft stack asked for and, for an unlimited hard limit, a hard limit lowered
  # to it, as stack_apply sets them.
  st_new S18/suite
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run --
  st_rc zero
  st_count 'STACK soft=65536 hard=65536' 1
  st_ran suite
  st_new S18/at-hard-limit
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run ST_HARD=65536 --
  st_rc zero
  st_line 'STACK soft=65536 hard=65536'
  st_ran suite
  st_new S18/import
  work=$ST_CASE/work
  mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v"
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run -- --import "$work/Import.v"
  st_rc zero
  st_file_is "$work/Import.v.stack" "STACK soft=65536 hard=65536"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_new S18/check
  work=$ST_CASE/work
  mkdir -p -- "$work" && : >"$work/Import.vo"
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run -- --check "$work/Import.vo"
  st_rc zero
  st_file_is "$work/Import.vo.stack" "STACK soft=65536 hard=65536"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_row S18

  # S18b: the script as committed, its copy unedited, sets its own CUT_STACK_KIB of 131072 KiB: with the hard limit
  # unlimited, the soft and hard stacks read back as 131072, under gVisor and elsewhere, and the suite runs.
  for v in generic gvisor; do
    st_new "S18b/$v"
    st_run "ST_UNAME=$v" --
    st_rc zero
    st_count 'STACK soft=131072 hard=131072' 1
    st_ran suite
  done
  st_row S18b

  # S19: CUT_STACK_KIB empty, 0, negative, unlimited or not an integer fails; no test runs.
  for v in '' 0 -5 unlimited abc 12x; do
    st_new "S19/'$v'"
    st_set_stack "$ST_REPO/$SCRIPT_REL" "$v"
    st_run --
    st_rc nonzero
    st_has "CUT_STACK_KIB='$v' is not a positive whole number of KiB"
    st_not_ran
  done
  st_row S19

  # S20: CUT_STACK_KIB above the hard limit fails; no test runs.
  st_new S20
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65537
  st_run ST_HARD=65536 --
  st_rc nonzero
  st_has 'CUT_STACK_KIB=65537 is above the hard stack limit of 65536 KiB'
  st_not_ran
  st_row S20

  # S20b: CUT_STACK_KIB above 131072 KiB fails under gVisor, or when uname -r fails or prints nothing; 131071 and
  # 131072 run under gVisor, and 131073 runs elsewhere.
  for v in gvisor fail empty; do
    st_new "S20b/131073-$v"
    st_set_stack "$ST_REPO/$SCRIPT_REL" 131073
    st_run "ST_UNAME=$v" --
    st_rc nonzero
    st_has 'CUT_STACK_KIB=131073 is above 131072 KiB, and gVisor caps the stack at 128 MiB'
    st_not_ran
  done
  for v in 131071 131072; do
    st_new "S20b/$v-gvisor"
    st_set_stack "$ST_REPO/$SCRIPT_REL" "$v"
    st_run ST_UNAME=gvisor --
    st_rc zero
    st_line "STACK soft=$v hard=$v"
    st_ran suite
  done
  st_new S20b/131073-generic
  st_set_stack "$ST_REPO/$SCRIPT_REL" 131073
  st_run ST_UNAME=generic --
  st_rc zero
  st_line 'STACK soft=131073 hard=131073'
  st_row S20b

  # S21: a soft stack read back that differs from CUT_STACK_KIB fails; no test runs.
  st_new S21
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run ST_SOFT=8192 --
  st_rc nonzero
  st_has 'the soft stack read back is 8192 KiB, not CUT_STACK_KIB=65536'
  st_not_ran
  st_row S21

  st_revert_rows

  # S23: --import and --check on a tree without history and with a broken inventory: a missing file, a
  # failing run, a normal run, the stack rules (its script holds no CUT_STACK_KIB line, then a bad one); no
  # inventory check.
  st_new S23/setup
  plain=$ST_CASE/plain work=$ST_CASE/work
  cp -a -- "$ST_REPO" "$plain" && rm -rf -- "$plain/.git"
  st_set_stack "$plain/$SCRIPT_REL" none
  printf 'not a row\n' >>"$plain/$inv"
  mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v" && : >"$work/Import.vo" && : >"$work/Other.vo"
  ST_REPO=$plain
  st_run -- --import "$work/Missing.v"
  st_rc nonzero
  st_has "--import: no such file: $work/Missing.v"
  st_not_ran
  ST_LABEL=S23/import-fails
  st_run ST_OUTCOME=fail -- --import "$work/Import.v"
  st_rc nonzero
  st_has 'Error: planted compile error'
  ST_LABEL=S23/import
  : >"$ST_CASE/calls"
  st_run -- --import "$work/Import.v" -- -Q /lib Lib
  st_rc zero
  st_file_is "$ST_CASE/out" 'stub compile stdout'
  st_file_is "$ST_CASE/err" 'stub compile stderr'
  st_file_is "$work/Import.v.stack" "$stack1"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  [[ $(st_call_field 2) == "$work" ]] || st_bad "rocq compile did not run in the file's directory"
  [[ $(st_call_field 3) == '-Q /lib Lib Import.v' ]] || st_bad "rocq compile got '$(st_call_field 3)'"
  [[ $(st_call_field 4) == suite && $(st_call_field 5) == - ]] || st_bad "rocq compile did not get the stack request"
  ST_LABEL=S23/check-missing
  : >"$ST_CASE/calls"
  st_run -- --check "$work/Import.vo" "$work/Missing.vo"
  st_rc nonzero
  st_has "--check: no such file: $work/Missing.vo"
  st_not_ran
  ST_LABEL=S23/check-fails
  st_run ST_OUTCOME=fail -- --check "$work/Import.vo"
  st_rc nonzero
  st_has 'Error: planted check error'
  ST_LABEL=S23/check
  : >"$ST_CASE/calls"
  st_run -- --check "$work/Import.vo" "$work/Other.vo" -- -Q /lib Lib
  st_rc zero
  st_file_is "$ST_CASE/out" 'stub check stdout'
  st_file_is "$ST_CASE/err" 'stub check stderr'
  [[ $(st_call_field 3) == "-silent -o -Q /lib Lib $work/Import.vo $work/Other.vo" ]] || st_bad "rocqchk got '$(st_call_field 3)'"
  [[ $(st_call_field 4) == suite && $(st_call_field 5) == - ]] || st_bad "rocqchk did not get the stack request"
  ST_LABEL=S23/import-stack
  : >"$ST_CASE/calls"
  st_set_stack "$plain/$SCRIPT_REL" abc
  st_run -- --import "$work/Import.v"
  st_rc nonzero
  st_has "CUT_STACK_KIB='abc'"
  st_not_ran
  st_row S23

  # S24: --source-at builds from the commit's src/ with the head's tests/, with the toolchain of the caller's PATH:
  # it reports the commit in the rocq-commit file of the root that holds the rocq on PATH (<root>/opam/<switch>/bin,
  # the layout build_switch makes), or unknown when that root has none or rocq is not in such a layout, never the
  # commit of $CUT_ROOT, and it neither builds nor selects the switch there (S9 and S9b do not apply); the test
  # runs with no opam root or switch selected. It prints the test's result and each planted entry that its own
  # case accepted: the case of a planted line is the first Redirect after it, and an entry is accepted there when
  # that Redirect's log announces it ("line N: <entry>"), refuses it nowhere, and says "Done!" after it. A
  # refused entry, the same name accepted in another case only, a longer name, a name in no Redirect's log, an
  # announced entry with no "Done!" after it and a case Rocq never reached are not accepted. Exit = test's.
  local caller_rocq left
  st_new S24/pass
  head=$(git -C "$ST_REPO" rev-parse HEAD)
  caller_rocq=$(readlink -f -- "$ST_CASE/caller/opam/cut/bin/rocq")
  st_run ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 0
  st_line "ROCQ EXECUTABLE $caller_rocq"
  st_line "ROCQ COMMIT $ST_CALLER_SHA"
  st_lacks "ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_line 'SOURCE-AT TEST pass'
  st_line 'SOURCE-AT ACCEPTED Planted.ok in planted_ok.log'
  st_line 'SOURCE-AT ACCEPTED Planted.same in planted_same_b.log'
  [[ $(grep -c '^SOURCE-AT ACCEPTED ' -- "$ST_CASE/out") == 2 ]] || st_bad "not exactly two accepted entries"
  st_line 'SOURCE-AT CASE Planted.err in planted_err.log: refused'
  st_line 'SOURCE-AT CASE Planted.same in planted_same_a.log: refused'
  st_line 'SOURCE-AT CASE Planted.pre in planted_pre.log: unseen'
  st_line 'SOURCE-AT CASE Planted.cut in planted_cut.log: unfinished'
  st_line 'SOURCE-AT CASE Planted.unstarted in planted_unstarted.log: unreached'
  st_line 'SOURCE-AT CASE Planted.cross in planted_cross.log: unreached'
  [[ $(st_call_field 4) == 'src at base' ]] || st_bad "src/ is not the commit's: $(st_call_field 4)"
  [[ $(st_call_field 5) == 'tests at head' ]] || st_bad "tests/ is not the head's: $(st_call_field 5)"
  [[ $(st_call_field 7) == '<unset>' && $(st_call_field 8) == '<unset>' ]] ||
    st_bad "the test ran with an opam root or switch selected: $(st_call_field 7), $(st_call_field 8)"
  st_tree_untouched "$head"
  st_new S24/fail
  st_run ST_OUTCOME=source:2 -- --source-at "$ST_BASE" tests/planted_sa.v
  st_rc 2
  st_line 'SOURCE-AT TEST fail'
  st_line 'SOURCE-AT ACCEPTED Planted.ok in planted_ok.log'
  st_line 'SOURCE-AT ACCEPTED Planted.same in planted_same_b.log'
  [[ $(grep -c '^SOURCE-AT ACCEPTED ' -- "$ST_CASE/out") == 2 ]] || st_bad "not exactly two accepted entries"
  # $CUT_ROOT holds another commit and no switch: the caller's commit is reported, and nothing is built there.
  st_new S24/unrelated-cut-root
  printf '%s\n' "$ST_OTHER_SHA" >"$ST_CASE/cut/rocq-commit"
  rm -rf -- "$ST_CASE/cut/opam"
  st_run ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 0
  st_line "ROCQ COMMIT $ST_CALLER_SHA"
  st_lacks "$ST_OTHER_SHA"
  st_line 'SOURCE-AT TEST pass'
  left=$(find "$ST_CASE/cut" -mindepth 1 -printf '%P\n')
  [[ $left == rocq-commit ]] || st_bad "\$CUT_ROOT changed: ${left//$'\n'/ }"
  # The caller's root has no rocq-commit: unknown, although $CUT_ROOT has one.
  st_new S24/unknown-rocq
  rm -f -- "$ST_CASE/caller/rocq-commit"
  st_run ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 0
  st_line 'ROCQ COMMIT unknown'
  st_lacks "ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_line 'SOURCE-AT TEST pass'
  # The rocq on PATH is not in an opam root's switch: a rocq-commit file beside its bin/ is not its metadata.
  st_new S24/other-layout
  if ! { mkdir -p -- "$ST_CASE/flat/bin" && printf '#!/usr/bin/env bash\nexit 0\n' >"$ST_CASE/flat/bin/rocq" &&
    chmod +x -- "$ST_CASE/flat/bin/rocq" && printf '%s\n' "$ST_OTHER_SHA" >"$ST_CASE/flat/rocq-commit"; }; then
    st_bad "cannot set up the flat toolchain"
  fi
  st_run "PATH=$ST_CASE/flat/bin:$PATH" ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 0
  st_line 'ROCQ COMMIT unknown'
  st_lacks "$ST_OTHER_SHA"
  st_row S24

  # S24b: --source-at of a commit that is not found, of a test not in the head's tests/, of a test with a planted
  # line that no Redirect follows, or with no rocq on PATH, fails with status 3; no test runs.
  for v in 0123456789abcdef0123456789abcdef01234567 no-such-ref; do
    st_new "S24b/$v"
    st_run -- --source-at "$v" planted_sa
    st_rc 3
    st_has "SOURCE-AT ERROR: commit $v not found"
    st_not_ran
  done
  st_new S24b/no-test
  st_run -- --source-at "$ST_BASE" nosuch
  st_rc 3
  st_has "SOURCE-AT ERROR: test tests/nosuch.v is not in the head's tests/"
  st_not_ran
  st_new S24b/no-case
  printf '(* planted: Planted.orphan *)\n' >>"$ST_REPO/tests/planted_sa.v"
  st_commit "a planted line with no Redirect after it"
  st_run ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 3
  st_has 'SOURCE-AT ERROR: tests/planted_sa.v line 18: no Redirect after the planted line of Planted.orphan'
  st_lacks 'SOURCE-AT TEST'
  st_not_ran
  st_new S24b/no-rocq
  st_run "PATH=$(st_norocq_path)" ST_OUTCOME=source:0 -- --source-at "$ST_BASE" planted_sa
  st_rc 3
  st_has 'SOURCE-AT ERROR: no rocq on PATH'
  st_lacks 'SOURCE-AT TEST'
  st_not_ran
  st_row S24b

  # S24c: --source-at exits 4, and reports the build failure, when the plugin build fails at that commit: no test
  # result and no accepted entry.
  st_new S24c
  st_run ST_OUTCOME=build-fail -- --source-at "$ST_BASE" planted_sa
  st_rc 4
  st_has 'SOURCE-AT BUILD FAILED: Error: Unbound value planted_build_error'
  st_lacks 'SOURCE-AT TEST'
  st_lacks 'SOURCE-AT ACCEPTED'
  st_row S24c

  # S24d: --source-at prints the test's line "ROCQCHK FAIL: tests/<name>.vo: ..." of the run's log (the rocqchk step
  # of tests/Makefile refused its .vo) as "SOURCE-AT ROCQCHK FAIL: ...", after the test's result; a run whose log has
  # no such line, or only another test's, prints none. The exit status stays the test's.
  for v in fail other-vo pass; do
    st_new "S24d/$v"
    printf '(* stand-in test case_k *)\n' >"$ST_REPO/tests/case_k.v"
    st_commit "test case_k"
    case $v in
      fail) st_run ST_OUTCOME=rocqchk:case_k -- --source-at "$ST_BASE" case_k ;;
      other-vo) st_run ST_OUTCOME=rocqchk:case_kk -- --source-at "$ST_BASE" tests/case_k.v ;;
      pass) st_run ST_OUTCOME=pass -- --source-at "$ST_BASE" case_k ;;
    esac
    if [[ $v == pass ]]; then
      st_rc 0
      st_line 'SOURCE-AT TEST pass'
    else
      st_rc 2
      st_line 'SOURCE-AT TEST fail'
    fi
    if [[ $v == fail ]]; then
      st_line 'SOURCE-AT ROCQCHK FAIL: tests/case_k.vo: Unhandled code 0018'
    else
      st_lacks 'SOURCE-AT ROCQCHK'
    fi
  done
  st_row S24d

  st_repo_rows
}

# S25 to S27: rules on the repository that holds this file ($ROOT), read as it is, with no case and no stub.
st_repo_rows() {
  local f p line n=0 self=0 build=0 body w found wf=$ROOT/.github/workflows/build-9.2-cut.yml
  local -a logs=()
  local -A ignored=()

  # S25: the log of each Redirect of a test, tests/<name>.out (redirect_logs), is a file that .gitignore ignores, so
  # that a run of the suite leaves no file git status lists.
  ST_LABEL=S25
  for f in "$ROOT"/tests/*.v; do
    while IFS= read -r p; do
      if [[ -n $p ]]; then logs+=("$p"); fi
    done <<<"$(redirect_logs "$f" tests)"
  done
  if ((${#logs[@]} == 0)); then
    st_bad "no Redirect in $ROOT/tests/*.v"
  else
    found=$(printf '%s\n' "${logs[@]}" | git -C "$ROOT" check-ignore --stdin)
    while IFS= read -r p; do
      if [[ -n $p ]]; then ignored[$p]=1; fi
    done <<<"$found"
    for p in "${logs[@]}"; do
      [[ -n ${ignored[$p]:-} ]] || st_bad "$p, the log of a Redirect of a test, is not ignored by git (.gitignore)"
    done
  fi
  st_row S25

  # S26: what build_switch builds the switch from is in ci/cut-settings.sh, the one file the workflow's cache key
  # hashes: the text of build_switch (declare -f, without its comments) names no version, package or compiler
  # option, and the settings give the OCaml configuration, the pins and the packages it installs.
  ST_LABEL=S26
  body=$(declare -f build_switch)
  if [[ $body =~ [0-9]+\.[0-9]+\.[0-9]+ ]]; then st_bad "build_switch names the version ${BASH_REMATCH[0]}"; fi
  for w in flambda naked_pointers rocq-runtime rocq-core coq-core coqide-server coq-stdlib rocq-stdlib dune yojson; do
    [[ $body != *"$w"* ]] || st_bad "build_switch names $w"
  done
  for w in OCAML_SWITCH_CONFIG ROCQ_SOURCE_PINS VERSION_PINS SWITCH_INSTALL; do
    grep -q "^$w=" -- "$SETTINGS" || st_bad "$SETTINGS sets no $w"
  done
  st_row S26

  # S27: the workflow runs this self-test before the build: its step "run: ci/build-9.2-cut.sh --self-test" comes
  # before its step "run: ci/build-9.2-cut.sh".
  ST_LABEL=S27
  if [[ -f $wf ]]; then
    while IFS= read -r line || [[ -n $line ]]; do
      n=$((n + 1))
      line=${line#"${line%%[![:space:]]*}"} line=${line%"${line##*[![:space:]]}"}
      if [[ $line == 'run: ci/build-9.2-cut.sh --self-test' ]] && ((!self)); then self=$n; fi
      if [[ $line == 'run: ci/build-9.2-cut.sh' ]] && ((!build)); then build=$n; fi
    done <"$wf"
    if ((!self)); then
      st_bad "no step of $wf runs ci/build-9.2-cut.sh --self-test"
    elif ((!build)); then
      st_bad "no step of $wf runs ci/build-9.2-cut.sh"
    elif ((self > build)); then
      st_bad "$wf runs the self-test (line $self) after the build (line $build)"
    fi
  else
    st_bad "no $wf"
  fi
  st_row S27
}

st_h_case() { # <label> <test file text> <run's log, printf %b> <case_h.log.out, printf %b, or - for none>: a case whose
  # tests/case_h.v is the text, fixed for the entry H.planted by fix a (st_r5_test), and whose parent side shows the
  # two logs (the stub's play:<status> outcome)
  st_new "$1"
  st_r5_test case_h H.planted <<<"$2"
  st_fx run.log "$3"
  if [[ $4 != - ]]; then st_fx case_h.log.out "$4"; fi
}

st_h_met() { # the control of tests/case_h.v is met at H.planted
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/case_h.v at H.planted (src/ of $ST_BASE)"
}

st_h_unmet() { # <messages...>: the control of tests/case_h.v is not met, as its r5 lines say, with each message
  local m
  st_rc nonzero
  st_has 'R5 negative not met: the test fails, but not as the r5 lines of tests/case_h.v say'
  for m in "$@"; do st_has "$m"; done
  st_lacks 'R5 NEGATIVE MET'
}

# S7l-A2 to S7l-A8e: an "r5 assertion" line whose text does not name the row's entry is met when some line of the
# Redirect's log that starts with the text has, right before it in that log, a refusal header of exactly that entry:
# "Skipping: Error at line N (for <entry>)" or "Error at line N (for <entry>)", as src/lean.ml's refusal prints a
# message on the line after its header (after_refusal_header). One row per row A2 to A8e of the rule's decision
# table (A1 is S7j; A5 is the head side, as V11). In each case the parent side fails with the stub's play:1 outcome,
# and its run's log holds the failure of the assertion's .expect line unless the row says otherwise.
st_r5_header_rows() {
  local t='Anomaly "File "m.ml", line 1, characters 2-3: Assertion failed."' v i u
  local r='Please report at http://example.invalid/bugs/.'
  local h='Skipping: Error at line 7 (for H.planted): {"thm": 7}'
  local o='Skipping: Error at line 5 (for H.other): {"thm": 5}'
  local import='Redirect "case_h.log" Lean Import "../dumps/small.ndjson".'
  local test_h="(* r5 assertion: \"case_h.log\" $t *)"$'\n'"$import"
  local run="EXPECT FAIL: tests/case_h.expect:3: case_h.log.out: unexpected '$t'\n"
  local iii="'$t' does not name H.planted, and no line right before it in case_h.log.out is a refusal header of H.planted"
  local no_start="case_h.log.out has no line starting '$t'"

  # A2: the text follows a Skip-mode header of the entry.
  st_h_case S7l-A2 "$test_h" "$run" "line 7: H.planted\n$h\n$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_h_met
  st_line "R5 CASE MET: tests/case_h.v, r5 assertion case_h.log: $t"
  st_row S7l-A2

  # A2b: a Stop-mode header, printed after the summary.
  st_h_case S7l-A2b "$test_h" "$run" "line 7: H.planted\n\nDone!\n- 1 entries\nError at line 7 (for H.planted): {\"thm\": 7}\n$t\n$r\n"
  st_revert play:1 tests/case_h.v
  st_h_met
  st_row S7l-A2b

  # A2c: a Fail-mode header, inside the Redirect of a Fail command.
  st_h_case S7l-A2c "(* r5 assertion: \"case_h.log\" $t *)"$'\n''Redirect "case_h.log" Fail Lean Import "../dumps/small.ndjson".' \
    "$run" "The command has indeed failed with message:\nError at line 7 (for H.planted): {\"thm\": 7}\n$t\n$r\n"
  st_revert play:1 tests/case_h.v
  st_h_met
  st_row S7l-A2c

  # A3a: the line before the text is the header of another entry.
  st_h_case S7l-A3a "$test_h" "$run" "$o\n$t\n$r\nline 7: H.planted\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A3a

  # A3b: the line before the text is no header, although it names the entry.
  st_h_case S7l-A3b "$test_h" "$run" "line 7: H.planted\n$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A3b

  # A3c: the header's line names the entry in its json, but its "(for ...)" part names another entry.
  st_h_case S7l-A3c "$test_h" "$run" "line 5: H.other\nSkipping: Error at line 5 (for H.other): {\"note\": \"H.planted\"}\n$t\n$r\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A3c

  # A3d: no line of the log starts with the text.
  st_h_case S7l-A3d "$test_h" "$run" "line 7: H.planted\n$h\nnote: $t\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$no_start" "$iii"
  st_row S7l-A3d

  # A3e: the header names a longer name, or the entry followed by another character.
  for v in '!' '?' '.x'; do
    st_h_case "S7l-A3e/$v" "$test_h" "$run" "Skipping: Error at line 7 (for H.planted$v): {\"thm\": 7}\n$t\n$r\n"
    st_revert play:1 tests/case_h.v
    st_h_unmet "$iii"
  done
  st_row S7l-A3e

  # A4: the text twice, first after another entry's header, then after the entry's.
  st_h_case S7l-A4 "$test_h" "$run" "$o\n$t\n$r\n$h\n$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_h_met
  st_row S7l-A4

  # A4r: the text twice, first after the entry's header, then after another entry's.
  st_h_case S7l-A4r "$test_h" "$run" "$h\n$t\n$r\n$o\n$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_h_met
  st_row S7l-A4r

  # A4b: the text twice, after neither the entry's header nor right after it, though the log has that header.
  st_h_case S7l-A4b "$test_h" "$run" "$h\nline 8: H.mid\n$t\n$r\n$o\n$t\n$r\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A4b

  # A5: the head side shows the header and the text too: it fails, and the control with it.
  st_h_case S7l-A5 "$test_h" "$run" "line 7: H.planted\n$h\n$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v ST_OUTCOME_HEAD=play:1
  st_rc nonzero
  st_has 'R5 negative not met: the head side fails at H.planted'
  st_lacks 'R5 NEGATIVE MET'
  st_row S7l-A5

  # A6: the entry's header ends the log of another Redirect, and the text starts the assertion's log.
  st_h_case S7l-A6 "(* r5 assertion: \"case_h.log\" $t *)"$'\n''Redirect "case_g.log" Lean Import "../dumps/small.ndjson".'$'\n'"$import" \
    "$run" "$t\n$r\nDone!\n"
  st_fx case_g.log.out "line 7: H.planted\n$h\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A6

  # A7a: the entry's header is two lines above the text.
  st_h_case S7l-A7a "$test_h" "$run" "line 7: H.planted\n$h\nthe first line of the message\n$t\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A7a

  # A7b: the text starts the entry's own header (Stop form, then Skip form) and names no entry; the line before it
  # is the entry's progress line.
  i=0
  for v in 'Error at line 7' 'Skipping: Error at line 7'; do
    i=$((i + 1))
    if ((i == 1)); then u='Error at line 7 (for H.planted): {"thm": 7}'; else u=$h; fi
    st_h_case "S7l-A7b/$i" "(* r5 assertion: \"case_h.log\" $v *)"$'\n'"$import" \
      "EXPECT FAIL: tests/case_h.expect:3: case_h.log.out: unexpected '$v'\n" "line 7: H.planted\n$u\nmissing something\n"
    st_revert play:1 tests/case_h.v
    st_h_unmet "'$v' does not name H.planted, and no line right before it in case_h.log.out is a refusal header of H.planted"
  done
  st_row S7l-A7b

  # A7c: the text is the log's first line.
  st_h_case S7l-A7c "$test_h" "$run" "$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "$iii"
  st_row S7l-A7c

  # A8a: the log does not exist: that alone is reported.
  st_h_case S7l-A8a "$test_h" "$run" -
  st_revert play:1 tests/case_h.v
  st_h_unmet 'case_h.log.out does not exist'
  st_lacks 'has no line starting'
  st_lacks 'does not name H.planted'
  st_row S7l-A8a

  # A8b: the log is empty.
  st_h_case S7l-A8b "$test_h" "$run" ''
  st_revert play:1 tests/case_h.v
  st_h_unmet "$no_start" "$iii"
  st_lacks 'case_h.log.out does not exist'
  st_row S7l-A8b

  # A8e: the log, which would meet the rule, cannot be read (mode 000): that alone is reported.
  st_h_case S7l-A8e "$test_h" "$run" "line 7: H.planted\n$h\n$t\n$r\nDone!\n"
  st_fx unreadable 'case_h.log.out\n'
  st_revert play:1 tests/case_h.v
  st_h_unmet 'case_h.log.out cannot be read'
  st_lacks 'has no line starting'
  st_lacks 'does not name H.planted'
  st_row S7l-A8e

  # A8c: Fail mode with no Fail command: the import's error ends the Redirect, the header and the text are in the
  # run's log and not in the Redirect's, and no .expect is checked.
  st_h_case S7l-A8c "$test_h" \
    "File \"./case_h.v\", line 2, characters 0-60:\nError: Error at line 7 (for H.planted): {\"thm\": 7}\n$t\n$r\n" \
    "line 7: H.planted\n"
  st_revert play:1 tests/case_h.v
  st_h_unmet "the run's log has no line \"EXPECT FAIL: tests/case_h.expect:<n>: case_h.log.out: unexpected '$t'\"" \
    "$no_start" "$iii"
  st_row S7l-A8c

  # A8d: the test's only Redirect follows Fail on its line: r5_lines counts no Redirect "case_h.log", the r5 line is
  # bad, and no test runs.
  st_h_case S7l-A8d "(* r5 assertion: \"case_h.log\" $t *)"$'\n''Fail Redirect "case_h.log" Lean Import "../dumps/small.ndjson".' \
    "$run" "line 7: H.planted\n$h\n$t\n$r\nDone!\n"
  st_revert play:1 tests/case_h.v
  st_rc nonzero
  st_has 'tests/case_h.v line 1: no Redirect "case_h.log" in the test'
  st_lacks 'R5 NEGATIVE MET'
  st_not_ran
  st_row S7l-A8d
}

st_revert_rows() {
  local v c head parent mode test=tests/lean434_a.v inv=$INVENTORY hard want s expected

  # V1 (S22c): a source-only fix, with a different stack on its parent and at the head.
  for v in 32768 none; do
    st_new "S22c/$v"
    printf 'src before fix\n' >"$ST_REPO/src/marker"
    st_set_stack "$ST_REPO/$SCRIPT_REL" "$v"
    st_commit "parent source and stack"
    parent=$(git -C "$ST_REPO" rev-parse HEAD)
    printf 'src after fix\n' >"$ST_REPO/src/marker"
    printf 'let fix_c = 1\n' >"$ST_REPO/src/fix_c.ml"
    st_commit "fix only the source"
    st_control_row "$(git -C "$ST_REPO" rev-parse HEAD)" -
    st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
    st_commit "row a and the head stack"
    st_revert fail:Alpha.one "$test"
    st_rc 0
    st_two_calls 65536 65536 'src after fix' 'src before fix'
    st_line "R5 NEGATIVE MET: $test at Alpha.one (src/ of $parent)"
  done
  st_row 'V1 (S22c)'

  # V2 (S22b): stack-only, with a later source change that both builds must use.
  for v in 32768 none absent; do
    st_new "S22b/$v"
    st_stack_fix "$v"
    head=$(git -C "$ST_REPO" rev-parse HEAD)
    st_revert fail:Alpha.one "$test"
    st_rc 0
    if [[ $v == 32768 ]]; then want=$v; else want=-; fi
    st_stack_calls 65536 "$want"
    st_line "R5 NEGATIVE MET: $test at Alpha.one (src/ of $head)"
  done
  st_row 'V2 (S22b)'

  # V3 (S22): refuse a control that changes both, in one fix commit or in several.
  for v in together separate; do
    st_new "S22/$v"
    st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
    if [[ $v == separate ]]; then
      st_commit "fix the stack first"
      c="$(git -C "$ST_REPO" rev-parse HEAD) "
    else
      c=
    fi
    printf 'let fix_s = 1\n' >"$ST_REPO/src/fix_s.ml"
    st_commit "fix the source"
    st_control_row "$c$(git -C "$ST_REPO" rev-parse HEAD)" -
    st_commit "row a"
    st_revert fail:Alpha.one "$test"
    st_rc 1
    st_has "the fix commits of $test change src/ and CUT_STACK_KIB; a control reverts one of them; split the fix"
    st_not_ran
  done
  st_row 'V3 (S22)'

  # V4: editing the script without changing the parsed stack or src/ is not a fix.
  st_new V4
  st_set_stack "$ST_REPO/$SCRIPT_REL" '"131072"'
  st_commit "quote the same stack value"
  st_control_row "$(git -C "$ST_REPO" rev-parse HEAD)" -
  st_commit "row a"
  st_revert fail:Alpha.one "$test"
  st_rc 1
  st_has "the fix commits of $test change neither src/ nor CUT_STACK_KIB; there is nothing to revert"
  st_not_ran
  st_row V4

  # V4b: a move out of src/ counts as a source change, even with rename detection configured.
  st_new V4b
  git -C "$ST_REPO" config diff.renames true
  printf 'let moved = 1\n' >"$ST_REPO/src/fix_move.ml"
  printf 'src before fix\n' >"$ST_REPO/src/marker"
  st_commit "add the file to move"
  parent=$(git -C "$ST_REPO" rev-parse HEAD)
  git -C "$ST_REPO" mv src/fix_move.ml tests/fix_move.ml || st_bad "cannot move the file out of src/"
  st_commit "move the file out of src/"
  c=$(git -C "$ST_REPO" rev-parse HEAD)
  [[ $(git -C "$ST_REPO" diff --name-status "$parent" "$c") == R100$'\t'src/fix_move.ml$'\t'tests/fix_move.ml ]] ||
    st_bad "the fix did not make a rename"
  st_control_row "$c" -
  st_commit "row a"
  st_revert fail:Alpha.one "$test"
  st_rc 0
  st_two_calls 131072 131072 'src before fix' 'src before fix'
  [[ $(st_call_field 6) != *fix_move.ml* && $(st_call_field 6 2) == *fix_move.ml* ]] ||
    st_bad "the moved file should appear in the parent's src/ only"
  st_line "R5 NEGATIVE MET: $test at Alpha.one (src/ of $parent)"
  st_row V4b

  # V4c: reject a merge, a root and a shallow boundary used as a fix.
  for v in merge root shallow; do
    st_new "V4c/$v"
    case $v in
      merge)
        git -C "$ST_REPO" switch -qc fix-side || st_bad "cannot start a side branch"
        printf 'let side = 1\n' >"$ST_REPO/src/fix_side.ml"
        st_commit "source fix on a side branch"
        git -C "$ST_REPO" switch -q main && git -C "$ST_REPO" merge -q --no-ff -m merge fix-side ||
          st_bad "cannot merge the side branch"
        c=$(git -C "$ST_REPO" rev-parse HEAD)
        ;;
      root) c=$ST_BASE ;;
      shallow) c=$ST_FIX_A ;;
    esac
    st_control_row "$c" -
    if [[ $v == shallow ]]; then
      printf '%s\n' "$c" >"$ST_REPO/.git/shallow"
      [[ $(git -C "$ST_REPO" rev-list --parents -n 1 "$c") == "$c" ]] || st_bad "the fix is not a shallow boundary"
    fi
    st_revert fail:Alpha.one "$test"
    st_rc 1
    st_has "fix commit $c is a merge or has no parent; a control needs one parent"
    st_not_ran
  done
  st_row V4c

  # V4d: refuse a malformed fix hash or a commit outside HEAD before inspecting its paths.
  for v in malformed unrelated; do
    st_new "V4d/$v"
    if [[ $v == malformed ]]; then
      c=${ST_FIX_A:0:8}
      expected="'$c' is not a full commit hash"
    else
      c=$(git -C "$ST_REPO" commit-tree -m unrelated "$ST_BASE^{tree}")
      expected="commit $c is not an ancestor of HEAD"
    fi
    st_control_row "$c" -
    st_revert fail:Alpha.one "$test"
    st_rc 1
    st_has "$inv line 2 ($test): $expected"
    st_not_ran
  done
  st_row V4d

  # V5 (S22d): neither script's 131072 can override a source control's 8192.
  st_new S22d
  st_control_row "$ST_FIX_A" 8192
  st_commit "row a specifies a lower stack"
  st_revert fail:Alpha.one "$test"
  st_rc 0
  st_two_calls 8192 8192 'src at head' 'src at base'
  st_line "R5 NEGATIVE MET: $test at Alpha.one (src/ of $ST_BASE)"
  st_row 'V5 (S22d)'

  # V6: only a source control can specify a stack.
  st_new V6
  st_stack_fix 32768
  st_control_row "$ST_STACK_FIX" 8192
  st_revert fail:Alpha.one "$test"
  st_rc 1
  st_has "a row that states a stack cannot revert a stack fix"
  st_not_ran
  st_row V6

  # V7: the stack field is validated in each mode that reads the inventory.
  for v in '' 0 -1 unlimited 12x abc; do
    st_new "V7/'$v'"
    st_control_row "$ST_FIX_A" "$v"
    if [[ -z $v ]]; then expected='empty stack field'; else expected="stack '$v' is not a positive whole number of KiB"; fi
    for mode in plain handoff revert; do
      ST_LABEL="V7/'$v'/$mode"
      case $mode in
        plain) st_run -- ;;
        handoff) st_run -- --handoff ;;
        revert) st_revert fail:Alpha.one "$test" ;;
      esac
      st_rc 1
      st_has "$inv line 2 cannot be read ($expected)"
      st_not_ran
    done
  done
  st_row V7

  # V7b: the limits check allows 1; the stub stands in for what the import actually does at that limit.
  st_new V7b
  st_control_row "$ST_FIX_A" 1
  st_revert fail:Alpha.one "$test"
  st_rc 0
  st_two_calls 1 1 'src at head' 'src at base'
  st_row V7b

  # V8: the hard limit includes equality. V8b: the gVisor rule (including unknown kernels) applies to a row.
  for v in 65535 65536 65537; do
    st_new "V8/$v"
    st_control_row "$ST_FIX_A" "$v"
    st_revert fail:Alpha.one "$test" ST_HARD=65536
    if ((v <= 65536)); then
      st_rc 0
      st_two_calls "$v" "$v" 'src at head' 'src at base'
    else
      st_rc 1
      st_has "$inv line 2 stack=$v is above the hard stack limit of 65536 KiB"
      st_not_ran
    fi
  done
  st_row V8
  for v in gvisor:131071 gvisor:131072 gvisor:131073 fail:131073 empty:131073 generic:131073; do
    st_new "V8b/$v"
    want=${v#*:} mode=${v%%:*}
    st_control_row "$ST_FIX_A" "$want"
    st_revert fail:Alpha.one "$test" "ST_UNAME=$mode"
    if ((want <= 131072)) || [[ $mode == generic ]]; then
      st_rc 0
      st_two_calls "$want" "$want" 'src at head' 'src at base'
    else
      st_rc 1
      st_has "$inv line 2 stack=$want is above 131072 KiB, and gVisor caps the stack at 128 MiB"
      st_not_ran
    fi
  done
  st_row V8b

  # V9: test the same checks on the stack fix's parent without making the head exceed a limit.
  for v in abc 65537 65538 131073; do
    st_new "V9/$v"
    st_stack_fix "$v"
    hard=65537 mode=generic
    if [[ $v == 131073 ]]; then hard=unlimited mode=gvisor; fi
    st_revert fail:Alpha.one "$test" "ST_HARD=$hard" "ST_UNAME=$mode"
    if [[ $v == 65537 ]]; then
      st_rc 0
      st_stack_calls 65536 "$v"
    else
      st_rc 1
      st_has "parent side (fix parent $ST_STACK_PARENT):"
      case $v in
        abc) st_has "CUT_STACK_KIB='abc' is not a positive whole number of KiB" ;;
        65538) st_has 'CUT_STACK_KIB=65538 is above the hard stack limit of 65537 KiB' ;;
        131073) st_has 'CUT_STACK_KIB=131073 is above 131072 KiB, and gVisor caps the stack at 128 MiB' ;;
      esac
      st_not_ran
    fi
  done
  st_row V9

  # V10: an unset script uses the default, but not an unlimited default.
  for v in head parent; do
    st_new "V10/$v"
    if [[ $v == parent ]]; then st_stack_fix none; else st_set_stack "$ST_REPO/$SCRIPT_REL" none; fi
    st_revert fail:Alpha.one "$test" ST_DEFAULT_SOFT=unlimited
    st_rc 1
    st_has "$v side"
    st_has 'the default soft stack is unlimited'
    st_not_ran
  done
  st_row V10

  # V10b: the checker refuses a mismatch on either side, before either import.
  for v in head parent; do
    st_new "V10b/$v"
    st_stack_fix 32768
    if [[ $v == head ]]; then want=65536; else want=32768; fi
    st_revert fail:Alpha.one "$test" "ST_SOFT_${v^^}=8192"
    st_rc 1
    st_has "$v side"
    st_has "the soft stack read back is 8192 KiB, not CUT_STACK_KIB=$want"
    st_not_ran
  done
  st_row V10b

  # V11: any head failure invalidates the control, even if the parent's outcome would otherwise meet R5.
  for v in fail:Alpha.one fail-noentry build-fail; do
    st_new "V11/$v"
    head=$(git -C "$ST_REPO" rev-parse HEAD)
    st_revert fail:Alpha.one "$test" "ST_OUTCOME_HEAD=$v"
    st_rc 1
    st_has "R5 negative not met: the head side fails at Alpha.one (src/ of $head, STACK soft=131072 hard=131072)"
    st_calls 'head:131072:src at head'
    st_lacks 'R5 NEGATIVE MET'
  done
  st_row V11

  # V12: all parent failures name the actual source and stack, including when the source is the head's.
  for v in pass fail:Alpha.two fail-noentry build-fail r5-lines; do
    st_new "V12/$v"
    st_stack_fix 32768
    if [[ $v == r5-lines ]]; then
      printf '%s\n' '(* r5 error: planted failure *)' 'Check Alpha.' >"$ST_REPO/$test"
      st_commit "add an r5 line to the head's test"
    fi
    head=$(git -C "$ST_REPO" rev-parse HEAD)
    if [[ $v == r5-lines ]]; then st_revert fail:Alpha.one "$test"; else st_revert "$v" "$test"; fi
    st_rc 1
    st_stack_calls 65536 32768
    case $v in
      pass) expected='R5 negative not met: the test passes' ;;
      fail:Alpha.two) expected='the test fails at Alpha.two, but its row names Alpha.one' ;;
      fail-noentry) expected='the test fails at no "Error at line N (for X)" line' ;;
      build-fail) expected="the parent side's plugin build failed" ;;
      r5-lines) expected='the test fails, but not as the r5 lines' ;;
    esac
    st_has "$expected"
    st_has "(src/ of $head, STACK soft=32768 hard=32768)"
    st_lacks 'R5 NEGATIVE MET'
  done
  st_row V12

  # V13: six columns are not a seven-column row with an implicit "-".
  st_new V13
  st_inventory "${ST_ROW_A%$'\t'*}" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
  st_revert fail:Alpha.one "$test"
  st_rc 1
  st_has "$inv line 2 cannot be read (6 fields, not 7)"
  st_not_ran
  st_row V13

  # V14: both suite modes ignore the control stack, even for a row with a different value.
  st_new V14
  st_control_row "$ST_FIX_A" 8192
  for mode in plain handoff; do
    ST_LABEL="V14/$mode"
    : >"$ST_CASE/calls"
    if [[ $mode == plain ]]; then st_run --; else st_run -- --handoff; fi
    st_rc 0
    st_calls 'suite:131072:src at head'
    st_line 'STACK soft=131072 hard=131072'
  done
  st_row V14

  # V15: one record with the two actual src/ commits and read-backs, before the verdict.
  st_new V15
  head=$(git -C "$ST_REPO" rev-parse HEAD)
  st_control_row "$ST_FIX_A" 8192
  st_revert fail:Alpha.one "$test" ST_HARD=32768
  st_rc 0
  st_two_calls 8192 8192 'src at head' 'src at base'
  s='STACK soft=8192 hard=32768'
  expected="R5 CONTROL head: src/ of $head, $s; parent: src/ of $ST_BASE, $s"
  st_count "$expected" 1
  st_file_is "$ST_CASE/out" "$expected"$'\n'"R5 NEGATIVE MET: $test at Alpha.one (src/ of $ST_BASE)"
  st_row V15

  # V16: open and listed rows cannot state a stack.
  for v in open listed; do
    st_new "V16/$v"
    st_control_row - 8192 "$v"
    st_run --
    st_rc 1
    st_has "$inv line 2 cannot be read (a stack applies only to a fixed row's control)"
    st_not_ran
  done
  st_row V16
}

self_test() {
  unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES
  export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_AUTHOR_NAME=self-test \
    GIT_AUTHOR_EMAIL=self-test@example.invalid GIT_COMMITTER_NAME=self-test GIT_COMMITTER_EMAIL=self-test@example.invalid
  ST_ROOT=$(mktemp -d "${TMPDIR:-/tmp}/build-9.2-cut-self-test.XXXXXX") || {
    echo "cannot create a scratch directory under ${TMPDIR:-/tmp}" >&2
    return 1
  }
  SCRATCH_DIRS+=("$ST_ROOT")
  if ! { st_stubs && st_template; }; then
    echo "SELF-TEST setup failed" >&2
    return 1
  fi
  st_rows
  printf 'SELF-TEST %s PASS %s FAIL\n' "$ST_PASS" "$ST_FAIL"
  ((ST_FAIL == 0))
}
