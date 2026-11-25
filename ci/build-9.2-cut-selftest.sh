# shellcheck shell=bash
# ci/build-9.2-cut-selftest.sh: the self-test of ci/build-9.2-cut.sh, whose --self-test mode sources this file and
# runs self_test. It reads the settings and helpers of that script (SELF, SETTINGS, SCRIPT_REL, INVENTORY, ...).

# ---- Self-test ------------------------------------------------------------------------------------------------
# One row per rule of ci/build-9.2-cut.sh, S0 to S24c, the rule stated in the comment above the row. Each case of
# a row runs on its own copy of a scratch git repository (made with git init and real commits under a mktemp -d
# of $TMPDIR), through a copy of the script with the stubs its "Self-test stubs" section describes. A row passes
# only when every one of its cases shows the exit status and the lines or files the row names.

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
  printf '# file\tfeatures\tbase_entry\town_entry\tstatus\tcommits\n'
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
# Self-test stand-in for RUN_TEST. $1: suite|one, $2: tree, $3: test name; ST_OUTCOME picks the outcome. Each call
# is recorded with the opam root and switch its environment selects ("<unset>" when none).
src_marker=$(<"$2/src/marker") tests_marker=$(<"$2/tests/marker") fixes=$(cd "$2/src" && echo fix_*.ml)
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "${3:-}" "$src_marker" "$tests_marker" "$fixes" \
  "${OPAMROOT-<unset>}" "${OPAMSWITCH-<unset>}" >>"$ST_CALLS"
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
    # The case filled ST_FX: run.log is the run's output, and every other file goes to tests/ of the tree as a
    # Redirect log of the test.
    for f in "$ST_FX"/*; do
      [[ -f $f ]] || continue
      if [[ ${f##*/} == run.log ]]; then cat -- "$f"; else cp -- "$f" "$2/tests/"; fi
    done
    exit "${ST_OUTCOME#play:}" ;;
  *) echo "stub: unknown ST_OUTCOME '$ST_OUTCOME'" >&2; exit 99 ;;
esac
EOF
  cat >"$s/ulimit" <<'EOF'
#!/usr/bin/env bash
# Self-test stand-in for the stack read-back. $1: soft|hard, $2: the KiB the setter was asked for, or "-".
case $1 in
  soft) if [[ -n $ST_SOFT ]]; then echo "$ST_SOFT"; elif [[ $2 == - ]]; then echo "$ST_DEFAULT_SOFT"; else echo "$2"; fi ;;
  hard) echo "$ST_HARD" ;;
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
printf 'compile\t%s\t%s\n' "$PWD" "$*" >>"$ST_CALLS"
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
printf 'check\t%s\t%s\n' "$PWD" "$*" >>"$ST_CALLS"
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
  cp -- "$SELF" "$t/$SCRIPT_REL" && cp -- "$SETTINGS" "$t/ci/" || return 1
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
  ST_ROW_A=$(st_tsv tests/lean434_a.v F1 Alpha.one - fixed "$ST_FIX_A")
  ST_ROW_B=$(st_tsv tests/lean434_b.v 'F2 F3' Beta.base Beta.own fixed "$ST_FIX_B")
  ST_ROW_C=$(st_tsv tests/lean434_c.v F4 Gamma.one - listed -)
  ST_ROW_OPT=$(st_tsv tests/lean434_opt.v F5 'option:Lean Entry Timeout' - fixed "$ST_FIX_OPT")
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
      "$(st_tsv "tests/$1.v" F9 "$2" - fixed "$ST_FIX_A")" >"$ST_REPO/$INVENTORY"; } || st_bad "cannot write tests/$1.v"
  st_commit "test $1"
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
        CUT_STUB_CHECK="$ST_ROOT/stubs/check" ST_CALLS="$ST_CASE/calls" ST_OUTCOME=pass ST_SOFT= \
        ST_DEFAULT_SOFT=8192 ST_HARD=unlimited ST_UNAME=generic ST_FX="$ST_CASE/fx" "${envs[@]}" \
        bash "$ST_REPO/$SCRIPT_REL" "$@"
  ) >"$ST_CASE/out" 2>"$ST_CASE/err" </dev/null
  ST_RC=$?
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
st_call_field() { # <field number>: that field of the first recorded call
  local -a fields
  IFS=$'\t' read -r -a fields <"$ST_CASE/calls"
  printf '%s' "${fields[$1 - 1]:-}"
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
  local head v dangling inv=$INVENTORY plain work parent fix c
  local at_a="src/ of $ST_BASE, the parent of the first fix commit $ST_FIX_A"
  local stack1='STACK soft=8192 hard=unlimited'

  # S0: a clean tree passes every check and goes on to build and run the suite (SUITE PASS), plain and with
  # --handoff.
  for v in plain --handoff; do
    st_new "S0/$v"
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
      st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_d.v F6 Delta.one - open -)" >"$ST_REPO/$inv"
    else
      st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_d.v F6 Delta.one - fixed "$ST_FIX_A")" >"$ST_REPO/$inv"
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
    st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - fixed "$c")" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
    st_commit "row a: $v"
    if [[ $v == blank-revert ]]; then st_run ST_OUTCOME=fail:Alpha.one -- --revert-fix tests/lean434_a.v; else st_run --; fi
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
    st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - open -)" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
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
  st_run ST_OUTCOME=fail:Alpha.one -- --revert-fix tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_ran one
  [[ $(st_call_field 4) == 'src at base' && $(st_call_field 6) == 'fix_*.ml' ]] ||
    st_bad "src/ is not the parent's of fix a: $(st_call_field 4), $(st_call_field 6)"
  [[ $(st_call_field 5) == 'tests at head' ]] || st_bad "tests/ is not the head's: $(st_call_field 5)"
  st_tree_untouched "$head"
  st_row S5

  # S6: --revert-fix fails ("R5 negative not met") when the test passes at the parent's src/, and names it.
  st_new S6
  st_run ST_OUTCOME=pass -- --revert-fix tests/lean434_a.v
  st_rc nonzero
  st_has "R5 negative not met: the test passes ($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_ran one
  st_row S6

  # S7: --revert-fix, built from the src/ of the parent of the row's first fix commit, fails when the test fails
  # at another entry than its row names (also a prefix or an extension of the right one, and the base entry where
  # the row names an own entry), when an option test fails elsewhere than its Set line, and when no "Error at
  # line N (for X)" line names an entry; the line names the parent.
  for v in Alpha.two Alpha.on Alpha.one.x; do
    st_new "S7/$v"
    st_run "ST_OUTCOME=fail:$v" -- --revert-fix tests/lean434_a.v
    st_rc nonzero
    st_has "the test fails at $v, but its row names Alpha.one ($at_a)"
    st_lacks 'R5 NEGATIVE MET'
  done
  st_new S7/own-entry
  st_run ST_OUTCOME=fail:Beta.base -- --revert-fix tests/lean434_b.v
  st_rc nonzero
  st_has "the test fails at Beta.base, but its row names Beta.own (src/ of $ST_FIX_A, the parent of the first fix commit $ST_FIX_B)"
  st_lacks 'R5 NEGATIVE MET'
  st_new S7/option
  st_run ST_OUTCOME=fail:Gamma.x -- --revert-fix tests/lean434_opt.v
  st_rc nonzero
  st_has 'the test fails at Gamma.x, not at its Set line'
  st_has "option:Lean Entry Timeout (src/ of $ST_FIX_B, the parent of the first fix commit $ST_FIX_OPT)"
  st_lacks 'R5 NEGATIVE MET'
  st_new S7/no-entry
  st_run ST_OUTCOME=fail-noentry -- --revert-fix tests/lean434_a.v
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
  st_run ST_OUTCOME=fail:Alpha.one -- --revert-fix tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_ran one
  [[ $(st_call_field 3) == lean434_a ]] || st_bad "RUN_TEST did not get the test name lean434_a"
  [[ $(st_call_field 2) != "$ST_REPO" ]] || st_bad "the test ran in the caller's tree"
  [[ $(st_call_field 4) == 'src at base' && $(st_call_field 6) == 'fix_*.ml' ]] ||
    st_bad "src/ is not the parent's of fix a: $(st_call_field 4), $(st_call_field 6)"
  [[ $(st_call_field 5) == 'tests at head' ]] || st_bad "tests/ is not the head's: $(st_call_field 5)"
  [[ $(st_call_field 7) == "$ST_CASE/cut/opam" && $(st_call_field 8) == cut ]] ||
    st_bad "the test did not run on the cut's switch: OPAMROOT $(st_call_field 7), OPAMSWITCH $(st_call_field 8)"
  st_tree_untouched "$head"
  st_new S7b/own
  st_run ST_OUTCOME=fail:Beta.own -- --revert-fix lean434_b
  st_rc zero
  st_line "R5 NEGATIVE MET: lean434_b at Beta.own (src/ of $ST_FIX_A)"
  [[ $(st_call_field 6) == fix_a.ml ]] || st_bad "src/ is not the parent's of fix b: $(st_call_field 6)"
  st_new S7b/option
  st_run 'ST_OUTCOME=option:Lean Entry Timeout' -- --revert-fix tests/lean434_opt.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_opt.v at option:Lean Entry Timeout (src/ of $ST_FIX_B)"
  st_new S7b/quoted
  sed -i 's/\tAlpha\.one\t/\t«Alpha».one\t/' "$ST_REPO/tests/lean434_features.txt"
  grep -q '«Alpha».one' "$ST_REPO/tests/lean434_features.txt" || st_bad "the template's row names no Alpha.one to quote"
  st_commit "quote a name component as Lean does"
  st_run ST_OUTCOME=fail:Alpha.one -- --revert-fix tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_row S7b

  # S7c: a test that imports under Redirect gets the importer's errors in the Redirect's .out file, not in the
  # run's log: --revert-fix reads that file too, and passes when its first entry error is the row's entry.
  st_new S7c
  st_redirect_test lean434_a.log
  st_commit "test a imports under Redirect"
  st_run ST_OUTCOME=redirect:lean434_a.log=Alpha.one -- --revert-fix tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_lacks 'Error at line 7 (for Alpha.one)'
  st_row S7c

  # S7d: a failure at another entry that only a Redirect's .out file names fails --revert-fix, which names that
  # entry and the parent.
  st_new S7d
  st_redirect_test lean434_a.log
  st_commit "test a imports under Redirect"
  st_run ST_OUTCOME=redirect:lean434_a.log=Alpha.two -- --revert-fix tests/lean434_a.v
  st_rc nonzero
  st_has "R5 negative not met: the test fails at Alpha.two, but its row names Alpha.one ($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_row S7d

  # S7e: the .out files are read in the order of the test's Redirect lines, not the order they were written: the
  # first names another entry, so --revert-fix fails, although the second names the row's entry.
  st_new S7e
  st_redirect_test lean434_a_1.log lean434_a_2.log
  st_commit "test a imports under two Redirects"
  st_run 'ST_OUTCOME=redirect:lean434_a_2.log=Alpha.one lean434_a_1.log=Alpha.two' -- --revert-fix tests/lean434_a.v
  st_rc nonzero
  st_has "R5 negative not met: the test fails at Alpha.two, but its row names Alpha.one ($at_a)"
  st_lacks 'R5 NEGATIVE MET'
  st_row S7e

  # S7f: the run's log is read before the .out files: its entry error, the row's, decides, although the .out file
  # of a Redirect names another entry.
  st_new S7f
  st_redirect_test lean434_a.log
  st_commit "test a imports under Redirect"
  st_run 'ST_OUTCOME=redirect:lean434_a.log=Alpha.two -=Alpha.one' -- --revert-fix tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  st_row S7f

  # S7g: a row naming two fix commits, the later one first: its first fix commit is the earlier one in the history
  # of HEAD, and --revert-fix builds the src/ of that commit's parent.
  st_new S7g
  st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - fixed "$ST_FIX_B $ST_FIX_A")" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
  st_commit "row a: two fix commits"
  st_run ST_OUTCOME=fail:Alpha.one -- --revert-fix tests/lean434_a.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_a.v at Alpha.one (src/ of $ST_BASE)"
  [[ $(st_call_field 6) == 'fix_*.ml' ]] || st_bad "src/ is not the parent's of fix a: $(st_call_field 6)"
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
    if [[ $v == pass ]]; then st_run -- --revert-fix tests/case_p.v; else st_run ST_OUTCOME=play:1 -- --revert-fix tests/case_p.v; fi
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
    st_ran one
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
    st_run ST_OUTCOME=play:1 -- --revert-fix tests/case_pp.v
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
    st_run ST_OUTCOME=play:1 -- --revert-fix tests/case_s.v
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
  # entry. Another assertion's failure, the failure on another Redirect's log, the failure with no such line in
  # the log (or no log), and a failed run with no assertion failure each fail.
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
    st_run ST_OUTCOME=play:1 -- --revert-fix tests/case_u.v
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
    st_run ST_OUTCOME=fail:M -- --revert-fix tests/case_m.v
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

  # S9b: a switch whose Rocq commit cannot be read (missing, empty, not a file) fails, the cut is never
  # assumed; no test runs.
  for v in missing empty directory; do
    st_new "S9b/$v"
    rm -f -- "$ST_CASE/cut/rocq-commit"
    case $v in
      empty) : >"$ST_CASE/cut/rocq-commit" ;;
      directory) mkdir -- "$ST_CASE/cut/rocq-commit" ;;
    esac
    st_run --
    st_rc nonzero
    st_has 'cannot read the Rocq commit of the switch'
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
      status) st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_x.v F7 X.one - 'done' -)" >"$ST_REPO/$inv" ;;
      file) st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv '' F7 X.one - listed -)" >"$ST_REPO/$inv" ;;
    esac
    st_commit "bad row: $v"
    st_run --
    st_rc nonzero
    st_has "$inv line 6 cannot be read"
    case $v in
      fields) st_has '5 fields, not 6' ;;
      status) st_has 'unknown status done' ;;
      file) st_has 'empty file field' ;;
    esac
    st_not_ran
  done
  st_row S12

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
  st_run ST_OUTCOME=build-fail -- --revert-fix tests/lean434_a.v
  st_rc nonzero
  st_has "the plugin build failed ($at_a)"
  st_has 'Error: Unbound value planted_build_error'
  st_lacks 'R5 NEGATIVE MET'
  st_row S14

  # S15: --revert-fix of an open row fails: an open row names no fix to revert; no test runs.
  st_new S15
  st_inventory "$(st_tsv tests/lean434_a.v F1 Alpha.one - open -)" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" >"$ST_REPO/$inv"
  st_commit "row a open"
  st_run -- --revert-fix tests/lean434_a.v
  st_rc nonzero
  st_has "$inv line 2 (tests/lean434_a.v) is open"
  st_not_ran
  st_row S15

  # S16: --revert-fix of a listed row succeeds without running the test, and says it skipped it.
  st_new S16
  st_run ST_OUTCOME=fail:Gamma.one -- --revert-fix tests/lean434_c.v
  st_rc zero
  st_line 'SKIPPED, LISTED: tests/lean434_c.v'
  st_lacks 'R5 NEGATIVE MET'
  st_not_ran
  st_row S16

  # S17: CUT_STACK_KIB unset: the default soft stack is read back into one STACK line, on stderr before the
  # test, or in <input>.stack (with the Rocq commit, nothing else printed) for --import and --check; an
  # unlimited default soft stack fails.
  st_new S17/suite
  st_run --
  st_rc zero
  st_count "$stack1" 1
  grep -qxF -e "$stack1" -- "$ST_CASE/err" || st_bad "the STACK line is not on stderr"
  [[ $(grep -nxF -e "$stack1" -- "$ST_CASE/err" | cut -d: -f1) -lt $(grep -nF 'STUB RUN-TEST' -- "$ST_CASE/err" | cut -d: -f1) ]] ||
    st_bad "the STACK line does not come before the test run"
  work=$ST_CASE/work
  st_new S17/import
  work=$ST_CASE/work
  mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v"
  st_run -- --import "$work/Import.v"
  st_rc zero
  st_file_is "$work/Import.v.stack" "$stack1"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_file_is "$ST_CASE/out" 'stub compile stdout'
  st_file_is "$ST_CASE/err" 'stub compile stderr'
  st_new S17/check
  work=$ST_CASE/work
  mkdir -p -- "$work" && : >"$work/Import.vo" && : >"$work/Other.vo"
  st_run -- --check "$work/Import.vo" "$work/Other.vo"
  st_rc zero
  st_file_is "$work/Import.vo.stack" "$stack1"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  [[ ! -e $work/Other.vo.stack ]] || st_bad "a .stack file was written for the second file"
  st_file_is "$ST_CASE/out" 'stub check stdout'
  st_file_is "$ST_CASE/err" 'stub check stderr'
  st_new S17/unlimited
  st_run ST_DEFAULT_SOFT=unlimited --
  st_rc nonzero
  st_has 'the default soft stack is unlimited'
  st_not_ran
  st_new S17/unlimited-import
  work=$ST_CASE/work
  mkdir -p -- "$work" && printf 'Check nat.\n' >"$work/Import.v"
  st_run ST_DEFAULT_SOFT=unlimited -- --import "$work/Import.v"
  st_rc nonzero
  st_has 'the default soft stack is unlimited'
  [[ ! -e $work/Import.v.stack ]] || st_bad "a .stack file was written"
  st_not_ran
  st_row S17

  # S18: CUT_STACK_KIB at or below the hard limit (the hard limit itself included) is set, read back and
  # reported, for the suite, --import and --check.
  st_new S18/suite
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run --
  st_rc zero
  st_count 'STACK soft=65536 hard=unlimited' 1
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
  st_file_is "$work/Import.v.stack" "STACK soft=65536 hard=unlimited"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_new S18/check
  work=$ST_CASE/work
  mkdir -p -- "$work" && : >"$work/Import.vo"
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run -- --check "$work/Import.vo"
  st_rc zero
  st_file_is "$work/Import.vo.stack" "STACK soft=65536 hard=unlimited"$'\n'"ROCQ COMMIT $CUT_ROCQ_COMMIT"
  st_row S18

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
    st_line "STACK soft=$v hard=unlimited"
    st_ran suite
  done
  st_new S20b/131073-generic
  st_set_stack "$ST_REPO/$SCRIPT_REL" 131073
  st_run ST_UNAME=generic --
  st_rc zero
  st_line 'STACK soft=131073 hard=unlimited'
  st_row S20b

  # S21: a soft stack read back that differs from CUT_STACK_KIB fails; no test runs.
  st_new S21
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_run ST_SOFT=8192 --
  st_rc nonzero
  st_has 'the soft stack read back is 8192 KiB, not CUT_STACK_KIB=65536'
  st_not_ran
  st_row S21

  # S22: the fix commit of the row also set CUT_STACK_KIB; the parent of that commit holds no such line, so the
  # test runs at the default stack, and it still has to fail at its entry. The plain run of the same head (stack
  # 65536) is the control.
  for v in revert control; do
    st_new "S22/$v"
    printf '(* stand-in *)\n' >"$ST_REPO/tests/lean434_s.v"
    printf 'lean434_s.v\n' >>"$ST_REPO/tests/_CoqProject"
    st_commit "test s"
    parent=$(git -C "$ST_REPO" rev-parse HEAD)
    st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
    printf 'let fix_s = 1\n' >"$ST_REPO/src/fix_s.ml"
    st_commit "fix s, with a larger stack"
    st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" \
      "$(st_tsv tests/lean434_s.v F8 Sigma.one - fixed "$(git -C "$ST_REPO" rev-parse HEAD)")" >"$ST_REPO/$inv"
    st_commit "row s"
    if [[ $v == revert ]]; then
      st_run ST_OUTCOME=fail:Sigma.one -- --revert-fix tests/lean434_s.v
      st_rc zero
      st_line "R5 NEGATIVE MET: tests/lean434_s.v at Sigma.one (src/ of $parent)"
      st_line "$stack1"
      st_lacks 'soft=65536'
    else
      st_run --
      st_rc zero
      st_line 'STACK soft=65536 hard=unlimited'
    fi
  done
  st_row S22

  # S22b: the CUT_STACK_KIB that the parent of the row's first fix commit sets is the stack of the test, not the
  # one a later commit set at the head.
  st_new S22b
  printf '(* stand-in *)\n' >"$ST_REPO/tests/lean434_s.v"
  printf 'lean434_s.v\n' >>"$ST_REPO/tests/_CoqProject"
  st_set_stack "$ST_REPO/$SCRIPT_REL" 65536
  st_commit "test s, with a larger stack"
  parent=$(git -C "$ST_REPO" rev-parse HEAD)
  printf 'let fix_s = 1\n' >"$ST_REPO/src/fix_s.ml"
  st_commit "fix s"
  fix=$(git -C "$ST_REPO" rev-parse HEAD)
  st_set_stack "$ST_REPO/$SCRIPT_REL" 32768
  st_inventory "$ST_ROW_A" "$ST_ROW_B" "$ST_ROW_C" "$ST_ROW_OPT" "$(st_tsv tests/lean434_s.v F8 Sigma.one - fixed "$fix")" >"$ST_REPO/$inv"
  st_commit "row s, with a smaller stack"
  st_run ST_OUTCOME=fail:Sigma.one -- --revert-fix tests/lean434_s.v
  st_rc zero
  st_line "R5 NEGATIVE MET: tests/lean434_s.v at Sigma.one (src/ of $parent)"
  st_line 'STACK soft=65536 hard=unlimited'
  st_lacks 'soft=32768'
  st_row S22b

  # S23: --import and --check on a tree without history and with a broken inventory: a missing file, a
  # failing run, a normal run, the stack rules; no inventory check.
  st_new S23/setup
  plain=$ST_CASE/plain work=$ST_CASE/work
  cp -a -- "$ST_REPO" "$plain" && rm -rf -- "$plain/.git"
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
