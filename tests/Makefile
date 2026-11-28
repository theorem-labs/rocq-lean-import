MAKE_OPTS:= --no-builtin-rules

# Extract the NDJSON archives once, before building the tests that import them.
# init and stdlib are Git LFS objects. The smaller strings archive is in Git.
DUMPS := ../dumps

# The tests whose Redirect logs <test>.expect checks (check_expect.py): after each make of such a test, its
# .expect is checked, and a missing or empty one fails. Every .expect file must belong to a test named here.
# A test whose Redirect logs nothing checks has no .expect: for example path_deferred_saved.v, the library
# tests/path_deferred_reload.v loads, lean434_stack.v, whose log only ci/build-9.2-cut.sh --revert-fix reads, and
# the tests of the base.
EXPECT_TESTS := entry_memory entry_timeout entry_timeout_parse fin_transport_bitwise fin_transport_bitwise_absent \
  fin_transport_budget_name \
  fin_transport_ceiling fin_transport_charge fin_transport_lemma_refused fin_transport_nest fin_transport_refused \
  fin_transport_shape fin_transport_share \
  fin_transport_values fin_transport_values_differ lean434_bigint_decide lean434_string_length lean434_strings \
  litarith_absent litarith_budget litarith_chain litarith_dvd litarith_eval litarith_hold litarith_nobool litarith_refused \
  nat_transport nat_transport_budget nat_transport_parts nat_transport_step_budget \
  nat_transport_total negative_controls parse_text_numbering parse_text_recovery parse_text_recovery_prefix \
  parse_unclear_id parse_untagged parse_untagged_prefix parse_wrong_payload parse_wrong_payload_prefix path_choice \
  path_deferred_legacy path_deferred_reload path_deferred_string predeclared relcast relcast_absent relcast_depth \
  relcast_lemma relcast_refused rocqchk_literal_below \
  rocqchk_literal_text string_literal_mk uint32_legacy_only \
  transport_walk transport_work uint32_transport_ofnatlt uint32_transport_shiftleft univ_undeclared \
  utf8size_transport_one utf8size_transport_two
# The tests of the list $(1) that this make's goals build: all of them for the goal all or for no goal, else
# those a goal names as <test>.vo. EXPECTS and ROCQCHKS share it.
goal_tests = $(if $(or $(filter all,$(MAKECMDGOALS)),$(if $(MAKECMDGOALS),,all)),\
  $(1),\
  $(filter $(patsubst %.vo,%,$(filter %.vo,$(MAKECMDGOALS))),$(1)))
EXPECTS = $(addsuffix .expect,$(call goal_tests,$(EXPECT_TESTS)))
UNLISTED_EXPECTS = $(filter-out $(EXPECT_TESTS:=.expect),$(wildcard *.expect))

# The tests whose .vo the suite checks with rocqchk (the cut's on CI) after the make, because Lean Import stores the
# importer's state in the .vo, which rocqchk must read (src/lean.ml, lean_obj, says what it cannot read). After each
# make of such a test (the goals of EXPECTS), rocqchk checks its .vo with the load path of tests/_CoqProject and the
# flags of ci/build-9.2-cut.sh --check, its output in <test>.rocqchk.log. A failure prints "ROCQCHK FAIL:
# tests/<test>.vo: <the log's first line that is not blank>" and fails the make; a test of the list whose .vo a make
# that passed did not write prints "ROCQCHK MISSING: tests/<test>.vo: ..." and fails it. ci/build-9.2-cut.sh
# (rocqchk_tests) reads this list for the inventory's check:rocqchk rows: the line "ROCQCHK_TESTS :=" and the lines
# a trailing backslash continues it with, and no other assignment to ROCQCHK_TESTS.
ROCQCHK_TESTS := core lean434_bigint rocqchk_literal rocqchk_literal_below rocqchk_literal_over rocqchk_literal_text
ROCQCHKS = $(call goal_tests,$(ROCQCHK_TESTS))

# Rocq's makefile compiles each test (its .vo, .vos and .vok rules) with $(ROCQ) compile. check_expect.py --rocq
# runs that command after it deletes the logs of the test it compiles, so a log only an earlier compile wrote
# cannot satisfy an assertion; a make that compiles nothing keeps the logs.
.PHONY: submake
submake: Makefile.rocq
	@for f in init stdlib lean434/strings; do \
	  test -f $(DUMPS)/$$f.ndjson || \
	    ( cd $(DUMPS) && python3 -m zipfile -e $$f.ndjson.zip $$(dirname $$f) ) || exit; \
	done
	@status=0; failed=0; \
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq ROCQ='python3 check_expect.py --rocq $(COQBIN)rocq' $(MAKECMDGOALS) || status=$$?; \
	expects=''; for spec in $(EXPECTS); do \
	  if [ $$status -eq 0 ] || [ -f "$${spec%.expect}.vo" ]; then expects="$$expects $$spec"; fi; \
	done; \
	if [ -n "$$expects" ]; then python3 check_expect.py $$expects || failed=1; fi; \
	for t in $(ROCQCHKS); do \
	  if [ -f "$$t.vo" ]; then \
	    $(COQBIN)rocqchk -silent -o -Q ../src LeanImport -R . Test Test.$$t > "$$t.rocqchk.log" 2>&1 || { \
	      first=$$(sed -n '/[^[:space:]]/{p;q;}' "$$t.rocqchk.log"); \
	      echo "ROCQCHK FAIL: tests/$$t.vo: $${first:-no output}" >&2; failed=1; }; \
	  elif [ $$status -eq 0 ]; then \
	    echo "ROCQCHK MISSING: tests/$$t.vo: no such file after the make (is $$t.v in tests/_CoqProject?)" >&2; failed=1; \
	  fi; \
	done; \
	for spec in $(UNLISTED_EXPECTS); do \
	  echo "EXPECT FAIL: tests/$$spec: its test is not in EXPECT_TESTS of tests/Makefile" >&2; failed=1; \
	done; \
	if [ $$status -eq 0 ]; then status=$$failed; fi; \
	exit $$status

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
