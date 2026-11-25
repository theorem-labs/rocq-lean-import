MAKE_OPTS:= --no-builtin-rules

# Extract the NDJSON archives once, before building the tests that import them.
# init and stdlib are Git LFS objects. The smaller strings archive is in Git.
DUMPS := ../dumps

# The tests whose Redirect logs <test>.expect checks (check_expect.py): after each make of such a test, its
# .expect is checked, and a missing or empty one fails. Every .expect file must belong to a test named here.
# A test whose Redirect logs nothing checks (path_deferred_saved.v, the library tests/path_deferred_reload.v
# loads, and the tests of the base) has no .expect.
EXPECT_TESTS := entry_memory entry_timeout entry_timeout_parse lean434_bigint_decide lean434_string_length \
  lean434_strings nat_transport nat_transport_budget negative_controls parse_text_numbering parse_text_recovery \
  parse_text_recovery_prefix parse_unclear_id parse_untagged parse_untagged_prefix parse_wrong_payload \
  parse_wrong_payload_prefix path_choice path_deferred_legacy path_deferred_reload path_deferred_string \
  predeclared string_literal_mk uint32_legacy_only uint32_transport_ofnatlt uint32_transport_shiftleft \
  univ_undeclared
EXPECTS = $(addsuffix .expect,$(if $(or $(filter all,$(MAKECMDGOALS)),$(if $(MAKECMDGOALS),,all)),\
  $(EXPECT_TESTS),\
  $(filter $(patsubst %.vo,%,$(filter %.vo,$(MAKECMDGOALS))),$(EXPECT_TESTS))))
UNLISTED_EXPECTS = $(filter-out $(EXPECT_TESTS:=.expect),$(wildcard *.expect))

# Rocq's makefile compiles each test (its .vo, .vos and .vok rules) with $(ROCQ) compile. check_expect.py --rocq
# runs that command after it deletes the logs of the test it compiles, so a log only an earlier compile wrote
# cannot satisfy an assertion; a make that compiles nothing keeps the logs.
.PHONY: submake
submake: Makefile.rocq
	@for f in init stdlib lean434/strings; do \
	  test -f $(DUMPS)/$$f.ndjson || \
	    ( cd $(DUMPS) && python3 -c "from pathlib import Path; from zipfile import ZipFile; p = Path('$$f.ndjson.zip'); ZipFile(p).extractall(p.parent)" ) || exit; \
	done
	@status=0; failed=0; \
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq ROCQ='python3 check_expect.py --rocq $(COQBIN)rocq' $(MAKECMDGOALS) || status=$$?; \
	expects=''; for spec in $(EXPECTS); do \
	  if [ $$status -eq 0 ] || [ -f "$${spec%.expect}.vo" ]; then expects="$$expects $$spec"; fi; \
	done; \
	if [ -n "$$expects" ]; then python3 check_expect.py $$expects || failed=1; fi; \
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
