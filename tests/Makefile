MAKE_OPTS:= --no-builtin-rules

# Extract the NDJSON archives once, before building the tests that import them.
# init and stdlib are Git LFS objects. The smaller strings archive is in Git.
DUMPS := ../dumps
EXPECTS = $(if $(or $(filter all,$(MAKECMDGOALS)),$(if $(MAKECMDGOALS),,all)),\
  $(wildcard *.expect),\
  $(wildcard $(patsubst %.vo,%.expect,$(filter %.vo,$(MAKECMDGOALS)))))

.PHONY: submake
submake: Makefile.rocq
	@for f in init stdlib lean434/strings; do \
	  test -f $(DUMPS)/$$f.ndjson || \
	    ( cd $(DUMPS) && python3 -c "from pathlib import Path; from zipfile import ZipFile; p = Path('$$f.ndjson.zip'); ZipFile(p).extractall(p.parent)" ) || exit; \
	done
	@status=0; $(MAKE) $(MAKE_OPTS) -f Makefile.rocq $(MAKECMDGOALS) || status=$$?; \
	expects=''; for spec in $(EXPECTS); do \
	  if [ $$status -eq 0 ] || [ -f "$${spec%.expect}.vo" ]; then expects="$$expects $$spec"; fi; \
	done; \
	if [ -n "$$expects" ]; then python3 check_expect.py $$expects || exit 1; fi; \
	exit $$status

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
