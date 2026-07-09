ROCQBIN?=$(dir $(shell command -v rocq))
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=

.PHONY: all install clean
all install: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@

clean: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@
	rm -f _CoqProject

_CoqProject: gen_CoqProject.sh rocq-flags.conf
	./$< > $@

Makefile.coq: _CoqProject
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< $(shell find . -regex ".*/[^.][^/]*[.]v" -not -name All.v) -o $@

%.vo: Makefile.coq %.v
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@
