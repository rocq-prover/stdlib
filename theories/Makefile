ROCQBIN?=$(dir $(shell command -v rocq))
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=
ROCQSOURCES?=$(shell find . -regex ".*/[^.][^/]*[.]v" -not -name All.v)

.PHONY: all install clean
all install clean: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@

Makefile.coq: _CoqProject
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< $(ROCQSOURCES) -o $@

%.vo: Makefile.coq %.v
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@
