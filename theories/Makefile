ROCQBIN?=$(dir $(shell command -v rocq))
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=

.PHONY: all install clean
all install clean: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@

Makefile.coq: _CoqProject
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< $(shell find . -regex ".*/[^.][^/]*[.]v") -o $@

%.vo: Makefile.coq %.v
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@
