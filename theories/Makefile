ROCQBIN?=$(dir $(shell command -v rocq))
ROCQFIND?=$(ROCQBIN)rocq find
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=
ROCQSOURCES?=$(shell find . -regex ".*/[^.][^/]*[.]v" -not -name All.v)

# Move these options to _CoqProject when requiring rocq-core >= 9.3.
ROCQPACKAGEOPTIONS?=--rocq-package rocq-stdlib -package rocq-core --legacy-support --description "Rocq standard library"

.PHONY: all install clean
all install clean: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@

# The second branch can be removed when requiring rocq-core >= 9.3.
Makefile.coq: _CoqProject
ifeq ($(shell rocq find > /dev/null 2> /dev/null; echo "$$?"),0)
	$(ROCQMAKEFILE) $(ROCQPACKAGEOPTIONS) $(ROCQMAKEFILEOPTIONS) -f $< $(ROCQSOURCES) -o $@
else
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< $(ROCQSOURCES) -o $@
endif

%.vo: Makefile.coq %.v
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@
