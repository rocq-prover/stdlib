ROCQBIN?=$(dir $(shell command -v rocq))
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=

.PHONY: all
all: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS)

.PHONY: install
install: Makefile.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) install

Makefile.coq: _CoqProject
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< $(shell find . -name "*.v") -o $@

build-%: Makefile-%.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS)

Makefile-%.coq: Make.%
	for f in $$(cat $< | sed -e 's/#.*//;s/-.*//' | grep -v '^[ \t]*$$') ; do \
	  d=$$(dirname $${f}) ; \
	  if [ $${d%/_*} != $${d} ] ; then \
	    mkdir -p $${d} ; \
	    ln -sf ../$$(basename $${f}) $${d} ; \
	  fi ; \
	done
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< -o $@

install-%: Makefile-%.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) install

%.vo: Makefile.coq %.v
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) $@

clean: Makefile.coq
	+$(MAKE) -f $< clean
	# for subcomponent builds:
	find . \
	\( -name '*.vo' \
	-o -name '*.vok' \
	-o -name '*.vos' \
	-o -name '*.glob' \
	\) -exec rm -vf {} +
