DUNE=dev/with-rocq-wrap.sh dune

.PHONY: clean all install dune dune-install test-suite

all install:
	+$(MAKE) -j -C theories $@

dune:
	$(DUNE) build -p rocq-stdlib @install

dune-install:
	$(DUNE) install --root . rocq-stdlib

build-% install-%:
	+$(MAKE) -C theories $@

# Make of individual .vo
theories/%.vo:
	+$(MAKE) -C theories $*.vo

refman-html:
	$(DUNE) build --root . --no-buffer @refman-html

stdlib-html:
	$(DUNE) build --root . @stdlib-html

test-suite:
	test -d _build/default/theories/
	+COQEXTRAFLAGS="-Q ../_build/default/theories/ Stdlib" \
	COQCHKEXTRAFLAGS="$$COQEXTRAFLAGS" \
	$(MAKE) -C test-suite

clean:
	+$(MAKE) -C theories clean
