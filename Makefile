DUNE=dev/with-rocq-wrap.sh dune

.PHONY: clean all install dune dune-install

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

clean:
	rm -rf _build
	find . \
	\( -name '*.vo' \
	-o -name '*.vok' \
	-o -name '*.vos' \
	-o -name '*.glob' \
	\) -exec rm -vf {} +
