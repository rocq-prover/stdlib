{ antlr4_9, python311, rocq-core, stdlib, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {
  pname = "stdlib-refman-html";

  overrideBuildInputs = stdlib.buildInputs
  ++ [ rocq-core.ocamlPackages.ocaml rocq-core.ocamlPackages.dune_3 stdlib ]
  ++ [
    # Sphinx doc dependencies
    (python311.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             (ps.antlr4-python3-runtime.override {antlr4 = antlr4_9;}) ps.sphinxcontrib-bibtex ]))
    antlr4_9
  ];

  useDune = true;

  buildPhase = ''
    patchShebangs dev/with-rocq-wrap.sh
    dev/with-rocq-wrap.sh dune build --root . --no-buffer @refman-html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '';

  installPhase = ''
    echo "nothing to install"
    touch $out
  '';

  fixupPhase = ''
    echo "nothing to fixup"
  '';
} stdlib
