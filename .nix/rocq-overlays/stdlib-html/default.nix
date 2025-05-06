{ graphviz, stdlib, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {
  pname = "stdlib-html";

  overrideBuildInputs = stdlib.buildInputs ++ [ graphviz ];

  useDune = true;

  buildPhase = ''
    patchShebangs dev/with-rocq-wrap.sh
    patchShebangs doc/stdlib/make-library-index
    dev/with-rocq-wrap.sh dune build @stdlib-html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
    # check that the make-depend script still runs
    patchShebangs dev/tools/make-depends.sh
    dev/tools/make-depends.sh
  '';

  installPhase = ''
    echo "nothing to install"
    touch $out
  '';
} stdlib
