{ python312, graphviz, stdlib, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {
  pname = "stdlib-html";

  overrideBuildInputs = stdlib.buildInputs ++ [ python312 graphviz ];

  useDune = true;

  buildPhase = ''
    patchShebangs dev/with-rocq-wrap.sh
    dev/with-rocq-wrap.sh dune build @stdlib-html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '';

  installPhase = ''
    echo "nothing to install"
    touch $out
  '';
} stdlib
