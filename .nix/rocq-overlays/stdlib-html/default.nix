{ python312, graphviz, stdlib, lib }:

lib.overrideRocqDerivation {
  pname = "stdlib-html";

  overrideBuildInputs = stdlib.buildInputs ++ [ python312 graphviz ];

  useDune = true;

  buildPhase = ''
    dune build @stdlib-html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '';

  installPhase = ''
    echo "nothing to install"
    touch $out
  '';
} stdlib
