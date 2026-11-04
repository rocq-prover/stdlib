{ python312, graphviz, stdlib, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {
  pname = "stdlib-html";

  overrideBuildInputs = stdlib.buildInputs ++ [ python312 graphviz ];

  useDune = true;

  buildPhase = ''
    dune build @stdlib-html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '';

  installPhase = ''
    echo "nothing to install"
    mkdir $out
  '';
} stdlib
