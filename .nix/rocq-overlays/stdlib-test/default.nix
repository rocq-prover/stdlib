{ rsync, rocq-core, stdlib, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {

  pname = "stdlib-test";

  propagatedBuildInputs = [ rsync stdlib ]
    ++ (with rocq-core.ocamlPackages; [ ocaml findlib zarith ]);

  useDune = false;

  buildPhase = ''
    cd test-suite
    make -j $NIX_BUILD_CORES
  '';

  installPhase = ''
    echo "nothing to install"
  '';
} stdlib
