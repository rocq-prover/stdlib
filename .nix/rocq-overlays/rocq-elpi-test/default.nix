{ mkRocqDerivation, rocq-elpi, version ? null }:

mkRocqDerivation {
  pname = "rocq-elpi-test";
  repo = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  propagatedBuildInputs = [ rocq-elpi ];

  useDune = true;

  buildPhase = ''
    export DUNE_build_FLAGS="--release"
    make -j1 all-tests
    make -j1 all-examples
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
