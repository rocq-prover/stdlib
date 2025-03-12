{ mkRocqDerivation, rocq-elpi, stdlib, version ? null }:

mkRocqDerivation {
  pname = "rocq-elpi-test";
  repo = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  propagatedBuildInputs = [ rocq-elpi stdlib ];

  useDune = true;

  configurePhase = ''
    export COQPATH=''${ROCQPATH}
    patchShebangs etc/with-rocq-wrap.sh
  '';

  buildPhase = ''
    export DUNE_build_FLAGS="--release"
    make -j1 all-tests
    make -j1 all-examples
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
