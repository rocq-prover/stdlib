{ lib, mkCoqDerivation, unicoq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "Mtac2";
  owner = "Mtac2";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ unicoq stdlib ];

  mlPlugin = true;

  preBuild = ''
    coq_makefile -f _CoqProject -o Makefile
    patchShebangs tests/sf-5/configure.sh
  '';
}
