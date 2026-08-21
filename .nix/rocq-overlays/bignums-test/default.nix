{ mkCoqDerivation, bignums, version ? null }:

mkCoqDerivation {
  pname = "bignums-test";
  repo = "bignums";
  owner = "coq";
  inherit version;

  mlPlugin = true;

  propagatedBuildInputs = [ bignums ];

  buildPhase = ''
    cd tests
    make
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
