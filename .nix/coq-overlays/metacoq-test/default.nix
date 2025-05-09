{ mkCoqDerivation, metacoq, version ? null }:

mkCoqDerivation {
  pname = "metacoq-test";
  repo = "metarocq";
  owner = "MetaRocq";
  inherit version;

  mlPlugin = true;

  propagatedBuildInputs = [ metacoq ];

  configurePhase = ''
    patchShebangs ./configure.sh
    ./configure.sh
  '';

  buildFlags = [ "-C" "test-suite" ];

  installPhase = ''
    echo "nothing to install"
  '';
}
