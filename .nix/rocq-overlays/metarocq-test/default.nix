{ mkCoqDerivation, metarocq, version ? null }:

mkCoqDerivation {
  pname = "metarocq-test";
  repo = "metarocq";
  owner = "MetaRocq";
  inherit version;

  mlPlugin = true;

  propagatedBuildInputs = [ metarocq ];

  configurePhase = ''
    patchShebangs ./configure.sh
    ./configure.sh
  '';

  buildFlags = [ "-C" "test-suite" ];

  installPhase = ''
    echo "nothing to install"
  '';
}
