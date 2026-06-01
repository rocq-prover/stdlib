{ bash, stdlib, rocqPackages }:

rocqPackages.lib.overrideRocqDerivation {

  pname = "stdlib-all";

  propagatedBuildInputs = [ bash ];

  buildPhase = ''
    patchShebangs theories/All.sh
    patchShebangs dev/tools/check-all.sh
    echo "Check that theories/All.v is up to date:"
    dev/tools/check-all.sh
  '';

  installPhase = ''
    echo "nothing to install"
  '';
} stdlib
