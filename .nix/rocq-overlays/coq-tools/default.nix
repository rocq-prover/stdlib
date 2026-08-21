{ lib, bash, python3, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "coq-tools";
  owner = "JasonGross";
  inherit version;
  defaultVersion = null;  # no released version

  nativeBuildInputs = [ bash python3 ];
  propagatedBuildInputs = [ stdlib ];

  preConfigure = ''
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
    for f in $(find . -name "*.py") ; do patchShebangs $f ; done
    export ROCQPATH=''${COQPATH}
    unset COQPATH
  '';

  buildFlags = [ "check" ];

  installPhase = ''
    echo "nothing to install"
    mkdir -p $out
  '';
}
