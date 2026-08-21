{ lib, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "neural-net-coq-interp";
  owner = "JasonGross";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  buildFlags = [ "coq-ci-target" ];

  installPhase = "make install || true";
}
