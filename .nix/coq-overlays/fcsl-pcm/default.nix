{ lib, mkCoqDerivation, coq, mathcomp-algebra, stdlib, version ? null }:

mkCoqDerivation {
  pname = "fcsl-pcm";
  owner = "imdea-software";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ mathcomp-algebra stdlib ];
}
