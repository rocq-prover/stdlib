{ lib, mkCoqDerivation, coq, iris, autosubst, version ? null }:

mkCoqDerivation {
  pname = "iris-examples";
  domain = "gitlab.mpi-sws.org";
  owner = "iris";
  repo = "examples";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ iris autosubst ];

  preBuild = ''
    if [[ -f rocq-lint.sh ]]
    then patchShebangs rocq-lint.sh
    fi
  '';
}
