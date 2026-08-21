{ lib, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "engine-bench";
  owner = "mit-plv";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  buildPhase = ''
    make coq
    make coq-perf-Sanity
  '';
}
