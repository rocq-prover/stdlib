{ lib, time, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "coq-performance-tests";
  owner = "coq-community";
  inherit version;
  defaultVersion = let inherit (lib.versions) range; in
    lib.switch coq.coq-version [
      { case = range "8.19" "8.19"; out = "1.0.1"; }
    ] null;
  release = {
    "1.0.1".sha256  = "sha256-2hHKr6dnxwMCsJtBSIgiIhUfcFcAuzQbP5R2oLXvThU=";
  };
  releaseRev = v: "v${v}";

  mlPlugin = true;

  nativeBuildInputs = [ time ];
  propagatedBuildInputs = [ stdlib ];

  preConfigure = ''
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
  '';

  buildPhase = ''
    make coq perf-Sanity
    make validate
  '';

  meta = {
    description = "A library of Coq source files testing for performance regressions on Coq";
    license = lib.licenses.mit;
  };
}
