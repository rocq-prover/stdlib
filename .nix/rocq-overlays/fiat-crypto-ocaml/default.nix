let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

{ lib, python3, mkCoqDerivation, coq, fiat-crypto, version ? null }@args:

mkCoqDerivation {
  pname = "fiat-crypto-ocaml";
  repo = "fiat-crypto";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  nativeBuildInputs = [ python3 ];
  propagatedBuildInputs = [ fiat-crypto ];

  mlPlugin = true;

  makeFlags = [ "EXTERNAL_DEPENDENCIES=1" "OCAMLFIND=ocamlfind" ];

  preBuild = ''
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
    for f in $(find . -name "*.py") ; do patchShebangs $f ; done
  '';

  buildFlags = [ "lite-c-files" ];

  installPhase = ''
    echo "not installing anything"
  '';
}
