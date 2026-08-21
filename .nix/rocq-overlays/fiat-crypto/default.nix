let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

{ lib, python3, mkCoqDerivation, coq, coqprime, rewriter, rupicola, version ? null }@args:

mkCoqDerivation {
  pname = "fiat-crypto";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  nativeBuildInputs = [ python3 ];
  propagatedBuildInputs = [ coqprime rewriter rupicola ];

  mlPlugin = true;

  makeFlags = [ "EXTERNAL_REWRITER=1" "EXTERNAL_COQPRIME=1" "EXTERNAL_COQUTIL=1" "EXTERNAL_BEDROCK2=1" ];

  preBuild = ''
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
    for f in $(find . -name "*.py") ; do patchShebangs $f ; done
  '';

  buildFlags = [ "pre-standalone-extracted" "printlite" "lite" "check-output" ];

  installPhase = ''
    echo "not installing anything"
  '';
}
