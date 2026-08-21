let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

{ lib, python3, mkCoqDerivation, coq, stdlib, version ? null }@args:

mkCoqDerivation {
  pname = "fiat-parsers";
  repo = "fiat";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  nativeBuildInputs = [ python3 ];
  propagatedBuildInputs = [ stdlib ];

  mlPlugin = true;

  buildFlags = [ "parsers" "parsers-examples" "fiat-core" ];

  preBuild = ''
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
    for f in $(find . -name "*.py") ; do patchShebangs $f ; done
  '';

  installPhase = ''
    echo "not installing anything"
  '';
}
