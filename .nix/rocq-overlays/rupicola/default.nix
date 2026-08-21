let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = if owner == "mit-plv" then "https://${domain}/${owner}/fiat-crypto"
        else "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

{ lib, mkCoqDerivation, coq, coqutil, bedrock2, version ? null }@args:

mkCoqDerivation {
  pname = "rupicola";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ coqutil bedrock2 ];

  makeFlags = [ "EXTERNAL_COQUTIL=1" "EXTERNAL_BEDROCK2=1" ];

  preBuild = "cd rupicola || true";
}
