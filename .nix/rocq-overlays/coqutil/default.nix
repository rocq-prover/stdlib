let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    let submodules = owner == "mit-plv"; in
    fetchGit {
      url = if submodules then "https://${domain}/${owner}/fiat-crypto"
        else "https://${domain}/${owner}/${repo}";
      ref = rev;
      inherit submodules;
    };
in

{ lib, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "coqutil";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  preBuild = "cd rupicola/bedrock2/deps/coqutil || true";
}
