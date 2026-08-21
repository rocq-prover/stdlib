{ lib, mkCoqDerivation, coq, stdlib, version ? null }:

let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

mkCoqDerivation {
  pname = "argosy";
  owner = "mit-pdos";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  preConfigure = ''
    sed -i vendor/classes/src/EqualDec.v -e 's/ZArith.ZArith/ZArith/'
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
  '';

  installPhase = ''
    echo "no install target"
  '';
}
