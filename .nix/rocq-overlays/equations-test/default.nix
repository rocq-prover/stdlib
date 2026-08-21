{ mkCoqDerivation, equations, version ? null }:

mkCoqDerivation {
  pname = "equations-test";
  repo = "Coq-Equations";
  owner = "mattam82";
  inherit version;

  propagatedBuildInputs = [ equations ];

  mlPlugin = true;

  useDune = true;

  buildPhase = ''
    dune build -p rocq-equations-tests,rocq-equations-examples
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
