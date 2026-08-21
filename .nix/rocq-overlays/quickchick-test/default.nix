{ time, python3, mkCoqDerivation, coq, QuickChick, version ? null }:

mkCoqDerivation {
  pname = "quickchick-test";
  repo = "QuickChick";
  owner = "QuickChick";
  inherit version;

  nativeBuildInputs = [ time python3 ]
    ++ (with coq.ocamlPackages; [ cppo menhir ]);
  propagatedBuildInputs = [ QuickChick ];

  useDune = true;

  buildPhase = ''
    dune build -p coq-quickchick @runtest @cram --stop-on-first-error
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
