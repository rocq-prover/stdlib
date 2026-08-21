{ lib, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "sf";
  owner = "DeepSpec";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  buildPhase = ''
    ( cd lf-current
      make
    )

    ( cd plf-current
      make
    )

    ( cd vfa-current
      make
    )

    ( cd slf-current
      make
    )
  '';

  installPhase = "";
}
