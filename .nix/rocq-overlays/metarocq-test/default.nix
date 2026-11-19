{ mkCoqDerivation, metarocq, version ? null }:

mkCoqDerivation {
  pname = "metarocq-test";
  repo = "metarocq";
  owner = "MetaRocq";
  inherit version;

  mlPlugin = true;

  propagatedBuildInputs = [ metarocq ];

  useDune = true;

  configurePhase = ''
    echo no configuration
  '';

  buildPhase = ''
    dune build ''${enableParallelBuilding:+-j $NIX_BUILD_CORES} @runtest
  '';

  installPhase = ''
    echo installing nothing
    # Make an output directory rather than a file, so this is more friendly to buildEnv
    mkdir $out
  '';
}
