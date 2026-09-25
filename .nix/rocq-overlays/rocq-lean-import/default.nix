{ mkCoqDerivation, python3, rocq-core, stdlib, version ? null }:

mkCoqDerivation {
  pname = "rocq-lean-import";
  inherit version;

  buildInputs = [ python3 rocq-core.ocamlPackages.yojson ];
  propagatedBuildInputs = [ stdlib ];

  mlPlugin = true;

  configurePhase = ''
    export COQEXTRAFLAGS='-native-compiler no'
  '';

  # broken since it uses git-lfs, c.f., https://github.com/rocq-prover/rocq/pull/22474
  # buildFlags = [ "test" ];
}
