{ mkCoqDerivation, stdlib, version ? null }:

mkCoqDerivation {
  pname = "rocq-lean-import";
  inherit version;

  propagatedBuildInputs = [ stdlib ];

  mlPlugin = true;

  buildFlags = [ "test" ];
}
