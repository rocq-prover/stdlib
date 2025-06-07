# CI job to test that we don't break the subcomponent structure of the stdlib,
# as described in the graph doc/stdlib/depends.dot

{ rocq-core, stdlib, rocqPackages }:

let
  # stdlib subcomponents with their dependencies
  # when editing this, ensure to keep doc/stdlib/depends.dot in sync
  components = {
    "corelib-wrapper" = [ ];
    "logic" = [ ];
    "relations" = [ "corelib-wrapper" ];
    "program" = [ "corelib-wrapper" "logic" ];
    "classes" = [ "program" "relations" ];
    "bool" = [ "classes" ];
    "structures" = [ "bool" ];
    "arith-base" = [ "structures" ];
    "positive" = [ "arith-base" ];
    "narith" = [ "ring" ];
    "zarith-base" = [ "narith-base" ];
    "narith-base" = [ "positive" ];
    "lists" = [ "arith-base" ];
    "ring" = [ "zarith-base" "lists" ];
    "arith" = [ "ring" ];
    "strings" = [ "arith" ];
    "lia" = [ "arith" "narith" ];
    "zarith" = [ "lia" ];
    "zmod" = [ "zarith" "sorting" "field" ];
    "qarith-base" = [ "ring" ];
    "field" = [ "zarith" ];
    "lqa" = [ "field" "qarith-base" ];
    "qarith" = [ "lqa" ];
    "classical-logic" = [ "arith" ];
    "sets" = [ "classical-logic" ];
    "vectors" = [ "lists" ];
    "sorting" = [ "lia" "sets" "vectors" ];
    "orders-ex" = [ "strings" "sorting" ];
    "unicode" = [ ];
    "primitive-int" = [ "unicode" "zarith" ];
    "primitive-floats" = [ "primitive-int" ];
    "primitive-array" = [ "primitive-int" ];
    "primitive-string" = [ "primitive-int" "orders-ex" ];
    "reals" = [ "qarith" "classical-logic" "vectors" ];
    "fmaps-fsets-msets" = [ "orders-ex" "zarith" ];
    "extraction" = [ "primitive-string" "primitive-array" "primitive-floats" ];
    "funind" = [ "arith-base" ];
    "wellfounded" = [ "lists" ];
    "streams" = [ "logic" ];
    "rtauto" = [ "positive" "lists" ];
    "compat" = [ "rtauto" "fmaps-fsets-msets" "funind" "extraction" "reals" "zmod" "wellfounded" "streams" ];
    "all" = [ "compat" ];
  };

  stdlib_ = component: let
    pname = "stdlib-${component}";
    stdlib-deps = map stdlib_ components.${component};
    in rocqPackages.lib.overrideRocqDerivation ({
      inherit pname;
      propagatedBuildInputs = stdlib-deps;
      mlPlugin = true;
    } // {
      buildPhase = ''
        make ''${enableParallelBuilding:+-j $NIX_BUILD_CORES} build-${component}
      '';
      installPhase = ''
        make COQLIBINSTALL=$out/lib/coq/${rocq-core.rocq-version}/user-contrib install-${component}
      '';
    }) stdlib;
in stdlib_ "all"
