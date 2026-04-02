with builtins; with (import <nixpkgs> {}).lib; {
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "stdlib";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  coqproject = "theories/_CoqProject";

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  # cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  cachix.coq.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "rocq-9.2";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles = let
    ## In some cases, light overrides are not available/enough
    ## in which case you can use either
    # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
    ## or a "long" overlay to put in `.nix/coq-overlays
    ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
    ## to automatically retrieve the one from nixpkgs
    ## if it exists and is correctly named/located

    ## You can override Coq and other coqPackages
    ## through the following attribute
    ## If <ocaml-pkg> does not support light overrides,
    ## you may use `overrideAttrs` or long overlays
    ## located in `.nix/ocaml-overlays`
    ## (there is no automation for this one)
    #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

    ## You can also override packages from the nixpkgs toplevel
    # <nix-pkg>.override.overrideAttrs = o: <overrides>;
    ## Or put an overlay in `.nix/overlays`

    ## you may mark a package as a main CI job (one to take deps and
    ## rev deps from) as follows
    # coqPackages.<main-pkg>.main-job = true;
    ## by default the current package and its shell attributes are main jobs

    ## you may mark a package as a CI job as follows
    #  coqPackages.<another-pkg>.job = "test";
    ## It can then built through
    ## nix-build --argstr bundle "default" --arg job "test";
    ## in the absence of such a directive, the job "another-pkg" will
    ## is still available, but will be automatically included in the CI
    ## via the command genNixActions only if it is a dependency or a
    ## reverse dependency of a job flagged as "main-job" (see above).

    ## Run on push on following branches (default [ "master" ])
    # push-branches = [ "master" "branch2" ];

    rocq-master = [
      "bignums"
    ];
    master = [
      "aac-tactics"
      "argosy"
      "atbr"
      "autosubst"
      "bedrock2"
      "bignums"
      "bignums-test"
      "category-theory"
      "coinduction"
      "CoLoR"
      "compcert"
      "coqprime"
      "coquelicot"
      "coqutil"
      "ExtLib"
      "coq-hammer"
      "coq-hammer-tactics"
      "coq-performance-tests"
      # "coq-tools"  # overlay
      "corn"
      "deriving"
      "engine-bench"
      "fcsl-pcm"
      "fiat-crypto"
      "fiat-crypto-ocaml"
      "fiat-parsers"
      "flocq"
      "hierarchy-builder"
      "iris"
      "iris-examples"
      "itauto"
      "ITree"
      "mathcomp-analysis"
      "mathcomp-reals"
      "mathcomp-zify"
      "math-classes"
      "MenhirLib"
      "mtac2"
      "neural-net-coq-interp"
      "paco"
      "paramcoq-test"
      "QuickChick"
      "quickchick-test"
      "relation-algebra"
      "rewriter"
      "rocq-lean-import"
      "rupicola"
      "sf"
      "simple-io"
      "stalmarck-tactic"
      "stdpp"
      "trakt"
      "unicoq"
      "VST"
    ];
    coq-master = [
      "dpdgraph-test"
      "waterproof"
    ];
    main = [
      "equations"
      "equations-test"
      "jasmin"
      "mathcomp-word"
      "metarocq"
      "metarocq-test"
    ];
    # To lighten the CI on released version, don't test reverse dependencies
    # of Stdlib that take >= 5 min of CI (and their reverse dependencies)
    lighten-released = [
      "bedrock2"
      "category-theory"
      "CoLoR"
      "coq-performance-tests"
      "coq-tools"
      "corn"
      "engine-bench"
      "fiat-crypto"
      "fiat-crypto-ocaml"
      "iris"
      "iris-examples"
      "jasmin"
      "metacoq"
      "metacoq-common"
      "metacoq-erasure"
      "metacoq-erasure-plugin"
      "metacoq-pcuic"
      "metacoq-quotation"
      "metacoq-safechecker"
      "metacoq-safechecker-plugin"
      "metacoq-template-coq"
      "metacoq-template-pcuic"
      "metacoq-translations"
      "metacoq-utils"
      "metarocq"
      "metarocq-common"
      "metarocq-erasure"
      "metarocq-erasure-plugin"
      "metarocq-pcuic"
      "metarocq-quotation"
      "metarocq-safechecker"
      "metarocq-safechecker-plugin"
      "metarocq-template-pcuic"
      "metarocq-template-rocq"
      "metarocq-test"
      "metarocq-utils"
      "rewriter"
      "rupicola"
    ];
    coq-common-bundles = listToAttrs (forEach rocq-master (p:
      { name = p; value.override.version = "master"; }))
    // listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // listToAttrs (forEach coq-master (p:
      { name = p; value.override.version = "coq-master"; }))
    // listToAttrs (forEach main (p:
      { name = p; value.override.version = "main"; }))
    // {
      coq-tools.override.version = "proux01:coq_19955";
      stdlib-html.job = true;
      stdlib-refman-html.job = true;
      rocq-elpi.job = true;
      iris-examples.job = false;  # Currently broken
      CakeMLExtraction.job = false;  # not in Rocq CI
      ceres.job = false;  # not in Rocq CI
      ceres-bs.job = false;  # not in Rocq CI
      CertiRocq.job = false;  # not in Rocq CI
      ConCert.job = false;  # not in Rocq CI
      coqeal.job = false;  # not in Rocq CI
      ElmExtraction.job = false;  # not in Rocq CI
      extructures.job = false;  # not in Rocq CI
      gaia.job = false;  # not in Rocq CI
      graph-theory.job = false;  # not in Rocq CI
      json.job = false;  # not in Rocq CI
      libvalidsdp.job = false;  # not in Rocq CI
      Ordinal.job = false;  # not in Rocq CI
      parsec.job = false;  # not in Rocq CI
      RustExtraction.job = false;  # not in Rocq CI
      interval.job = false;  # not in Rocq CI
      parseque.job = false;  # not in Rocq CI
      LibHyps.job = false;  # not in Rocq CI
      reglang.job = false;  # not in Rocq CI
      ssprove.job = false;  # not in Rocq CI
      # smtcoq.override.version = "rocq-master";  # can't use rocq-master above as it isn't actually a rocq package yet
      TypedExtraction.job = false;  # not in Rocq CI
      TypedExtraction-common.job = false;  # not in Rocq CI
      TypedExtraction-elm.job = false;  # not in Rocq CI
      TypedExtraction-plugin.job = false;  # not in Rocq CI
      TypedExtraction-rust.job = false;  # not in Rocq CI
      validsdp.job = false;  # not in Rocq CI
      verified-extraction.job = false;  # not in Rocq CI
      wasmcert.job = false;  # not in Rocq CI
      hierarchy-builder.job = false;  # not a reverse dependency of Stdlib
      mathcomp-order.job = false;  # not a reverse dependency of Stdlib
      mathcomp-fingroup.job = false;  # not a reverse dependency of Stdlib
      mathcomp-algebra.job = true;  # dependency of analysis
      mathcomp-solvable.job = false;  # not a reverse dependency of Stdlib
      mathcomp-character.job = false;  # not a reverse dependency of Stdlib
      mathcomp-field.job = true;  # dependency of analysis
      mathcomp.job = false;  # not a reverse dependency of Stdlib
      # To add a simple overlay applying to all bundles,
      # add, just below this comment, a line like
      #<package>.override.version = "<github_login>:<branch>";
      # where
      # * <package> will typically be one of the strings above (without the quotes)
      #   or look at https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules
      #   for a complete list of Coq packages available in Nix
      # * <github_login>:<branch> is such that this will use the branch <branch>
      #   from https://github.com/<github_login>/<repository>
      bedrock2.override.version = "proux01:stdlib251";
      coq-elpi.override.version = "proux01:stdlib251";
      coqutil.override.version = "proux01:stdlib251";
      itauto.override.version = "proux01:stdlib251";
      equations.override.version = "proux01:stdlib251";
      equations-test.override.version = "proux01:stdlib251";
      smtcoq.override.version = "proux01:stdlib251";
      metarocq.override.version = "proux01:stdlib251";
      metarocq-test.override.version = "proux01:stdlib251";
      waterproof.override.version = "proux01:stdlib251";
      sf.job = false;  # temporarily disactivated in Rocq CI
    };
    common-bundles = listToAttrs (forEach rocq-master (p:
      { name = p; value.override.version = "master"; }))
    // {
      micromega-plugin.override.version = "tify";
      rocq-elpi.override.version = "proux01:stdlib251";
      rocq-elpi-test.override.version = "proux01:stdlib251";
    };
  in {
    "rocq-master" = { rocqPackages = common-bundles // {
      rocq-core.override.version = "master";
      stdlib-test.job = true;
      rocq-elpi.override.version = "master";
      # rocq-elpi-test.override.version = "master";
      rocq-elpi-test.override.version = "proux01:stdlib251";
      hierarchy-builder.override.version = "master";
      # micromega-plugin.override.version = "master";
      micromega-plugin.override.version = "tify";
      micromega-plugin.job = false;
      mathcomp.override.version = "master";
      mathcomp-bigenough.override.version = "master";
      mathcomp-finmap.override.version = "master";
      stdlib-all.job = true;  # check that theories/All.v is up to date
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "master";
      coq-elpi.override.version = "master";
      hierarchy-builder.override.version = "master";
      mathcomp.override.version = "master";
      mathcomp-bigenough.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp-algebra-tactics.job = false;  # no longer in Rocq CI since Rocq 9.3
    }; };
    "rocq-9.3" = { rocqPackages = common-bundles // {
      rocq-core.override.version = "9.3";
      # check that we compile without warnings on last release of Rocq
      stdlib-warnings.job = true;
      rocq-elpi.override.version = "master";
      rocq-elpi-test.override.version = "master";
      # plugin pins, from v9.3 branch of Rocq
      bignums.override.version = "36cd7009759b797b9b248ca91959e11494e89a4a";
      stdlib-test.job = false;
      autosubst.job = false;  # no release for 9.3 yet
      coquelicot.job = false;  # no release for 9.3 yet
      deriving.job = false;  # no release for 9.3 yet
      fcsl-pcm.job = false;  # no release for 9.3 yet
      hierarchy-builder.job = false;  # no release for 9.3 yet
      mathcomp.job = false;  # no release for 9.3 yet
      mathcomp-algebra.job = false;  # no release for 9.3 yet
      mathcomp-algebra-tactics.job = false;  # no release for 9.3 yet
      mathcomp-analysis.job = false;  # no release for 9.3 yet
      mathcomp-analysis-stdlib.job = false;  # no release for 9.3 yet
      mathcomp-field.job = false;  # no release for 9.3 yet
      mathcomp-reals.job = false;  # no release for 9.3 yet
      mathcomp-reals-stdlib.job = false;  # no release for 9.3 yet
      mathcomp-word.job = false;  # no release for 9.3 yet
      mathcomp-zify.job = false;  # no release for 9.3 yet
      mathcomp-finmap.job = false;  # no release for 9.3 yet
      mathcomp-bigenough.job = false;  # no release for 9.3 yet
      QuickChick.job = false;  # no release for 9.3 yet
      quickchick-test.job = false;  # no release for 9.3 yet
      relation-algebra.job = false;  # no release for 9.3 yet
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "9.3";
      coq-elpi.override.version = "master";
      # plugin pins, from v9.3 branch of Rocq
      aac-tactics.override.version = "09523f9910891dcc2072f2b87fee658a62feb484";
      atbr.override.version = "1806f95dd68b953312cbee44224ea1e96de9f35f";
      bignums.override.version = "36cd7009759b797b9b248ca91959e11494e89a4a";
      itauto.job = false;  # broken
      coinduction.override.version = "81ecd5f1ffa3e46b696d9461c88ad6ca9be5cfc7";
      dpdgraph-test.override.version = "86433889a23298cb946175df9578434ec20990a2";
      coq-hammer.override.version = "810ee0b644022104de2dae3a4f397c08c9681b9d";
      coq-hammer-tactics.override.version = "810ee0b644022104de2dae3a4f397c08c9681b9d";
      equations.override.version = "d562d8c413f4b0d2a837ef742d08fa59d14107e6";
      equations-test.job = false;
      fiat-parsers.job = false;  # broken
      metarocq.override.version = "9242c14bc377611a56d45283977ea754fd499c47";
      metarocq-test.override.version = "9242c14bc377611a56d45283977ea754fd499c47";
      mtac2.override.version = "b229396fbfe474c0b9c5a7732dd5988454cb291a";
      paramcoq-test.override.version = "eba83b1cc03bb1ef4dc4384129a975e4286736db";
      relation-algebra.override.version = "2d2af3631929399bbac56f57b3e15302d8697e1c";
      rewriter.override.version = "bed456b1068058c0f80e559a845e0e40aad5dc73";
      rocq-lean-import.override.version = "38fb4791bc7a3bc49995526448778c6e5555aaf1";
      smtcoq.job = false;
      stalmarck-tactic.override.version = "698fb18415d10bfef07af3a3935acf551a829322";
      unicoq.override.version = "afff890feb05adfae6362344ba8b088c40059706";
      waterproof.override.version = "f49b8305b74eeddc039282de6f610b34ca941713";
      compcert.job = false;  # broken
      trakt.job = false;  # not available yet
      VST.job = false;  # depends on compcert
    } // listToAttrs (forEach lighten-released (p:
      { name = p; value.job = false; })); };
    "rocq-9.2" = { rocqPackages = common-bundles // {
      rocq-core.override.version = "9.2";
      # plugin pins, from v9.2 branch of Rocq
      bignums.override.version = "30a45625546da0a88db8689a8009d580aa3f557f";
      stdlib-test.job = false;
      autosubst.job = false;  # no release for 9.2 yet
      coquelicot.job = false;  # no release for 9.2 yet
      deriving.job = false;  # no release for 9.2 yet
      fcsl-pcm.job = false;  # no release for 9.2 yet
      mathcomp-algebra-tactics.job = false;  # no release for 9.2 yet
      mathcomp-word.job = false;  # no release for 9.2 yet
      mathcomp-zify.job = false;  # no release for 9.2 yet
      QuickChick.job = false;  # no release for 9.2 yet
      quickchick-test.job = false;  # no release for 9.2 yet
      relation-algebra.job = false;  # no release for 9.2 yet
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "9.2";
      # plugin pins, from v9.2 branch of Rocq
      aac-tactics.override.version = "4f796a7b0ee88330162727fc6ea988a7e0ea46e3";
      atbr.override.version = "47ac8fb6bf244d9a4049e04c01e561191490f543";
      bignums.override.version = "30a45625546da0a88db8689a8009d580aa3f557f";
      itauto.job = false;  # broken
      coinduction.override.version = "9502ae09e9f87518330f37c08bc19a8c452dcd91";
      dpdgraph-test.override.version = "7a0fba21287dd8889c55e6611f8ba219d012b81b";
      coq-hammer.override.version = "1d581299c2a85af175b53bd35370ea074af922ec";
      coq-hammer-tactics.override.version = "1d581299c2a85af175b53bd35370ea074af922ec";
      equations.job = false;
      equations-test.job = false;
      fiat-parsers.job = false;  # broken
      metarocq.override.version = "e8f8078e756cc378b830eb5a8e4637df43d481af";
      metarocq-test.override.version = "e8f8078e756cc378b830eb5a8e4637df43d481af";
      mtac2.job = false;  # not available for 9.2
      paramcoq-test.override.version = "f8026210f37faf6c4031de24ada9fdded29d67e5";
      relation-algebra.override.version = "ba3db5783060d9e25d1db5e377fc9d71338a5160";
      rewriter.override.version = "dd37fb28ed7f01a3b7edc0675a86b95dd3eb1545";
      rocq-lean-import.override.version = "b8291b9dae4f5ed780112e95eea484e435199b46";
      smtcoq.job = false;
      stalmarck-tactic.override.version = "d32acd3c477c57b48dd92bdd96d53fb8fa628512";
      unicoq.job = false;  # not available for 9.2
      # waterproof.override.version = "99ad6ff78fa700c84ba0cb1d1bda27d8e0f11e1a";
      waterproof.job = false;
      compcert.job = false;  # broken
      VST.job = false;  # depends on compcert
    } // listToAttrs (forEach lighten-released (p:
      { name = p; value.job = false; })); };
  };
}
