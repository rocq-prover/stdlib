with builtins; with (import <nixpkgs> {}).lib;
{
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
  default-bundle = "rocq-9.0";

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

    master = [
      "aac-tactics"
      "argosy"
      "async-test"
      "atbr"
      "autosubst"
      "bbv"
      "bedrock2"
      "bignums"
      "bignums-test"
      "category-theory"
      "ceres"
      "Cheerios"
      "coinduction"
      "CoLoR"
      "compcert"
      "coqprime"
      "coquelicot"
      "coqutil"
      "coq-elpi"
      "ExtLib"
      "coq-hammer"
      "coq-hammer-tactics"
      "coq-performance-tests"
      # "coq-tools"  # overlay
      "corn"
      "cross-crypto"
      "deriving"
      "engine-bench"
      "fcsl-pcm"
      "fiat-crypto"
      "fiat-crypto-ocaml"
      "fiat-parsers"
      "flocq"
      "hierarchy-builder"
      "http"
      "InfSeqExt"
      "iris"
      "iris-examples"
      "itauto"
      "ITree"
      "itree-io"
      "json"
      "kami"
      "mathcomp"
      "mathcomp-algebra"
      "mathcomp-algebra-tactics"
      "mathcomp-analysis"
      "mathcomp-bigenough"
      "mathcomp-character"
      "mathcomp-classical"
      "mathcomp-field"
      "mathcomp-fingroup"
      "mathcomp-finmap"
      "mathcomp-reals"
      "mathcomp-solvable"
      "mathcomp-ssreflect"
      "mathcomp-zify"
      "math-classes"
      "MenhirLib"
      "mtac2"
      "neural-net-coq-interp"
      "paco"
      "paramcoq-test"
      "parsec"
      "perennial"
      "QuickChick"
      "quickchick-test"
      "relation-algebra"
      "rewriter"
      "riscvcoq"
      "rupicola"
      "sf"
      "simple-io"
      "stalmarck-tactic"
      "stdpp"
      "StructTact"
      "unicoq"
      "Verdi"
      "VerdiRaft"
      "vst"
    ];
    coq-master = [
      "dpdgraph-test"
      "smtcoq"
      "trakt"
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
    coq-common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // listToAttrs (forEach coq-master (p:
      { name = p; value.override.version = "coq-master"; }))
    // listToAttrs (forEach main (p:
      { name = p; value.override.version = "main"; }))
    // {
      coq-elpi.override.elpi-version = "2.0.7";
      fiat-crypto-legacy.override.version = "sp2019latest";
      tlc.override.version = "master-for-coq-ci";
      smtcoq-trakt.override.version = "with-trakt-coq-master";
      coq-tools.override.version = "proux01:coq_19955";
      stdlib-refman-html.job = true;
      jasmin.job = false;  # Currently broken, c.f., https://github.com/rocq-prover/rocq/pull/20589
      # To add a simple overlay applying to all bundles,
      # add below a line like
      #<package>.override.version = "<github_login>:<branch>";
      # where
      # * <package> will typically be one of the strings above (without the quotes)
      #   or look at https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules
      #   for a complete list of Coq packages available in Nix
      # * <github_login>:<branch> is such that this will use the branch <branch>
      #   from https://github.com/<github_login>/<repository>
      corn.override.version = "andres-erbsen:patch-1";
    };
    common-bundles = {
      bignums.override.version = "master";
      rocq-elpi.override.version = "master";
      rocq-elpi.override.elpi-version = "2.0.7";
      rocq-elpi-test.override.version = "master";
      stdlib-html.job = true;
      stdlib-test.job = true;
      stdlib-subcomponents.job = true;
    };
  in {
    "rocq-master" = { rocqPackages = common-bundles // {
      rocq-core.override.version = "master";
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "master";
    }; };
    "rocq-9.0" = { rocqPackages = common-bundles // {
      rocq-core.override.version = "9.0.0";
    }; coqPackages = coq-common-bundles // {
      coq.override.version = "9.0.0";
      # plugin pins, from v9.0 branch of Coq
      aac-tactics.override.version = "109af844f39bf541823271e45e42e40069f3c2c4";
      atbr.override.version = "47ac8fb6bf244d9a4049e04c01e561191490f543";
      itauto.override.version = "c13c6b4a0070ecc3ae8ea9755a1d6a163d123127";
      bignums.override.version = "cc2d9ee990e4cfebe5f107d8357198baa526eded";
      coinduction.override.version = "09caaf1f809e3e91ebba05bc38cef6de83ede3b3";
      dpdgraph-test.override.version = "74ced1b11a8df8d4c04c3829fcf273aa63d2c493";
      coq-hammer.override.version = "31442e8178a5d85a9f57a323b65bf9f719ded8ec";
      coq-hammer-tactics.override.version = "31442e8178a5d85a9f57a323b65bf9f719ded8ec";
      equations.override.version = "1.3.1+9.0";
      equations-test.job = false;
      fiat-parsers.job = false;  # broken
      metarocq.override.version = "1.4-9.0";
      metarocq-test.override.version = "v1.4-9.0";
      mtac2.override.version = "1cdb2cb628444ffe9abc6535f6d2e11004de7fc1";
      paramcoq-test.override.version = "32609ca4a9bf4a0e456a855ea5118d8c00cda6be";
      perennial.job = false;  # broken
      relation-algebra.override.version = "7966d1a7bb524444120c56c3474717bcc91a5215";
      rewriter.override.version = "30c8507c1e30626b2aa1e15c0aa7c23913da033c";
      smtcoq.override.version = "5c6033c906249fcf98a48b4112f6996053124514";
      smtcoq-trakt.override.version = "9392f7446a174b770110445c155a07b183cdca3d";
      stalmarck-tactic.override.version = "d32acd3c477c57b48dd92bdd96d53fb8fa628512";
      unicoq.override.version = "a9b72f755539c0b3280e38e778a09e2b7519a51a";
      waterproof.override.version = "443f794ddc102309d00f1d512ab50b84fdc261aa";
      compcert.job = false;  # broken
    }; };
  };
}
