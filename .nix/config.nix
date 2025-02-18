{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  attribute = "coqeal";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
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
  # coqproject = "_CoqProject";

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  cachix.math-comp = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  
  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"
  
  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
  
  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "coq-8.20";

  ## write one `bundles.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well
  bundles = let

  ## You can override Coq and other Coq coqPackages
  ## through the following attribute
  # coqPackages.coq.override.version = "8.11";

  ## In some cases, light overrides are not available/enough
  ## in which case you can use either
  # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
  ## or a "long" overlay to put in `.nix/coq-overlays
  ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
  ## to automatically retrieve the one from nixpkgs
  ## if it exists and is correctly named/located

  ## You can override Coq and other Coq coqPackages
  ## throught the following attribute
  ## If <ocaml-pkg> does not support lights overrides,
  ## you may use `overrideAttrs` or long overlays
  ## located in `.nix/ocaml-overlays`
  ## (there is no automation for this one)
  #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

  ## You can also override packages from the nixpkgs toplevel
  # <nix-pkg>.override.overrideAttrs = o: <overrides>;
  ## Or put an overlay in `.nix/overlays`

  ## you may mark a package as a CI job as follows
  #  coqPackages.<another-pkg>.ci.job = "test";
  ## It can then be built throught
  ## nix-build --argstr ci "default" --arg ci-job "test";

  common-bundles = { 
    mathcomp-ssreflect.job = true;
    mathcomp-algebra.job = true;
    mathcomp-field.job = true;
    mathcomp-finmap.job = true;
    mathcomp-bigenough.job = true;
    multinomials.job = true;
    mathcomp-real-closed.job = true;
    mathcomp-zify.job = true;
    mathcomp-algebra-tactics.job = true;
    mathcomp-apery.override.version = "master";  # reverse dependency of coqeal
    stdlib.job = true;
    bignums.job = true;
    interval.job = false;
    coquelicot.job = false;
    # To add an overlay applying to all bundles,
    # add below a line like
    #<package>.override.version = "<github_login>:<branch>";
    # where
    # * <package> will typically be one of the strings above (without the quotes)
    #   or look at https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules
    #   for a complete list of Coq packages available in Nix
    # * <github_login>:<branch> is such that this will use the branch <branch>
    #   from https://github.com/<github_login>/<repository>
  };
  in {
    "coq-master" = { rocqPackages = {
      rocq-core.override.version = "master";
      stdlib.override.version = "master";
      bignums.override.version = "master";
      rocq-elpi.override.version = "master";
      rocq-elpi.override.elpi-version = "2.0.7";
    }; coqPackages = common-bundles // {
      coq.override.version = "master";
      stdlib.override.version = "master";
      bignums.override.version = "master";
      coq-elpi.override.version = "master";
      coq-elpi.override.elpi-version = "2.0.7";
      hierarchy-builder.override.version = "master";
      mathcomp.override.version = "master";
      mathcomp-finmap.override.version = "master";
      mathcomp-bigenough.override.version = "master";
      multinomials.override.version = "master";
      mathcomp-real-closed.override.version = "master";
      mathcomp-zify.override.version = "master";
      mathcomp-algebra-tactics.override.version = "master";
    }; };
    "rocq-9.0".coqPackages = common-bundles // {
      coq.override.version = "9.0";
      coq-elpi.job = true;
      hierarchy-builder.job = true;
      mathcomp.override.version = "2.3.0";
      multinomials.override.version = "2.3.0";
    };
    "coq-8.20".coqPackages = common-bundles // {
      coq.override.version = "8.20";
      coq-elpi.override.version = "2.5.0";
      coq-elpi.override.elpi-version = "2.0.7";
      hierarchy-builder.override.version = "1.8.1";
      mathcomp.override.version = "2.3.0";
    };
  };
}
