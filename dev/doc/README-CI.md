# Stdlib CI

The CI is mostly implemented using Nix on top of packages of the
nixpkgs repository https://github.com/NixOS/nixpkgs through the
coq-nix-toolbox https://github.com/coq-community/coq-nix-toolbox .
Binary results are cached using Cachix.

### Local Installation and Nix Usage

See this wiki page
https://github.com/math-comp/math-comp/wiki/Using-nix for how to
install and setup Nix and Cachix.

### Rerunning a CI Task Locally

You can take example of the files `.github/workflows/nix-action-coq-*.yml`
For instance, to rerun iris for Rocq master :
```shell
% nix-build --argstr bundle "coq-master" --argstr job iris
```
The list of bundles can be found in `.nix/config.nix`.

### Test CI Configurations with Overlays

For simple overlays, it's enough to add a line in the .nix/config.nix
file (look for "simple overlay" there).

For more elaborate overlays (for instance editing package dependencies
or build process), a simple way to test modifications of the CI
configuration (new version or configuration change of some package for
instance) is through overlays, see the corresponding paragraph at
https://github.com/coq-community/coq-nix-toolbox#overlays (for sha256
hashes, one can just put an empty string, run the `nix-build` command
above and an error will give the correct value).

### Updating coq-nix-toolbox

Once overlays are satisfactory, they should eventually be merged into
the nixpkgs package repository.

The file `.nix/coq-nix-toolbox.nix` contains the git commit hash of
the version of coq-nix-toolbox used (c.f.,
https://github.com/coq-community/coq-nix-toolbox ). Coq-nix-toolbox
itself contains the git commit hash of the version of nixpkgs it uses
(c.f. https://github.com/NixOS/nixpkgs/ ). So in order to add or
remove a Nix derivation (package), one needs to first update nixpkgs,
then coq-nix-toolbox and finally the `.nix/coq-nix-toolbox.nix` file
here. See the [coq-nix-toolbox README](https://github.com/coq-community/coq-nix-toolbox#testing-coqpackages-updates-in-nixpkgs)
for details of the process.

The most common maintenance action on the CI is currently to update
the version of the coq-nix-toolbox and regenerate the github action
workflows, see the last command of [this
paragraph](https://github.com/coq-community/coq-nix-toolbox?tab=readme-ov-file#standalone).

### Learning Nix basics

Basic concepts of the Nix package manager:
https://nixos.org/manual/nix/stable/ (I particularly recommend
[Part I. introduction](https://nixos.org/manual/nix/stable/#chap-introduction) and
[Chapter 9. Basic Package Management](https://nixos.org/manual/nix/stable/#ch-basic-package-mgmt))

Nix is based on its own functional language:
[Part IV. Writing Nix Expressions](https://nixos.org/manual/nix/stable/#chap-writing-nix-expressions)

Specifics for Rocq packages: [15.5. Coq and coq packages](https://nixos.org/manual/nixpkgs/unstable/#sec-language-coq)

### Caching

The CI uses caching provided by https://www.cachix.org/ and there is a
token in the coq-community organization to authenticate and store the
results. Any CI build is stored globally and can be used on one's own
computer as described in
https://github.com/math-comp/math-comp/wiki/Using-nix
