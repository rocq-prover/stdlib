* generate changelog with dev/tools/generate-release-changelog.sh
  and update doc/sphinx/changes.rst accordingly
* update doc/sphinx/conf.py (particularly is_a_released_version)
* check the result of "make refman-html"
  (in _build/default/doc/refman-html)
* if need be, update supported versions of Rocq in .nix/config.nix
  and regenerate CI config with nix-shell --arg do-nothing true --run "genNixActions"
* rerun CI
* run `make refman-html` and push the resulting `_build/default/doc/refman-html`
  as `vX.Y/refman-stdlib` in https://github.com/rocq-prover/doc/
* run `make stdlib-html` and push the resulting `_build/default/doc/stdlib/html`
  as `vX.Y/stdlib` in https://github.com/rocq-prover/doc/
* release on github (and add the generated tarball as asset)
* once tagging is done push a commit to update doc/sphinx/changes.rst
  (particularly is_a_released_version)
