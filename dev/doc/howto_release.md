* generate changelog with dev/tools/generate-release-changelog.sh
  and update doc/sphinx/changes.rst accordingly
* update doc/sphinx/conf.py (particularly is_a_released_version)
* check the result of "make refman-html"
  (in _build/default/doc/refman-html)
* if need be, update supported versions of Rocq in .nix/config.nix
* rerun CI
* release on github (and add the generated tarball as asset)
* once tagging is done push a commit to update doc/sphinx/changes.rst
  (particularly is_a_released_version)
