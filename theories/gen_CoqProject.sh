#!/bin/sh
set -e
# Script generating the contents of [_CoqProject] from [rocq-flags.conf].

echo "# Generated file, edit [gen_CoqProject.sh] / [rocq-flags.conf] instead."

echo
echo "# Search path"
echo "-R . Stdlib"

echo
echo "# Flags"
# Adding "-arg " prefix to all non-empty, non-comment lines of [config/flags].
cat rocq-flags.conf | grep "^[^#]\+" | sed "s/^/-arg /"
