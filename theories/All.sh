#!/usr/bin/env bash
set -e
set -o pipefail
cd "$(dirname "$0")"

printf 'Set Warnings "-deprecated-library-file,-warn-library-file,-notation-incompatible-prefix,-notation-overridden,-overwriting-delimiting-key".\n'

if [ "$1" = "-unsorted" ]; then
  rocqdep="xargs echo"
else
  rocqdep="xargs rocq dep -Q . Stdlib -sort"
fi
for f in $(find . -regex '.*/[^.][^/]*[.]v' ! -path ./All.v | sort | $rocqdep); do
  f=${f%.v}
  f=${f#./}
  f=${f//"/"/.}
  printf 'From Stdlib Require Export %s.\n' "${f}"
done
