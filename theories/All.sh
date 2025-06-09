#!/bin/sh
set -e
set -u
set -o pipefail
cd "$(dirname "$0")"
printf 'Set Warnings "-deprecated-library-file,-warn-library-file,-notation-incompatible-prefix,-notation-overridden,-overwriting-delimiting-key".\n'
find . -name '*.v' ! -path ./All.v | sort | xargs rocq dep -Q . Stdlib -sort | \
  sed -e 's#\./#From Stdlib Require Export #g' -e 's#\.v\s*#.\n#g' -e 's#/#.#g'
