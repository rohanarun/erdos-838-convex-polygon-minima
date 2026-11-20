#!/bin/sh
set -eu
cd "$(dirname "$0")"
here=$(pwd -P)
if [ -n "${MATHLIB_LEAN_PATH:-}" ]; then deps=$MATHLIB_LEAN_PATH; else deps=$(lake env printenv LEAN_PATH); fi
mkdir -p "$here/.replay/tmp"
export LEAN_PATH="$here/.replay:$deps" TMPDIR="$here/.replay/tmp"
for mod in FiniteWitnesses ChunkWitnessBase ChunkWitness14 Exclusions14 Equality14; do
  echo "Checking $mod"
  lean -j 1 -s 524288 --root="$here" -o "$here/.replay/$mod.olean" "$here/$mod.lean"
done
