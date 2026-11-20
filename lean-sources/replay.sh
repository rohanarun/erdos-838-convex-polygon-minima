#!/bin/sh
set -eu
cd "$(dirname "$0")"
base=$(pwd -P)
if ! lean --version | grep -F 'version 4.32.0,' >/dev/null; then
  echo 'Use the Lean release in lean-toolchain (4.32.0).' >&2
  exit 1
fi
if [ -n "${MATHLIB_LEAN_PATH:-}" ]; then
  deps=$MATHLIB_LEAN_PATH
else
  deps=$(lake env printenv LEAN_PATH)
fi
mkdir -p "$base/.replay/tmp"
export LEAN_PATH="$base/.replay:$deps" TMPDIR="$base/.replay/tmp"
for mod in FiniteWitnesses Witness13 DeletionCount AreaIdentity ProductContradiction CompactCertificates Exclude569 OtherExclusions; do
  echo "Checking $mod"
  lean -s 524288 --root="$base" -o "$base/.replay/$mod.olean" "$base/$mod.lean"
done
echo 'All eight modules checked.'
