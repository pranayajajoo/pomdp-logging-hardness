#!/bin/sh
set -eu
cd "$(dirname "$0")"
export ELAN_HOME="$PWD/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
if [ ! -x "$ELAN_HOME/bin/lake" ]; then
  echo 'Local Lean installation is missing. Run: sh setup.sh' >&2
  exit 1
fi
lake build
lake env lean Audit.lean
