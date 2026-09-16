#!/bin/sh
set -eu
cd "$(dirname "$0")"
export ELAN_HOME="$PWD/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
mkdir -p .tools
for prerequisite in curl git tar; do
  command -v "$prerequisite" >/dev/null 2>&1 || {
    echo "Missing prerequisite: $prerequisite" >&2
    exit 1
  }
done
if [ ! -x "$ELAN_HOME/bin/elan" ]; then
  curl --fail --location --show-error --retry 3 \
    https://raw.githubusercontent.com/leanprover/elan/227caca133724d5516bee25c2aeb3e609478f2d8/elan-init.sh \
    --output .tools/elan-init.sh
  sh .tools/elan-init.sh -y --no-modify-path --default-toolchain none
fi
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
