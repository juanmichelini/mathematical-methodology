#!/bin/sh
# Build and run one oracle script against a foundations checkout.
#   scripts/haskell/build.sh <foundations-dir> <Module> [out-file]
# Needs GHC (brew install ghc). Prints the module's `main` output to stdout or out-file.
set -e
F="$1"; M="$2"; OUT="${3:-/dev/stdout}"
HERE="$(cd "$(dirname "$0")" && pwd)"
B="$(mktemp -d)"
ghc -w -O0 -i"$F/code" -i"$HERE" -outputdir "$B" -main-is "$M.main" "$HERE/$M.hs" -o "$B/run" >&2
"$B/run" > "$OUT"
