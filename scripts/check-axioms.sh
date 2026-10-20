#!/bin/sh
# Every exported theorem must be checked by Lean's kernel with no axioms and no `sorry`.
# For each generated proofs file, prints `#print axioms` for each theorem and fails if any
# line says something else than "does not depend on any axioms".
set -e
cd "$(dirname "$0")/.."

check() { # file module namespace
  F="$1"; M="$2"; NS="$3"
  T="$(mktemp -t axioms.XXXXXX).lean"
  { echo "import $M"
    grep '^theorem' "$F" | sed "s/^theorem \([A-Za-z0-9_]*\).*/#print axioms $NS.\1/"; } > "$T"
  OUT="$(lake env lean "$T")"
  N=$(echo "$OUT" | grep -c "does not depend on any axioms" || true)
  EXPECTED=$(grep -c '^theorem' "$F")
  if [ "$N" -ne "$EXPECTED" ]; then
    echo "$OUT" | grep -v "does not depend on any axioms" || true
    echo "FAIL ($F): $N of $EXPECTED theorems are axiom-free"; exit 1
  fi
  echo "$F: $N of $EXPECTED theorems depend on no axioms (and no sorry)"
}

check MathematicalMethodology/Generated/AppendixBProofs.lean MathematicalMethodology.Generated.AppendixBProofs AppB
