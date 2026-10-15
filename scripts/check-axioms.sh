#!/bin/sh
# Every exported theorem must be checked by Lean's kernel with no axioms and no `sorry`.
# Prints `#print axioms` for each theorem of Generated/AppendixBProofs.lean and fails if any
# line says something else than "does not depend on any axioms".
set -e
cd "$(dirname "$0")/.."
F=MathematicalMethodology/Generated/AppendixBProofs.lean
T="$(mktemp -t axioms.XXXXXX).lean"
{ echo "import MathematicalMethodology.Generated.AppendixBProofs"
  grep '^theorem' "$F" | sed 's/^theorem \([A-Za-z0-9_]*\).*/#print axioms AppB.\1/'; } > "$T"
OUT="$(lake env lean "$T")"
N=$(echo "$OUT" | grep -c "does not depend on any axioms" || true)
EXPECTED=$(grep -c '^theorem' "$F")
if [ "$N" -ne "$EXPECTED" ]; then
  echo "$OUT" | grep -v "does not depend on any axioms" || true
  echo "FAIL: $N of $EXPECTED theorems are axiom-free"; exit 1
fi
echo "$N of $EXPECTED theorems depend on no axioms (and no sorry)"
