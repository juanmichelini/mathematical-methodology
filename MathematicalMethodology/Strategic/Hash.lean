/-!
# A stable hash for comparing large outputs

FNV-1a, 64 bit, over the UTF-8 bytes.  Used to compare, against a committed value, outputs
that are too large to commit as text (the Haskell dumps in `fixtures/haskell/`).  The full
text can always be diffed against a fresh Haskell run (`scripts/haskell/`).
-/

namespace MM.Strategic

def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

end MM.Strategic
