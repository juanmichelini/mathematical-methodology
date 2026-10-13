/-!
# First-search candidates as printed by the original Haskell

Ground truth for `candidatosFst`: the output of foundations `Main.candidatosFst`, printed with
`toCLI` (types in the same style as `Ty.pp`).  Produced by running the Haskell on GHC; see
`docs/DEVELOPMENT.md` ("Comparing with the Haskell").  Order is significant.
-/

namespace MM.Examples

def haskellFst : List String :=
  [
    "\\a -> case a of { C_,R.0 -> C_,R.0; C_,R.1 b -> f b; }  ::  (C_,R -> C_,R)",
    "\\a -> case a of { C_,R.0 -> C_,R.1 C_,R.0; C_,R.1 b -> f b; }  ::  (C_,R -> C_,R)",
    "\\a -> case a of { C_,R.0 -> C_,R.1 (C_,R.1 C_,R.0); C_,R.1 b -> f b; }  ::  (C_,R -> C_,R)",
    "\\a -> case a of { C_,R.0 -> C_,R.0; C_,R.1 b -> C_,R.1 (f b); }  ::  (C_,R -> C_,R)",
    "\\a -> case a of { C_,R.0 -> C_,R.1 C_,R.0; C_,R.1 b -> C_,R.1 (f b); }  ::  (C_,R -> C_,R)",
    "\\a -> case a of { C_,R.0 -> C_,R.0; C_,R.1 b -> C_,R.1 (C_,R.1 (f b)); }  ::  (C_,R -> C_,R)",
    "\\a -> case a of { C_,R.0 -> C_,a_R.0; C_,R.1 b -> f b; }  ::  (C_,R -> C_,a_R)",
    "\\a -> case a of { C_,a_R.0 -> C_,R.0; C_,a_R.1 b c -> f c; }  ::  (C_,a_R -> C_,R)",
    "\\a -> case a of { C_,a_R.0 -> C_,R.1 C_,R.0; C_,a_R.1 b c -> f c; }  ::  (C_,a_R -> C_,R)",
    "\\a -> case a of { C_,a_R.0 -> C_,R.1 (C_,R.1 C_,R.0); C_,a_R.1 b c -> f c; }  ::  (C_,a_R -> C_,R)",
    "\\a -> case a of { C_,a_R.0 -> C_,R.0; C_,a_R.1 b c -> C_,R.1 (f c); }  ::  (C_,a_R -> C_,R)",
    "\\a -> case a of { C_,a_R.0 -> C_,R.1 C_,R.0; C_,a_R.1 b c -> C_,R.1 (f c); }  ::  (C_,a_R -> C_,R)",
    "\\a -> case a of { C_,a_R.0 -> C_,R.0; C_,a_R.1 b c -> C_,R.1 (C_,R.1 (f c)); }  ::  (C_,a_R -> C_,R)",
    "\\a -> case a of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 b c -> f c; }  ::  (C_,a_R -> C_,a_R)",
    "\\a -> case a of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 b c -> C_,a_R.1 b (f c); }  ::  (C_,a_R -> C_,a_R)",
    "\\a -> case a of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 b c -> C_,a_R.1 b (C_,a_R.1 b (f c)); }  ::  (C_,a_R -> C_,a_R)",
    "\\b -> \\a -> case b of { C_,R.0 -> a; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.0; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 a; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 C_,R.0; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 (C_,R.1 a); C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 (C_,R.1 C_,R.0); C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> a; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.0; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 a; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 C_,R.0; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> a; C_,R.1 c -> C_,R.1 (C_,R.1 (f c a)); }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.0; C_,R.1 c -> C_,R.1 (C_,R.1 (f c a)); }  ::  (C_,R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,a_R.0; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.0; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 C_,R.0; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 (C_,R.1 C_,R.0); C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.0; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.1 C_,R.0; C_,R.1 c -> C_,R.1 (f c a); }  ::  (C_,R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,R.0; C_,R.1 c -> C_,R.1 (C_,R.1 (f c a)); }  ::  (C_,R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,R.0 -> a; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,R.0 -> C_,a_R.0; C_,R.1 c -> f c a; }  ::  (C_,R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.0; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 a; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 C_,R.0; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 (C_,R.1 a); C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 (C_,R.1 C_,R.0); C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> C_,R.1 (f d a); }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.0; C_,a_R.1 c d -> C_,R.1 (f d a); }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 a; C_,a_R.1 c d -> C_,R.1 (f d a); }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 C_,R.0; C_,a_R.1 c d -> C_,R.1 (f d a); }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> C_,R.1 (C_,R.1 (f d a)); }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.0; C_,a_R.1 c d -> C_,R.1 (C_,R.1 (f d a)); }  ::  (C_,a_R -> (C_,R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 c d -> C_,a_R.1 c (f d a); }  ::  (C_,a_R -> (C_,R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 c d -> C_,a_R.1 c (C_,a_R.1 c (f d a)); }  ::  (C_,a_R -> (C_,R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.0; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 C_,R.0; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 (C_,R.1 C_,R.0); C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.0; C_,a_R.1 c d -> C_,R.1 (f d a); }  ::  (C_,a_R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.1 C_,R.0; C_,a_R.1 c d -> C_,R.1 (f d a); }  ::  (C_,a_R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,R.0; C_,a_R.1 c d -> C_,R.1 (C_,R.1 (f d a)); }  ::  (C_,a_R -> (C_,a_R -> C_,R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 c d -> f d a; }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> C_,a_R.1 c (f d a); }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 c d -> C_,a_R.1 c (f d a); }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> a; C_,a_R.1 c d -> C_,a_R.1 c (C_,a_R.1 c (f d a)); }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))",
    "\\b -> \\a -> case b of { C_,a_R.0 -> C_,a_R.0; C_,a_R.1 c d -> C_,a_R.1 c (C_,a_R.1 c (f d a)); }  ::  (C_,a_R -> (C_,a_R -> C_,a_R))"
  ]

end MM.Examples
