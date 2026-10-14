import MathematicalMethodology.Examples.ConjecturesFst
import MathematicalMethodology.Examples.ConjecturesTest
import MathematicalMethodology.Strategic.Hash
import MathematicalMethodology.Examples.SecondSearch

open MM.Strategic

/-- `lake exe haskell-check`: compare the large dumps with the hashes of the Haskell output
(`fixtures/haskell/*.fnv`).  Prints the hash; exits non-zero on a mismatch.  With
`--write`, prints what to commit.  Use `--dump <name>` to print a dump for diffing with a
fresh Haskell run. -/
def checks : List (String × String × String) :=
  [ ("conj_test", MM.Examples.ConjecturesTest.dump, include_str "fixtures/haskell/conj_test.fnv") ]

/-- Dumps committed as text. They are compared in full by `lake exe results` (it runs the second
search, about a minute), so `--dump` only prints them, for diffing with a fresh Haskell run. -/
def textChecks : List (String × (Unit → String) × String) :=
  [ ("snd_sel", fun _ => MM.Examples.SecondSearch.dump, include_str "fixtures/haskell/snd_sel.txt") ]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--dump", n] =>
    match checks.find? (·.1 == n) with
    | some (_, d, _) => IO.print d; return 0
    | none =>
      match textChecks.find? (·.1 == n) with
      | some (_, d, _) => IO.print (d ()); return 0
      | none => IO.eprintln s!"unknown dump {n}"; return 2
  | _ =>
    let mut bad := false
    for (n, d, expected) in checks do
      let h := fnv1a d
      let lines := (d.splitOn "\n").length - 1
      let line := s!"{h} {lines}"
      IO.println s!"{n}: {line}"
      if line != expected.trim then
        IO.println s!"  MISMATCH: expected {expected.trim}"
        bad := true
    return if bad then 1 else 0
