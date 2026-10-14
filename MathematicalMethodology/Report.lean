import MathematicalMethodology.Pretty
import MathematicalMethodology.Examples.Lists
import MathematicalMethodology.Examples.ListsStore
import MathematicalMethodology.Examples.ListsSearch
import MathematicalMethodology.Examples.Enumeration
import MathematicalMethodology.Examples.ExportCheck
import MathematicalMethodology.Examples.ConjecturesFst
import MathematicalMethodology.Examples.ProveFst
import MathematicalMethodology.Examples.FirstSearch
import MathematicalMethodology.Examples.SecondSearch
import MathematicalMethodology.Examples.TestSuite
import MathematicalMethodology.Export.AppendixB

/-!
# Report

Builds the markdown report committed as `results/report.md` (see `Results.lean`).
Display and orchestration only; not part of the trusted base.

The report is deterministic on purpose: no timestamps, no commit hashes, no timings.
That lets CI regenerate it on a clean runner and compare it with the committed copy.
-/

namespace MM.Report

open MM MM.Examples

/-- Outcome for one lemma of a development. -/
structure LemmaResult where
  name   : String
  stmt   : Affirm
  size   : Nat
  result : Except String Unit

/-- Check lemmas in order. A proven lemma becomes a rule for the later ones; a
failed one does not. -/
def runDev (cx : Ctx) : List (String × Affirm × Cert) → List Rule → List LemmaResult
  | [], _ => []
  | (name, g, c) :: rest, rules =>
    let r := c.check cx rules g
    let rules' := match r with
      | .ok () => rules ++ [g.toRule]
      | .error _ => rules
    ⟨name, g, c.size, r⟩ :: runDev cx rest rules'

def LemmaResult.ok (r : LemmaResult) : Bool :=
  match r.result with
  | .ok () => true
  | .error _ => false

def escape (s : String) : String := s.replace "|" "\\|"

def positiveRows (rs : List LemmaResult) : List String :=
  rs.map fun r =>
    let status := match r.result with
      | .ok () => "accepted"
      | .error e => s!"REJECTED: {e}"
    s!"| `{r.name}` | `{escape r.stmt.pp}` | {r.size} | {status} |"

/-- Rejection message of a negative test, or `none` if it was wrongly accepted. -/
def negativeOutcome (dev : List (String × Affirm × Cert)) : Option String :=
  match checkDevelopment listCtx dev [] with
  | .error e => some e
  | .ok _ => none

def negativeRows : List String :=
  negatives.map fun (desc, dev) =>
    match negativeOutcome dev with
    | some e => s!"| {escape desc} | rejected: `{escape e}` |"
    | none => s!"| {escape desc} | WRONGLY ACCEPTED |"

/-- Is the committed `Generated/FstCandidates.lean` what the generator prints? -/
def exportUpToDate : Bool :=
  MM.Export.fstFile == include_str "Generated/FstCandidates.lean"

def conjLines : List String := MM.Examples.ConjecturesFst.dump.splitOn "\n"

def conjCount : Nat := (conjLines.filter fun (l : String) => l.contains '|').length

def batchCount : Nat := (conjLines.filter fun (l : String) => l.startsWith "# batch").length

/-- Do the conjectures for the first-search candidates equal the Haskell's, line by line? -/
def conjecturesMatchHaskell : Bool :=
  MM.Examples.ConjecturesFst.dump == include_str "../fixtures/haskell/conj_fst.txt"

/-- Rows of the `paciencia` table: ours against foundations'. -/
def pacienciaRows : List String :=
  MM.Examples.ProveFst.haskellCounts.map fun (n, expected) =>
    let got := MM.Examples.ProveFst.counts n
    s!"| {n} | {got.length} | {got} | {expected} | {got == expected} |"

def pacienciaOk : Bool :=
  MM.Examples.ProveFst.haskellCounts.all fun (n, expected) => MM.Examples.ProveFst.counts n == expected

/-- Is the proof trace identical to the Haskell's? -/
def proveTraceMatches : Bool :=
  MM.Examples.ProveFst.dump == include_str "../fixtures/haskell/prove_fst.txt"

/-- Everything behaved as expected: good certificates accepted, bad ones rejected. -/
def allCertified : Bool :=
  MM.Examples.ProveFst.certified.all fun (_, found, ok) => found == ok

def firstSearchRows : List String :=
  (MM.Examples.FirstSearch.selected.zip (MM.Examples.FirstSearch.measured.zip
      MM.Examples.FirstSearch.appendixB)).map fun (s, (m, e)) =>
    s!"| `{s.name}` | `{s.ty.pp}` | {m.1} | {m.2} | {e.1} | {e.2} |"

def firstSearchMatches : Bool :=
  (MM.Examples.FirstSearch.dump == (include_str "../fixtures/haskell/fst_sel.txt")) &&
  MM.Examples.FirstSearch.measured == MM.Examples.FirstSearch.appendixB

def appendixBRows : List String :=
  let names := (MM.Examples.FirstSearch.selected ++ MM.Examples.SecondSearch.selected).map (·.name)
  (names.zip (MM.Examples.SecondSearch.measured.zip MM.Examples.SecondSearch.appendixB)).map
    fun (n, (m, e)) => s!"| `{n}` | {m.1} | {m.2} | {e.1} | {e.2} | {m == e} |"

def secondSearchMatches : Bool :=
  (MM.Examples.SecondSearch.dump == (include_str "../fixtures/haskell/snd_sel.txt")) &&
  MM.Examples.SecondSearch.measured == MM.Examples.SecondSearch.appendixB

def suiteLines : List String := MM.Examples.TestSuite.dump.splitOn "\n"

def suiteProved : Nat := (suiteLines.filter fun (l : String) => l.startsWith "OK").length

def suiteMatches : Bool :=
  (MM.Examples.TestSuite.dump == (include_str "../fixtures/haskell/test_suite.txt")) &&
  suiteProved == MM.Examples.TestEnv.lemas.length

/-- Name, number of lemmas found and finished proofs of each chain of `Test.hs`. -/
def chainRows : List String :=
  let rec go (ls : List String) (name : String) (n : Nat) (acc : List String) : List String :=
    match ls with
    | [] => acc.reverse
    | l :: rest =>
      if l.startsWith "## " && !l.startsWith "## lemas" then go rest (l.drop 3) 0 acc
      else if l.startsWith "lemma " then go rest name (n + 1) acc
      else if l.startsWith "done " then go rest name 0 (s!"| `{name}` | {n} | {l.drop 5} |" :: acc)
      else go rest name n acc
  go suiteLines "" 0 []

/-- Is the committed `Generated/AppendixB.lean` what the generator prints for f0 … f30? -/
def appendixBExportUpToDate : Bool :=
  MM.Export.appendixBFile (MM.Examples.FirstSearch.selected ++ MM.Examples.SecondSearch.selected) ==
    (include_str "Generated/AppendixB.lean")

/-- Everything behaved as expected: good certificates accepted, bad ones rejected. -/
def allOk : Bool :=
  (runDev listCtx development []).all LemmaResult.ok &&
  negatives.all (fun (_, dev) => (negativeOutcome dev).isSome) &&
  MM.Examples.Enumeration.fstLines == MM.Examples.haskellFst &&
  exportUpToDate &&
  conjecturesMatchHaskell &&
  pacienciaOk && proveTraceMatches && allCertified && firstSearchMatches && secondSearchMatches &&
  suiteMatches && appendixBExportUpToDate

/-- Rows of the lemma-store classification: one per stored lemma. -/
def storeRows : List String :=
  let row (kind : String) (a : Affirm) : String := s!"| {kind} | `{escape a.pp}` |"
  let r := MM.Examples.store
  r.simp.map (row "simp") ++ r.reor.map (row "reor") ++ r.basu.map (row "basu")

/-- Rows of the tactic-search table: what the search found for each conjecture, and
whether the checker accepts it. -/
def searchRows : List String :=
  let checked := runDev listCtx MM.Examples.foundDevelopment []
  MM.Examples.found.map fun (n, _, c) =>
    match c with
    | none => s!"| `{n}` | not found | | |"
    | some c =>
      let status := match checked.find? (·.name == n) with
        | some r => if r.ok then "accepted" else "REJECTED"
        | none => "REJECTED"
      s!"| `{n}` | found | {c.size} | {status} |"

/-- Rows of the enumeration table: the data types of `Main.datas`. -/
def dataRows : List String :=
  MM.Strategic.datas.map fun d =>
    let ctors := d.2.map fun (c, fs) =>
      if fs.isEmpty then c else s!"{c} {" ".intercalate (fs.map MM.Strategic.Ty.pp)}"
    s!"| `{d.1}` | {", ".intercalate (ctors.map fun c => s!"`{c}`")} |"

/-- Number of first-search candidates for each function type. -/
def candidateRows : List String :=
  open MM.Strategic in
  let tipos := (armarTip 1 fstTypes) ++ (armarTip 2 fstTypes)
  tipos.map fun t =>
    s!"| `{t.pp}` | {(candidatosFst.filter fun (_, u) => u == t).length} |"

def markdown : String :=
  let pos := runDev listCtx development []
  String.intercalate "\n" <|
    [ "# Results"
    , ""
    , "Generated by `lake exe results`. Do not edit by hand: CI regenerates this file and"
    , "fails if it differs from the committed copy."
    , ""
    , "## Development: lists"
    , ""
    , "Each lemma is proved by a certificate that `Cert.check` re-verifies. Lemmas are"
    , "checked in order; each proven lemma is available as a rewrite rule to the next."
    , ""
    , "| lemma | statement | certificate steps | result |"
    , "|---|---|---|---|" ]
    ++ positiveRows pos ++
    [ ""
    , "## Negative tests"
    , ""
    , "The checker must reject each of these."
    , ""
    , "| case | result |"
    , "|---|---|" ]
    ++ negativeRows ++
    [ ""
    , s!"## Summary"
    , ""
    , s!"- lemmas accepted: {(pos.filter LemmaResult.ok).length} of {pos.length}"
    , s!"- negative tests rejected: {(negatives.filter fun (_, d) => (negativeOutcome d).isSome).length} of {negatives.length}"
    , s!"- overall: {if allOk then "ok" else "FAILED"}"
    , ""
    , "## Lemma store"
    , ""
    , "Proven lemmas are classified for the (untrusted) tactic search, as `Rec.add` does in"
    , "foundations `Prove.hs`: `simp` rewrites the bigger side to the smaller (sorted by the"
    , "`fund` gap), `reor` holds permutation lemmas in both directions, `basu` the rest."
    , "(`flod` and `floe` exist but, as in Haskell, `addAffirm` never fills them.)"
    , ""
    , "| store | lemma |"
    , "|---|---|" ]
    ++ storeRows ++
    [ ""
    , "## Tactic search"
    , ""
    , "The untrusted search (`Tactical/Search.lean`, port of `mainTactic`) is given the"
    , "statements above with no certificates and proves them in order, each proven lemma"
    , "feeding the lemma store. Whatever it finds is re-checked by `Cert.check`."
    , ""
    , "| lemma | search | certificate steps | checker |"
    , "|---|---|---|---|" ]
    ++ searchRows ++
    [ ""
    , "## Enumeration"
    , ""
    , "The untrusted strategic level (`Strategic/Enumerate.lean`, port of the enumeration in"
    , "`Propose.hs`) proposes data types and candidate functions. Data types of `Main.datas`:"
    , ""
    , "| type | constructors |"
    , "|---|---|" ]
    ++ dataRows ++
    [ ""
    , s!"First-search candidates (recursive functions on `C_,R` and `C_,a_R`):"
    , s!"{MM.Strategic.candidatosFst.length} in total; the original Haskell prints {MM.Examples.haskellFst.length}"
    , s!"and the two lists are identical, in order: {MM.Examples.Enumeration.fstLines == MM.Examples.haskellFst}."
    , ""
    , "| function type | candidates |"
    , "|---|---|" ]
    ++ candidateRows ++
    [ ""
    , "## Conjectures"
    , ""
    , "`Strategic/Conjecture.lean` (port of `conjeturas*`, `ample*`, `instanceAny` of `Propose.hs`)"
    , "proposes, for each candidate function, batches of equations to try to prove. For the"
    , s!"{MM.Strategic.candidatosFst.length} first-search candidates it proposes"
    , s!"{conjCount} conjectures in"
    , s!"{batchCount} batches; the"
    , "original Haskell prints the same statements, with the same variable names, in the same order:"
    , s!"{conjecturesMatchHaskell}. The functions of foundations `Test.hs` are checked against a hash of the"
    , "Haskell output by `lake exe haskell-check`."
    , ""
    , "## Finding lemmas"
    , ""
    , "`Tactical/Prove.lean` is a faithful port of `mainTactic`, `cutSingleStepCycles`, `giveUp`"
    , "and `prove`; `Strategic/FindLemmas.lean` of `findlemas`/`provell` (the first conjecture of a"
    , "batch that is proven becomes a lemma for the rest). The first search keeps the functions with"
    , "more than three lemmas, for several values of the search limit `paciencia`:"
    , ""
    , "| paciencia | kept | lemmas per kept function | foundations | same |"
    , "|---|---|---|---|---|" ]
    ++ pacienciaRows ++
    [ ""
    , s!"The whole trace of `provell` over the {MM.Strategic.candidatosFst.length} candidates (every conjecture tried,"
    , "whether its proof completes, the smallest budget at which it does, the lemma chosen from each"
    , s!"batch) equals the original Haskell's, line by line: {proveTraceMatches}."
    , ""
    , "Every lemma found is also proved by the checker-based search (`Tactical/Search.lean`, rigid"
    , "induction hypotheses) and the certificate accepted by `Cert.check`:"
    , ""
    , "| candidate | lemmas found | certified by `Cert.check` |"
    , "|---|---|---|" ]
    ++ (MM.Examples.ProveFst.certified.map fun (i, a, b) => s!"| {i} | {a} | {b} |") ++
    [ ""
    , "## First search (f0-f2)"
    , ""
    , s!"Of the {MM.Strategic.candidatosFst.length} candidates, {MM.Examples.FirstSearch.selected.length} keep more than three"
    , "lemmas (`candidatosFstSel`); they are named `f0, f1, f2`. Lemmas and finished proofs, against"
    , "foundations' Appendix B comparison:"
    , ""
    , "| function | type | lemmas | finished proofs | Appendix B lemmas | Appendix B proofs |"
    , "|---|---|---|---|---|---|" ]
    ++ firstSearchRows ++
    [ ""
    , "The definitions (with the binder names Haskell gives them when `f` is renamed), the variable"
    , "names they use, the lemma statements and the whole lemma store `fstRec` (simp, reor, basu, in"
    , s!"order) equal what the original Haskell prints: {firstSearchMatches}."
    , ""
    , "## Second search (f3-f30) and Appendix B"
    , ""
    , s!"{(MM.Strategic.candidatosSnd MM.Examples.FirstSearch.selected).length} candidates use the recursive call and a function of the first search"
    , s!"(foundations: 164); {MM.Examples.SecondSearch.selected.length} keep at least two lemmas proved by induction (foundations: 28),"
    , "named `f3 … f30`. With `f0 … f2` these are the 31 functions of the thesis' Appendix B. Lemmas and"
    , "finished proofs of each, against foundations' Appendix B comparison:"
    , ""
    , "| function | lemmas | finished proofs | Appendix B lemmas | Appendix B proofs | same |"
    , "|---|---|---|---|---|---|" ]
    ++ appendixBRows ++
    [ ""
    , "The candidates (in order), the definitions with Haskell's binder names, the variable names they use,"
    , s!"every lemma statement and the finished-proof counts equal what the original Haskell prints: {secondSearchMatches}."
    , ""
    , "## The lemma suite of `Test.hs`"
    , ""
    , s!"`Test.lemas` has {MM.Examples.TestEnv.lemas.length} hand-written lemmas about booleans, naturals and lists. Each is proved with"
    , "`lemascomp` and the lemmas before it as hypotheses (`Test.provelemas 30`, as `check-lemmas` does):"
    , s!"{suiteProved} of {MM.Examples.TestEnv.lemas.length} are proved, each at the same smallest budget as in the Haskell. The lemma chains of"
    , "`Test.hs` (lemmas found for a function, some starting from the lemmas of another):"
    , ""
    , "| function | lemmas found | finished proofs |"
    , "|---|---|---|" ]
    ++ chainRows ++
    [ ""
    , "`flipexp` finds the two lemmas of thesis Sec. 10, `c^(a+b) = c^a * c^b` and `c^(a*b) = (c^b)^a`."
    , s!"The whole output (every lemma with its smallest budget, every chain) equals the original Haskell's: {suiteMatches}."
    , ""
    , "## Export to Lean"
    , ""
    , s!"The 31 functions of Appendix B (f0 … f30) are printed as plain Lean in `Generated/AppendixB.lean`,"
    , "also a module of the library (so `lake build` compiles it); f0, f1, f2 and f3 (reverse) run in Lean"
    , s!"(`Examples/ExportAppendixB.lean`). The committed file is the generator's output: {appendixBExportUpToDate}."
    , ""
    , s!"The {MM.Strategic.candidatosFst.length} candidates (and the data types) are printed as plain Lean"
    , "(`Export/Lean.lean`, `lake exe export-lean`) in `Generated/FstCandidates.lean`. That file is"
    , "part of the library, so `lake build` compiles it: Lean itself accepts the definitions and their"
    , "structural recursion. A guard checks that the committed file equals the generator's output:"
    , s!"{exportUpToDate}."
    , ""
    , "## Soundness"
    , ""
    , "Accepting a certificate is not just tested, it is proved correct in Lean"
    , "(`Semantics/CheckSound.lean`): if `Cert.check` accepts a certificate for a statement,"
    , "the two sides are convertible (delta, beta, case) for every substitution of values for"
    , "its variables.  The theorem assumes that definitions are closed terms, that the declared"
    , "function signatures are right, and that data type names are unique."
    , "`Examples/ListsSound.lean` proves these assumptions for this development, giving"
    , "`development_valid` and `revRev_valid` (`rev (rev xs) = xs`)."
    , "" ]

end MM.Report
