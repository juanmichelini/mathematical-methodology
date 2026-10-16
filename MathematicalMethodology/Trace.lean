import MathematicalMethodology.Export.Proofs
import MathematicalMethodology.Strategic.SecondSearch

/-!
# Traces of the pipeline

What was **enumerated**, **conjectured**, **attempted** and **proved**, including everything that
failed or was skipped, not just the proved lemmas (issue #39).  Every artifact is printed in two
forms: the original de Bruijn one (`Term`, `Affirm`) and the one exported to plain Lean
(`Export/`), so that an exported file can be traced back to the term it came from.

Display only.  **Untrusted**: nothing trusted imports it.  Deterministic (no timestamps, no
timings), but *not committed*: `lake exe trace [dir]` writes the files (default `trace/`, which
is git-ignored) and prints a summary.

* `enumerated.txt`: the data types and every candidate function of both searches.
* `conjectured.txt`: every conjecture proposed for each candidate, batch by batch, and whether it
  was tried or skipped because a stored lemma already rewrites it.
* `attempted.txt`: every proof attempt with its outcome; a failure says why (no rule applies, a
  cycle was cut, or the step budget `paciencia` ran out).
* `proved.txt`: the lemma chosen from each batch, and for the functions kept (f0 … f30) the Lean
  theorem the export prints for it.
-/

namespace MM.Trace

open MM MM.Strategic MM.Export

/-! ## de Bruijn view -/

mutual
  /-- A term with its de Bruijn indices: `#i` variables, `@f` defined functions. -/
  def dbTerm : Term → String
    | .var i => s!"#{i}"
    | .con c => c
    | .const f => s!"@{f}"
    | .app f a => s!"({dbTerm f} {dbTerm a})"
    | .abs b => s!"(λ. {dbTerm b})"
    | .cas s alts => s!"(case {dbTerm s} \{{"; ".intercalate (dbAlts alts)}})"
  def dbAlts : Alts → List String
    | .nil => []
    | .alt c n b rest => s!"{c}/{n} → {dbTerm b}" :: dbAlts rest
end

def dbAffirm (a : Affirm) : String :=
  s!"[{", ".intercalate a.ctx}] {dbTerm a.lhs} = {dbTerm a.rhs}"

/-! ## Why a proof failed -/

mutual
  /-- The first reason a proof attempt gave up, if it did. -/
  def proofReason : Proof → Option String
    | .done => none
    | .fail => some "step budget exhausted"
    | .step _ .noIdea .fail => some "no rule applies"
    | .step _ .loop .fail => some "cycle cut"
    | .step _ _ p => proofReason p
    | .ind _ _ cs => reasonCases cs
  def reasonCases : List (Comment × List Conj × Proof) → Option String
    | [] => none
    | (_, _, p) :: rest => proofReason p <|> reasonCases rest
end

/-! ## The runs -/

/-- One candidate of a search, with everything the pipeline did to it. -/
structure CandTrace where
  index : Nat
  def_ : Term
  ty : Ty
  batches : List (List Conj)
  results : List BatchResult

def CandTrace.chosen (c : CandTrace) : List Proof := c.results.filterMap (·.chosen)

/-- First search (`Main.candidatosFstTeo`), keeping every batch and every attempt. -/
def traceFirst (n : Nat) : List CandTrace :=
  candidatosFst.zipIdx.map fun ((f, ty), i) =>
    let tenv : TEnv := (Term.const "f", ty) :: cerothTEnv
    let cx := mkPCtx [("f", f)] datas (defNamesOf f)
    let bs := plemas (rejectWith {}) cx.env tenv "f"
    ⟨i, f, ty, bs, provell cx n {} bs⟩

/-- Second search (`Main.candidatosSndTeo`) given the functions kept by the first. -/
def traceSecond (fst : List Selected) (n : Nat) : List CandTrace :=
  let env0 := fstEnv fst
  let tenv0 := fstTEnv fst
  let rec0 := fstRec fst
  let used0 := fst.flatMap (·.used)
  (candidatosSnd fst).zipIdx.map fun ((f, ty), i) =>
    let cx := mkPCtx (("f", f) :: env0) datas (defNamesOf f ++ used0)
    let tenv := (Term.const "f", ty) :: tenv0
    let bs := plemas (rejectWith rec0) cx.env tenv "f"
    ⟨i, f, ty, bs, provell cx n rec0 bs⟩

def keptFirst (c : CandTrace) : Bool := c.chosen.length > 3
def keptSecond (c : CandTrace) : Bool :=
  (c.chosen.filter Proof.startsWithInduction).length ≥ 2

/-! ## Rendering -/

def statementOnly (ds : List DatasH) (name : String) (c : Conj) : String :=
  ((theoremHeader ds name c).replace " := by" "").replace ":\n    " ": "

def indent (s : String) : String := "    " ++ s.replace "\n" "\n    "

def enumeratedFile (fst snd : List CandTrace) : String :=
  let dataPart := datas.map fun d =>
    s!"{d.1}\n{indent (exportData datas d).trimRight}"
  let cand (prefix_ : String) (c : CandTrace) : String :=
    s!"### {prefix_} {c.index}  ::  {c.ty.pp}\n" ++
    s!"db:   {dbTerm c.def_}\nshow: {showFun c.def_}\n" ++
    s!"lean:\n{indent (exportFun datas s!"{prefix_}Cand{c.index}" c.ty c.def_).trimRight}\n"
  "# Enumerated\n\n## Data types (" ++ toString datas.length ++ ")\n\n" ++ "\n".intercalate dataPart ++
  s!"\n\n## First search: {fst.length} candidates\n\n" ++
  "(Lean text: the candidates of `Generated/FstCandidates.lean`, namespace `Gen`, compiled by `lake build`.)\n\n" ++
  "\n".intercalate (fst.map (cand "fst")) ++
  s!"\n## Second search: {snd.length} candidates\n\n" ++
  "(Lean text printed for reference: they call the first-search functions f0 … f2, which are in\n" ++
  "`Generated/AppendixB.lean`; only the 28 kept ones are compiled, as f3 … f30.)\n\n" ++
  "\n".intercalate (snd.map (cand "snd")) ++ "\n"

def batchHeader (b : Nat) (n : Nat) : String := s!"batch {b}: {n} conjectures"

def conjecturedFile (label : String) (cs : List CandTrace) : String :=
  let one (c : CandTrace) : String :=
    let head := s!"### {label} {c.index}  ::  {c.ty.pp}\n"
    let bs := (c.batches.zip c.results).zipIdx.map fun ((batch, r), b) =>
      let items := batch.zipIdx.map fun (cj, k) =>
        let status := if r.tried.any (·.1 == cj) then "tried" else "skipped (a stored lemma rewrites it)"
        s!"  [{b + 1}.{k + 1}] {status}\n    show: {cj.show}\n    db:   {dbAffirm cj.aff}\n" ++
        s!"    lean: {statementOnly datas s!"conj_{b + 1}_{k + 1}" cj}"
      batchHeader (b + 1) batch.length ++ "\n" ++ "\n".intercalate items
    head ++ "\n".intercalate bs ++ "\n"
  s!"# Conjectured ({label} search)\n\n" ++ "\n".intercalate (cs.map one)

def attemptedFile (label : String) (cs : List CandTrace) : String :=
  let one (c : CandTrace) : String :=
    let bs := c.results.zipIdx.map fun (r, b) =>
      let lines := r.tried.zipIdx.map fun ((cj, p), k) =>
        let outcome := if p.complete then s!"PROVED (size {p.size})"
          else s!"FAILED: {(proofReason p).getD "unknown"}"
        s!"  [{b + 1}.{k + 1}] {outcome}  {cj.show}"
      let chosen := match r.chosen.bind Proof.head with
        | some h => s!"  chosen: {h.show}"
        | none => "  chosen: none"
      s!"batch {b + 1}: {r.tried.length} attempts\n" ++ "\n".intercalate (lines ++ [chosen])
    s!"### {label} {c.index}  ::  {c.ty.pp}\n" ++ "\n".intercalate bs ++ "\n"
  s!"# Attempted ({label} search)\n\n" ++ "\n".intercalate (cs.map one)

/-- The text of the theorem the export prints for `name`, if there is one. -/
def theoremText (texts : List String) (name : String) : Option String :=
  texts.find? fun t => t.startsWith s!"theorem {name} "

def provedFile (label : String) (cs : List CandTrace) (keep : CandTrace → Bool)
    (nameOf : Nat → Option String) (texts : List String) : String :=
  let one (c : CandTrace) : String :=
    let kept := keep c
    let fname := nameOf c.index
    let lemmas := c.chosen.zipIdx.filterMap fun (p, i) =>
      p.head.map fun h =>
        let leanPart := match fname with
          | some f =>
            match theoremText texts s!"{sanitize f}_l{i + 1}" with
            | some t => s!"\n    lean ({f}_l{i + 1}):\n{indent t.trimRight}"
            | none => "\n    lean: (no theorem)"
          | none => "\n    lean: (function not kept: no definition exported, so no theorem)"
        s!"  lemma {i + 1} (size {p.size}): {h.show}\n    db:   {dbAffirm h.aff}{leanPart}"
    let head := s!"### {label} {c.index}  ::  {c.ty.pp}  " ++
      (match fname with | some f => s!"KEPT as {f}" | none => if kept then "kept" else "not kept")
    head ++ "\n" ++ "\n".intercalate lemmas ++ "\n"
  s!"# Proved ({label} search)\n\n" ++
  "(The de Bruijn terms use the candidate's own name `f`; a kept function is renamed f0, f1, … in\n" ++
  "the Lean text.)\n\n" ++ "\n".intercalate (cs.map one)

/-! ## Summary -/

def countBy (xs : List String) : List (String × Nat) :=
  xs.eraseDups.map fun x => (x, (xs.filter (· == x)).length)

def summaryOf (label : String) (cs : List CandTrace) (keep : CandTrace → Bool) : List String :=
  let batches := cs.flatMap (·.batches)
  let conjs := batches.flatMap id
  let tried := cs.flatMap fun c => c.results.flatMap (·.tried)
  let proved := tried.filter (·.2.complete)
  let failed := tried.filter (!·.2.complete)
  let reasons := countBy (failed.map fun (_, p) => (proofReason p).getD "unknown")
  [ s!"{label} search"
  , s!"  candidates:        {cs.length}"
  , s!"  kept:              {(cs.filter keep).length}"
  , s!"  batches:           {batches.length}"
  , s!"  conjectures:       {conjs.length}"
  , s!"  attempted:         {tried.length}  (skipped: {conjs.length - tried.length})"
  , s!"  proved attempts:   {proved.length}"
  , s!"  failed attempts:   {failed.length}" ]
  ++ (reasons.map fun (r, n) => s!"    {r}: {n}")
  ++ [s!"  lemmas chosen:     {(cs.flatMap (·.chosen)).filter (·.head.isSome) |>.length}"]

end MM.Trace
