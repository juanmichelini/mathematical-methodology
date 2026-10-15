import MathematicalMethodology.Strategic.FindLemmas

/-!
# The first search

Port of the first search of foundations `Main.hs`: `candidatosFstTeo` (find lemmas for each
candidate with the empty store), `candidatosFstSel` (keep the functions with more than three
lemmas), `namedFstSel` (call them `f0, f1, …`), `fstEnv`, `fstTEnv` and `fstRec` (the lemma
store the second search starts from).

Naming `f` as `f0` is done in Haskell by `multisubstitute`, which also *refreshes the names
of the binders* of the definition (the thesis shows `\d.\e. case d of {… g …}` for what was
`\b.\a. … c`).  Those names are what the second search must avoid when it names the fields
of an induction, so the same refresh is reproduced here (`renamedBinders`).

**Untrusted.**
-/

namespace MM

/-! ## Renaming a constant -/

mutual
  def Term.renameConst (a b : String) : Term → Term
    | .const f => .const (if f == a then b else f)
    | .app f x => .app (f.renameConst a b) (x.renameConst a b)
    | .abs t => .abs (t.renameConst a b)
    | .cas s alts => .cas (s.renameConst a b) (Alts.renameConst a b alts)
    | t => t
  def Alts.renameConst (a b : String) : Alts → Alts
    | .nil => .nil
    | .alt c n t rest => .alt c n (t.renameConst a b) (Alts.renameConst a b rest)
end

def Conj.renameConst (a b : String) (c : Conj) : Conj :=
  { c with aff := { c.aff with lhs := c.aff.lhs.renameConst a b, rhs := c.aff.rhs.renameConst a b } }

def SideComment.renameConst (a b : String) : SideComment → SideComment
  | .compute => .compute
  | .lemma r l bd => .lemma r (l.renameConst a b) (bd.map fun (i, t) => (i, t.renameConst a b))

def Comment.renameConst (a b : String) : Comment → Comment
  | .left s => .left (s.renameConst a b)
  | .right s => .right (s.renameConst a b)
  | .both s t => .both (s.renameConst a b) (t.renameConst a b)
  | c => c

mutual
  def Proof.renameConst (a b : String) : Proof → Proof
    | .fail => .fail
    | .done => .done
    | .step x c p => .step (x.renameConst a b) (c.renameConst a b) (p.renameConst a b)
    | .ind x c cs => .ind (x.renameConst a b) (c.renameConst a b) (renameCases a b cs)
  def renameCases (a b : String) : List (Comment × List Conj × Proof) →
      List (Comment × List Conj × Proof)
    | [] => []
    | (c, hs, p) :: r =>
      (c.renameConst a b, hs.map (·.renameConst a b), p.renameConst a b) :: renameCases a b r
end

mutual
  /-- Number of finished leaves of a proof (the `\done`s of Appendix B). -/
  def Proof.doneCount : Proof → Nat
    | .done => 1
    | .fail => 0
    | .step _ _ p => p.doneCount
    | .ind _ _ cs => casesDoneCount cs
  def casesDoneCount : List (Comment × List Conj × Proof) → Nat
    | [] => 0
    | (_, _, p) :: r => p.doneCount + casesDoneCount r
end

end MM

namespace MM.Strategic

open MM

/-! ## The binder names after `multisubstitute [("f", f0)]` -/

/-- The names Haskell gives the binders of a generated definition when `f` is renamed to
`fname`: the parameters (outermost first) and the fields of each alternative.  Each binder
takes the first fresh name that is not used by the binder itself, by what is under it, by the
substitution built so far (names and images). -/
def renamedBinders (def_ : Term) (fname : String) : List String × List (List String) :=
  let k := funArity def_
  let origParam (i : Nat) := letter (k - 1 - i)
  let origParams := (List.range k).map origParam
  let body := funBody def_
  let occName : Atm → Option String
    | .param i => some (origParam i)
    | .field j => some (letter (k + j))
    | .const f => some f
    | .con _ => none
  let occ := ((termAtoms k 0 body).filterMap occName)
  let (ps, sus) := (List.range k).foldl (fun (acc : List String × List (String × String)) j =>
      let (ps, sus) := acc
      let used := (origParam j) :: ((origParams.drop (j + 1)) ++ occ ++ sus.map (·.1) ++ sus.map (·.2))
      let h := (freshN used 1).headD "?"
      (ps ++ [h], (origParam j, h) :: sus)) ([], [("f", fname)])
  let fieldsOf : List (List String) :=
    match body with
    | .cas _ alts =>
      let rec go : Alts → List (List String)
        | .nil => []
        | .alt _ n b rest =>
          let vs := (List.range n).map fun j => letter (k + j)
          let altOcc := ((termAtoms k n b).filterMap occName)
          let used := vs ++ altOcc ++ sus.map (·.1) ++ sus.map (·.2)
          freshN used n :: go rest
      go alts
    | _ => []
  (ps, fieldsOf)

/-- The variable names a renamed definition uses (Haskell `usedVars`). -/
def renamedUsed (def_ : Term) (fname : String) : List String :=
  let k := funArity def_
  let (ps, fields) := renamedBinders def_ fname
  let consts := ((termAtoms k 0 (funBody def_)).filterMap fun
    | .const f => some (if f == "f" then fname else f)
    | _ => none)
  let fieldOcc : List String := match funBody def_ with
    | .cas _ alts =>
      let rec go (i : Nat) : Alts → List String
        | .nil => []
        | .alt _ n b rest =>
          let fs := fields.getD i []
          let occ := (termAtoms k n b).filterMap fun
            | .field j => fs[j]?
            | _ => none
          occ ++ go (i + 1) rest
      go 0 alts
    | _ => []
  sortStrings (ps ++ fieldOcc ++ consts).eraseDups

/-! ## Selecting and naming -/

/-- A function kept by the first search. -/
structure Selected where
  name : String
  def_ : Term
  ty : Ty
  proofs : List Proof
  /-- Binder names after the renaming (Haskell's). -/
  params : List String
  fields : List (List String)
  /-- The variable names the renamed definition uses (Haskell `usedVars`). -/
  used : List String

def Selected.lemmas (s : Selected) : List Conj := s.proofs.filterMap Proof.head

/-- Haskell `candidatosFstSel` and `namedFstSel`: candidates with more than three lemmas
(searched with the empty store), named `f0, f1, …`. -/
def selectFirst (n : Nat) : List Selected :=
  let kept := candidatosFst.filterMap fun (f, ty) =>
    let tenv : TEnv := (Term.const "f", ty) :: cerothTEnv
    let cx := mkPCtx [("f", f)] datas (defNamesOf f)
    let bs := findlemas cx tenv n {} "f"
    let ps := bs.filterMap (·.chosen)
    if ps.length > 3 then some (f, ty, ps) else none
  kept.zipIdx.map fun ((f, ty, ps), i) =>
    let name := s!"f{i}"
    let (params, fields) := renamedBinders f name
    ⟨name, f.renameConst "f" name, ty, ps.map (·.renameConst "f" name), params, fields,
      renamedUsed f name⟩

/-- Finished proofs of a function (the `\done`s of Appendix B). -/
def Selected.done (s : Selected) : Nat := (s.proofs.map Proof.doneCount).foldl (· + ·) 0

/-- A function as the oracle scripts print it: definition (with Haskell's binder names),
type, variable names used, lemmas, finished proofs. -/
def Selected.dump (s : Selected) : String :=
  "\n".intercalate (
    [ s!"## {s.name}"
    , s!"def {showFunN s.params s.fields s.name s.def_}"
    , s!"type {s.ty.pp}"
    , s!"used {" ".intercalate s.used}" ]
    ++ s.lemmas.map (fun l => s!"lemma {l.show}") ++ [s!"done {s.done}"])

/-- Haskell `fstEnv`. -/
def fstEnv (sel : List Selected) : Env := sel.map fun s => (s.name, s.def_)

/-- Haskell `fstTEnv`. -/
def fstTEnv (sel : List Selected) : TEnv :=
  cerothTEnv ++ sel.map fun s => (Term.const s.name, s.ty)

/-- Haskell `fstRec`: the lemmas of all selected functions, in order, in the store. -/
def fstRec (sel : List Selected) : HRec :=
  HRec.addAll (fstEnv sel) {} (sel.flatMap Selected.lemmas)

end MM.Strategic
