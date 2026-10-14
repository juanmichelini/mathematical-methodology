import MathematicalMethodology.Strategic.FirstSearch

/-!
# The second search

Port of the second search of foundations `Main.hs`: `candidatosSnd` (functions that use the
recursive call *and* some function found by the first search, enumerated with the first
search's lemma store filtering the bodies), `candidatosSndTeo` (find lemmas for each, with
the first search's store and environment), `candidatosSndSel` (keep those with at least two
lemmas whose proof starts with an induction), `namedSndSel` (call them `f3, f4, …`).

**Untrusted.**
-/

namespace MM.Strategic

open MM

/-- Haskell `candidatosSndUni`. -/
def candidatosSndUni (sel : List Selected) : List (Term × Ty) :=
  let rec_ := fstRec sel
  ((armarTip 1 fstTypes).flatMap fun tipo =>
    (enumFun (fun names t => applyRecT rec_ names t) "f" tipo datas (fstTEnv sel)).map fun f =>
      (f, tipo)).filter fun (e, _) =>
    mentions "f" e && sel.any fun s => mentions s.name e

/-- Haskell `candidatosSndBin`: also, the second parameter occurs at least twice. -/
def candidatosSndBin (sel : List Selected) : List (Term × Ty) :=
  let rec_ := fstRec sel
  ((armarTip 2 fstTypes).flatMap fun tipo =>
    (enumFun (fun names t => applyRecT rec_ names t) "f" tipo datas (fstTEnv sel)).map fun f =>
      (f, tipo)).filter fun (e, _) =>
    mentions "f" e &&
    (((termAtoms 2 0 (funBody e)).filter (· == Atm.param 1)).length ≥ 2) &&
    sel.any fun s => mentions s.name e

/-- Haskell `candidatosSnd`. -/
def candidatosSnd (sel : List Selected) : List (Term × Ty) :=
  candidatosSndUni sel ++ candidatosSndBin sel

/-- Haskell `containsIndc`: the proof starts with an induction. -/
def Proof.startsWithInduction : Proof → Bool
  | .ind .. => true
  | _ => false

/-- Haskell `candidatosSndTeo`/`candidatosSndSel`/`namedSndSel`: lemmas for each candidate
(environment and store of the first search), kept if at least two of the lemmas are proved
by induction, named `f3, f4, …`. -/
def selectSecond (fst : List Selected) (n : Nat) : List Selected :=
  let env0 := fstEnv fst
  let tenv0 := fstTEnv fst
  let rec0 := fstRec fst
  let used0 := fst.flatMap (·.used)
  let kept := (candidatosSnd fst).filterMap fun (f, ty) =>
    let cx := mkPCtx (("f", f) :: env0) datas (defNamesOf f ++ used0)
    let bs := findlemas cx ((Term.const "f", ty) :: tenv0) n rec0 "f"
    let ps := bs.filterMap (·.chosen)
    if (ps.filter Proof.startsWithInduction).length ≥ 2 then some (f, ty, ps) else none
  kept.zipIdx.map fun ((f, ty, ps), i) =>
    let name := s!"f{fst.length + i}"
    let (params, fields) := renamedBinders f name
    ⟨name, f.renameConst "f" name, ty, ps.map (·.renameConst "f" name), params, fields,
      renamedUsed f name⟩

end MM.Strategic
