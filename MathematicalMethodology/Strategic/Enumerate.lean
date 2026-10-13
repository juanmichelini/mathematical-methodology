import MathematicalMethodology.Strategic.Syntax

/-!
# Enumeration of data types and functions

Port of the enumeration half of foundations `code/Propose.hs` (`enumSimpleFiniteTypes`,
`enumContainerFiniteTypes`, `enumRecursiveTypes`, `enumContainerRecTypes`, `armarTip`,
`armarPar`, `dataAEsquema`, `enumApp`, `enumAppRec`, `enumFun`) and of `Main.datas`.

**Untrusted.**  Every function proposed here is only a candidate; a lemma about it still
has to be accepted by `Cert.check`.  Nothing trusted imports this file.

Order matters: the later search stages keep the first candidates they find, so the lists
below follow the Haskell list comprehensions exactly (see `hilar` for the order of nested
generators).
-/

namespace MM.Strategic

/-! ## Names -/

/-- Haskell `infiniteTVars`, truncated: `a b c d e 0 1 2 …`. -/
def tvarPool : List String := ["a", "b", "c", "d", "e"] ++ (List.range 40).map toString

/-- Haskell `infiniteVars`, truncated: `a … z`, `a0 … z0`, `a1 … z1`, … -/
def varPool : List String :=
  ("" :: (List.range 12).map toString).flatMap fun sfx =>
    "abcdefghijklmnopqrstuvwxyz".toList.map fun ch => ch.toString ++ sfx

/-! ## Data types -/

def most1 : List String → String
  | [] => "_"
  | xs => String.mk (("_".intercalate xs).toList.filter (· ≠ 't'))

def most2 (xs : List (List String)) : String := ",".intercalate (xs.map most1)

def enumSimpleFiniteTypes (n : Nat) : DatasH :=
  (s!"F{n}", (List.range n).map fun i => (s!"F{n}.{i + 1}", []))

def enumContainerFiniteTypes (n c : Nat) : List DatasH :=
  (dist n (tvarPool.take c)).map fun d =>
    (s!"C{most2 d}", d.map fun e => (s!"C{most2 d}.{most1 e}", e.map Ty.var))

def enumRecursiveTypes (n r : Nat) : List DatasH :=
  (dist n (List.replicate r "rec")).map fun d =>
    (s!"C{most2 d}", d.map fun e => (s!"C{most2 d}.{d.idxOf e}", e.map Ty.var))

/-- Haskell `swap a b z`. -/
def swapTy (a b z : Ty) : Ty := if a == z then b else if b == z then a else z

/-- `enumContainerRecTypes n c r`: `n` constructors, `c` type variables ("containers")
and `r` recursive slots in total; fields are drawn from both. -/
def enumContainerRecTypes (n c r : Nat) : List DatasH :=
  let rss := (dist n (List.replicate r "R")).map sortLists |>.eraseDups
  let css := (dist n (tvarPool.take c)).map sortLists |>.eraseDups
  rss.flatMap fun rs => css.flatMap fun cs =>
    let d := List.zipWith (· ++ ·) cs rs
    let name := s!"C{most2 d}"
    let d' := d.map fun e => e.map fun v =>
      swapTy (.var "R") (.con name) (.var v)
    [(name, (d'.zip ((List.range d'.length).map toString)).map fun (e, k) =>
      (s!"{name}.{k}", e))]

/-- `Main.datas`: two constructors, `c ∈ {0,1}` type variables, `r ∈ {0,1}` recursive
slots. -/
def datas : List DatasH :=
  [2].flatMap fun cantcons => [0, 1].flatMap fun canrec => [0, 1].flatMap fun canemb =>
    enumContainerRecTypes cantcons canrec canemb

/-- `Main.cerothTEnv`: the constructors of `datas`, as terms with their types. -/
def cerothTEnv : TEnv :=
  (datas.flatMap DatasH.toC).map fun (c, t) => (NTerm.con c, t)

/-! ## Function types and parameters -/

/-- Haskell `armarTip n xs`: all `x₁ → … → xₙ → t` with `xᵢ, t ∈ xs`. -/
def armarTip : Nat → List Ty → List Ty
  | 0, xs => xs
  | n + 1, xs => xs.flatMap fun x => (armarTip n xs).map fun t => .com x t

/-- Haskell `armarPar`: names for the parameters of a function type, in order, with
their types.  Each name is the first fresh one not used by the later parameters. -/
def armarPar : Ty → List (String × Ty)
  | .com x y =>
    let b := armarPar y
    let v := (varPool.find? fun w => !(b.map Prod.fst).contains w).getD "?"
    (v, x) :: b
  | _ => []

/-! ## Recursion scheme of a data type -/

/-- Haskell `dataAEsquema`: for the type `o`, the constructors with their field
variables, and for each constructor the typed expressions available in its branch: the
recursive calls `f v` (of the result type `b`) and the field variables. -/
structure Scheme where
  cons : List (String × List String)
  avail : List (List (NTerm × Ty))

def Scheme.mkCase (s : Scheme) (scrut : NTerm) (bodies : List NTerm) : NTerm :=
  .cas scrut (NAlts.ofList ((s.cons.zip bodies).map fun ((c, vs), b) => (c, vs, b)))

def dataAEsquema (d : DatasH) (vs : List String) (f : NTerm) (ty : Ty) : Option Scheme :=
  match ty with
  | .com a b =>
    if Ty.con d.1 == a then
      let para := d.2.map fun (_, fs) => vs.zip fs
      let tvarpara := para.map fun p => p.map fun (v, t) => (NTerm.var v, t)
      let recs := tvarpara.map fun p =>
        (p.filter fun (_, t) => t == a).map fun (e, _) => (NTerm.app f e, b)
      some ⟨(d.2.zip para).map fun ((c, _), p) => (c, p.map Prod.fst),
            List.zipWith (· ++ ·) recs tvarpara⟩
    else none
  | _ => none

/-! ## Expressions of a type -/

/-- Atoms of `tts` whose type ends in `s`, with the parameter types that remain. -/
def relevant (s : Ty) (tts : TEnv) : List (NTerm × List Ty) :=
  tts.filterMap fun (e, t) => (s.returnsM t).map fun args => (e, args)

/-- Haskell `enumApp n s tts`: applications of depth at most `n` of the typed atoms
`tts` that have type `s`; atoms of type `s` come first, then the applications. -/
def enumApp : Nat → Ty → TEnv → List NTerm
  | 0, s, tts => ((relevant s tts).filter fun (_, args) => args.isEmpty).map Prod.fst
  | n + 1, s, tts =>
    let rel := relevant s tts
    let base := rel.filter fun (_, args) => args.isEmpty
    let funs := rel.filter fun (_, args) => !args.isEmpty
    let fargs := (funs.map fun (f, args) => (f, args.map fun u => enumApp n u tts)).filter
      fun (_, cs) => !cs.any List.isEmpty
    base.map Prod.fst ++
      fargs.flatMap fun (f, cs) => (hilar cs).map fun cargs => f.mkApp cargs

/-- Haskell `enumAppRec`, with the rewrite-rule filter (`isNothing . applyRecT`) abstracted
as a predicate `reject`: terms that a known rule could rewrite are dropped.  With the
empty rule set of `Main.cerothRec` nothing is rejected. -/
def enumAppRec (reject : NTerm → Bool) (n : Nat) (s : Ty) (tts : TEnv) : List NTerm :=
  (enumApp n s tts).filter fun t => !reject t

/-- Haskell `repiteAtmHasta n`: keep the terms in which no atom occurs `n` or more times. -/
def repiteAtmHasta (n : Nat) (ts : List NTerm) : List NTerm :=
  ts.filter fun t => let as := t.atoms; as.all fun a => as.count a < n

/-- Haskell `enumFun rec f tipo datas ls`: the functions `f : tipo` defined by one `case`
on the first parameter, whose branches are applications built from the other parameters,
the fields, the recursive calls and the environment `ls`. -/
def enumFun (reject : NTerm → Bool) (f : String) (tipo : Ty) (ds : List DatasH)
    (ls : TEnv) : List NTerm :=
  match tipo with
  | .com (.con x) _ =>
    match ds.find? (·.1 == x) with
    | none => []
    | some d =>
      let vs := armarPar tipo
      let names := vs.map Prod.fst
      let vs2 : TEnv := vs.map fun (v, t) => (NTerm.var v, t)
      let free := varPool.filter fun v => !names.contains v
      match dataAEsquema d free (NTerm.var f) tipo, vs2 with
      | some sch, (scrut, _) :: others =>
        let res := tipo.parsAndRet.2
        let cas' := sch.avail.map fun cs => cs.map fun (e, t) =>
          let (g, gs) := e.listParams
          if g == NTerm.var f then ((NTerm.var f).mkApp (gs ++ others.map Prod.fst), res)
          else (e, t)
        let bodies := cas'.map fun c => enumAppRec reject 2 tipo.lastRet (others ++ c ++ ls)
        let apps := (hilar bodies).map (sch.mkCase scrut)
        repiteAtmHasta 3 (apps.map fun a => names.foldr NTerm.abs a)
      | _, _ => []
  | _ => []

/-! ## Candidates of the first search (`Main.candidatosFst`) -/

/-- Data types the first search uses: `datas!!1` and `datas!!3`. -/
def fstTypes : List Ty := [datas[1]!, datas[3]!].map fun d => Ty.con d.1

def candidatosFst : List (NTerm × Ty) :=
  ([1, 2].flatMap fun aridad => (armarTip aridad fstTypes).flatMap fun tipo =>
    (enumFun (fun _ => false) "f" tipo datas cerothTEnv).map fun e => (e, tipo)).filter
    fun (e, _) => e.contains (.var "f")

end MM.Strategic
