import MathematicalMethodology.Strategic.Syntax

/-!
# Enumeration of data types and functions

Port of the enumeration half of foundations `code/Propose.hs` (`enumSimpleFiniteTypes`,
`enumContainerFiniteTypes`, `enumRecursiveTypes`, `enumContainerRecTypes`, `armarTip`,
`dataAEsquema`, `enumApp`, `enumAppRec`, `enumFun`) and of `Main.datas`.

**Untrusted.**  Every function proposed here is only a candidate; a lemma about it still
has to be accepted by `Cert.check`.  Nothing trusted imports this file.

Order matters: the later search stages keep the first candidates they find, so the lists
below follow the Haskell list comprehensions exactly (see `hilar` for the order of nested
generators).
-/

namespace MM.Strategic

/-! ## Names of type variables -/

/-- Haskell `infiniteTVars`, truncated: `a b c d e 0 1 2 …`. -/
def tvarPool : List String := ["a", "b", "c", "d", "e"] ++ (List.range 40).map toString

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
  (datas.flatMap DatasH.toC).map fun (c, t) => (Term.con c, t)

/-! ## Function types and parameters -/

/-- Haskell `armarTip n xs`: all `x₁ → … → xₙ → t` with `xᵢ, t ∈ xs`. -/
def armarTip : Nat → List Ty → List Ty
  | 0, xs => xs
  | n + 1, xs => xs.flatMap fun x => (armarTip n xs).map fun t => .com x t

/-! ## Recursion scheme of a data type

Inside the alternative of a constructor of arity `n`, field `j` (from the left) is
`var (n-1-j)`; the parameters of the function follow, so parameter `i` of `k` is
`var (k-1-i + n)`. -/

/-- Haskell `dataAEsquema`: for the type `o`, the constructors with their arity, and for
each constructor the typed expressions available in its branch: the recursive calls `f v`
(of the result type `b`) and the field variables. -/
structure Scheme where
  cons : List (String × Nat)
  avail : List (List (Term × Ty))

def Scheme.mkCase (s : Scheme) (scrut : Term) (bodies : List Term) : Term :=
  .cas scrut ((s.cons.zip bodies).foldr (fun ((c, n), b) rest => .alt c n b rest) .nil)

def dataAEsquema (d : DatasH) (f : Term) (ty : Ty) : Option Scheme :=
  match ty with
  | .com a b =>
    if Ty.con d.1 == a then
      -- per constructor: its fields as (variable, type), by position from the left
      let para := d.2.map fun (_, fs) =>
        (fs.zipIdx.map fun (t, j) => (Term.var (fs.length - 1 - j), t))
      let recs := para.map fun p =>
        (p.filter fun (_, t) => t == a).map fun (e, _) => (Term.app f e, b)
      some ⟨d.2.map fun (c, fs) => (c, fs.length), List.zipWith (· ++ ·) recs para⟩
    else none
  | _ => none

/-! ## Expressions of a type -/

/-- Atoms of `tts` whose type ends in `s`, with the parameter types that remain. -/
def relevant (s : Ty) (tts : TEnv) : List (Term × List Ty) :=
  tts.filterMap fun (e, t) => (s.returnsM t).map fun args => (e, args)

/-- Haskell `enumApp n s tts`: applications of depth at most `n` of the typed atoms
`tts` that have type `s`; atoms of type `s` come first, then the applications. -/
def enumApp : Nat → Ty → TEnv → List Term
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
def enumAppRec (reject : Term → Bool) (n : Nat) (s : Ty) (tts : TEnv) : List Term :=
  (enumApp n s tts).filter fun t => !reject t

/-- Haskell `repiteAtmHasta n`, for the bodies of a function with `k` parameters: keep the
terms in which no atom occurs `n` or more times.  Atoms are counted by position (see
`Atm`), so field `j` of one constructor is the same atom as field `j` of another. -/
def repiteAtmHasta (k n : Nat) (ts : List Term) : List Term :=
  ts.filter fun t => let as := termAtoms k 0 t; as.all fun a => as.count a < n

/-- Haskell `enumFun rec f tipo datas ls`: the functions `f : tipo` defined by one `case`
on the first parameter, whose branches are applications built from the other parameters,
the fields, the recursive calls and the environment `ls` (closed terms). -/
def enumFun (reject : Term → Bool) (f : String) (tipo : Ty) (ds : List DatasH)
    (ls : TEnv) : List Term :=
  match tipo with
  | .com (.con x) _ =>
    match ds.find? (·.1 == x) with
    | none => []
    | some d =>
      let (ptys, res) := tipo.parsAndRet
      let k := ptys.length
      match dataAEsquema d (.const f) tipo with
      | none => []
      | some sch =>
        -- parameters after the first, as seen from an alternative of arity `n`
        let others (n : Nat) : TEnv :=
          (ptys.zipIdx.drop 1).map fun (t, i) => (Term.var (k - 1 - i + n), t)
        let bodies := (sch.cons.zip sch.avail).map fun ((_, n), avail) =>
          let cas' := avail.map fun (e, t) =>
            let (g, gs) := e.spine
            if g == .const f then ((Term.const f).mkApp (gs ++ (others n).map Prod.fst), res)
            else (e, t)
          enumAppRec reject 2 tipo.lastRet (others n ++ cas' ++ ls)
        let apps := (hilar bodies).map (sch.mkCase (.var (k - 1)))
        (repiteAtmHasta k 3 apps).map fun a => (List.range k).foldl (fun t _ => .abs t) a
  | _ => []

/-! ## Candidates of the first search (`Main.candidatosFst`) -/

/-- Data types the first search uses: `datas!!1` and `datas!!3`. -/
def fstTypes : List Ty := [1, 3].filterMap fun i => (datas[i]?).map fun d => Ty.con d.1

def candidatosFst : List (Term × Ty) :=
  ([1, 2].flatMap fun aridad => (armarTip aridad fstTypes).flatMap fun tipo =>
    (enumFun (fun _ => false) "f" tipo datas cerothTEnv).map fun e => (e, tipo)).filter
    fun (e, _) => mentions "f" e

end MM.Strategic
