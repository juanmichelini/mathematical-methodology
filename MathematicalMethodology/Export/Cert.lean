import MathematicalMethodology.Export.Proofs
import MathematicalMethodology.Examples.Lists
import MathematicalMethodology.Pretty

/-!
# Export of checked certificates as Lean theorems

Prints a development of `Cert`s (the objects `Cert.check` accepts) as plain Lean:
the data types and functions of its `Ctx` as `inductive`/`def`, and each lemma as a `theorem`
with a tactic proof, so that **Lean's kernel re-checks the development independently of
`Cert.check`**.  `Cert.check_sound` is about our own `Conv`, not Lean's `=`; this export is the
bridge, validated by compilation (issue #35).  This is the export of the *checker's* proofs;
`Export/Proofs.lean` exports the Haskell-style proofs of the search.

The exporter replays the checker (`computeWide`, `rewriteFirst`, `inductCases`) and refuses
to print a development the checker rejects.  **Untrusted**: nothing trusted imports it.

| `Cert` step | tactic |
|---|---|
| `refl` | `try rfl` |
| `compute s` | `change <lhs'> = <rhs'>` (definitional unfolding; the new goal is the checker's) |
| `rewrite s i rev` | `conv => lhs; rw [← rule args]` (`rhs` for the right side, `←` when `rev`); `args` is the instance the checker's matcher found |
| `induct v` | `induction x with \| ctor fields ih… =>`; the checker's rigid induction hypotheses are Lean's, with the other variables fixed |

Unlike the search export, no step is `try`d, except the final `rfl` (a `conv` already closes a
goal whose sides became equal): an unexpected shape fails to compile.
-/

namespace MM.Export

open MM MM.Strategic

/-! ## Data types and functions of a `Ctx` -/

/-- Lean name of a data type of a context (`List` would clash with the core type). -/
def exTy (s : String) : String := "Ex" ++ s

/-- A type name of a context as a prototype type: declared data types by their (renamed)
name, undeclared ones are opaque and become type parameters. -/
def ctxTy (cx : Ctx) (s : String) : Ty :=
  if cx.data.any (·.name == s) then .con (exTy s) else .var s

def ctxDatas (cx : Ctx) : List DatasH :=
  cx.data.map fun d => (exTy d.name, d.ctors.map fun (c, fs) => (c, fs.map (ctxTy cx)))

def sigTy (cx : Ctx) (args : List String) (res : String) : Ty :=
  args.foldr (fun a t => .com (ctxTy cx a) t) (ctxTy cx res)

/-! ## Rewriting with the instance -/

/-- `Rule.tryRoot`, also returning the binding the matcher found. -/
def tryRootB (cx : Ctx) (ctx : List String) (r : Rule) (t : Term) :
    Option (Term × Binding) :=
  if r.tys.isEmpty then
    if t = r.lhs then some (r.rhs, []) else none
  else if r.lhs.isFO && r.rhs.isFO then
    match matchFO r.lhs t [] with
    | some b =>
      if (List.range r.tys.length).all (fun i =>
          (b.find? (·.1 = i)).any fun p =>
            decide (cx.typeOf ctx p.2 = some ([], r.tys.getD i "")))
      then (r.rhs.instFO b).map fun u => (u, b) else none
    | none => none
  else none

/-- `Term.rewriteFirst`, also returning the binding.  Same traversal order. -/
def rewriteFirstB (cx : Ctx) (ctx : List String) (r : Rule) :
    Term → Option (Term × Binding)
  | .app f a =>
    match tryRootB cx ctx r (.app f a) with
    | some u => some u
    | none =>
      match rewriteFirstB cx ctx r f with
      | some (f', b) => some (.app f' a, b)
      | none => (rewriteFirstB cx ctx r a).map fun (a', b) => (.app f a', b)
  | .cas s alts =>
    match tryRootB cx ctx r (.cas s alts) with
    | some u => some u
    | none => (rewriteFirstB cx ctx r s).map fun (s', b) => (.cas s' alts, b)
  | t => tryRootB cx ctx r t

/-! ## Proofs -/

/-- `k` names `f<m>` that are not in `used`. -/
def freshNames (used : List String) (k : Nat) : List String :=
  let rec go (fuel m : Nat) (acc : List String) : List String :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      if acc.length ≥ k then acc.reverse
      else
        let n := s!"f{m}"
        if used.contains n then go fuel (m + 1) acc else go fuel (m + 1) (n :: acc)
  go (k + used.length + 1) 0 []

def printable (t : Term) : Except String Unit :=
  if t.isFO then .ok () else .error "a goal is not first-order; cannot print it"

/-- Arguments of a lemma instance, in the order of its variables. -/
def instArgs (ds : List DatasH) (names : List String) (n : Nat) (b : Binding) :
    Except String String := do
  let mut out := ""
  for i in List.range n do
    match b.find? (·.1 = i) with
    | some (_, t) =>
      let s := leanOpen ds names t
      out := out ++ (match t with | .app .. => s!" ({s})" | _ => s!" {s}")
    | none => throw s!"lemma variable {i} is not bound"
  return out

def sideName : Side → String
  | .lhs => "lhs"
  | .rhs => "rhs"

mutual
  /-- Tactic lines, one per step, for `c` proving `g` with `rules` (named `rn`). -/
  def certLines (cx : Ctx) (ds : List DatasH) (rn : List String) (rules : List Rule)
      (names : List String) (ind : String) (g : Affirm) : Cert → Except String (List String)
    | .refl => .ok [ind ++ "try rfl"]
    | .compute s rest =>
      match (s.get g).computeWide cx.env computeFuel with
      | none => .error "compute: no result"
      | some t' => do
        let g' := s.set g t'
        printable g'.lhs
        printable g'.rhs
        let rest' ← certLines cx ds rn rules names ind g' rest
        return (ind ++ s!"change {leanOpen ds names g'.lhs} = {leanOpen ds names g'.rhs}") :: rest'
    | .rewrite s i rev rest =>
      match rules[i]?, rn[i]? with
      | some r, some nm =>
        let r' := r.orient rev
        match rewriteFirstB cx g.ctx r' (s.get g) with
        | none => .error s!"rewrite: rule {i} does not apply"
        | some (t', b) => do
          unless (s.get g).rewriteFirst cx g.ctx r' == some t' do
            throw "rewrite: the instance found differs from the checker's"
          let g' := s.set g t'
          printable g'.lhs
          printable g'.rhs
          let args ← if r.tys.isEmpty then pure "" else instArgs ds names r.tys.length b
          let arrow := if rev then "← " else ""
          let rest' ← certLines cx ds rn rules names ind g' rest
          return (ind ++ s!"conv => {sideName s}; rw [{arrow}{nm}{args}]") :: rest'
      | _, _ => .error s!"rewrite: no rule {i}"
    | .induct v cases =>
      match g.ctx[v]?, names[v]? with
      | some ty, some x =>
        match cx.data.find? (·.name = ty) with
        | none => .error s!"induct: {ty} is not a data type"
        | some d => do
          let others := names.eraseIdx v
          let used := names
          let sub := inductCases g v d rules
          let pairs := rn.zip rules
          let old := (pairs.filter fun p => !p.2.tys.isEmpty).map (·.1)
          let hdr := ind ++ s!"induction {x} with"
          let body ← certsLines cx ds old others used ind d.name d.ctors sub cases
          return hdr :: body
      | _, _ => .error "induct: no such variable"

  /-- One `| ctor … =>` block per constructor. -/
  def certsLines (cx : Ctx) (ds : List DatasH) (old : List String) (others used : List String)
      (ind dname : String) :
      List (String × List String) → List (Affirm × List Rule) → Certs →
        Except String (List String)
    | [], [], .nil => .ok []
    | (c, fields) :: cs, (g', rules') :: gs, .cons cert rest => do
      let fns := freshNames used fields.length
      let names' := others ++ fns
      let recs := (List.range fields.length).filterMap fun j =>
        if fields.getD j "" = dname then some (fns.getD j "_") else none
      let ihs := recs.map ("ih_" ++ ·)
      let line := ind ++ s!"| {sanitize c}" ++ String.join ((fns ++ ihs).map (" " ++ ·)) ++ " =>"
      let inner ← certLines cx ds (ihs ++ old) rules' names' (ind ++ "  ") g' cert
      let more ← certsLines cx ds old others used ind dname cs gs rest
      return line :: inner ++ more
    | _, _, _ => .error "induct: constructors and certificates do not match"
end

/-- `theorem name {…} (x : T) … : lhs = rhs := by` for a statement of a context. -/
def certHeader (cx : Ctx) (ds : List DatasH) (name : String) (g : Affirm) : String :=
  let names := (List.range g.ctx.length).map freeName
  let tys := g.ctx.map fun t => if cx.data.any (·.name == t) then exTy t else t
  let ps := (tys.flatMap (ctxParams ds) ++ termParams ds g.lhs ++ termParams ds g.rhs).eraseDups
  let implicit := ps.map fun p => s!" \{{paramName p} : Type}"
  let binders := (names.zip tys).map fun (n, t) => s!" ({n} : {renderCtxTy ds t})"
  s!"theorem {name}{String.join implicit}{String.join binders} :\n    " ++
    leanOpen ds names g.lhs ++ " = " ++ leanOpen ds names g.rhs ++ " := by"

/-- The theorems of a development, in order; each is a lemma for the later ones. -/
def certTheorems (cx : Ctx) (ds : List DatasH) :
    List (String × Affirm × Cert) → List String → List Rule → Except String (List String)
  | [], _, _ => .ok []
  | (name, g, c) :: rest, rn, rules => do
    unless g.lhs.isFO && g.rhs.isFO do throw s!"{name}: the statement is not first-order"
    let names := (List.range g.ctx.length).map freeName
    let lines ← certLines cx ds rn rules names "  " g c
    let thm := "\n".intercalate (certHeader cx ds name g :: lines) ++ "\n"
    let more ← certTheorems cx ds rest (rn ++ [name]) (rules ++ [g.toRule])
    return thm :: more

/-- A whole Lean file for a development, or the reason it cannot be exported (the checker
rejects it, or a step has no tactic). -/
def exportCerts (title ns : String) (cx : Ctx) (dev : List (String × Affirm × Cert)) :
    Except String String := do
  match checkDevelopment cx dev [] with
  | .error e => throw s!"the checker rejects the development: {e}"
  | .ok _ => pure ()
  let ds := ctxDatas cx
  let funs ← cx.env.mapM fun (f, t) =>
    match cx.funSig f with
    | some (args, res) => pure (exportFun ds (sanitize f) (sigTy cx args res) t)
    | none => throw s!"{f}: no signature"
  let thms ← certTheorems cx ds dev [] []
  return s!"-- {title}\n-- Generated by `lake exe export-lean lists`; do not edit by hand (a guard in\n" ++
    "-- `Examples/ExportLists.lean` checks that this file equals the generator's output).\n\n" ++
    s!"set_option linter.unusedVariables false\n\nnamespace {ns}\n\n" ++
    "\n".intercalate (ds.map (exportData ds)) ++ "\n" ++ "\n".intercalate funs ++ "\n" ++
    "\n".intercalate thms ++ s!"\nend {ns}\n"

/-- The list development of `Examples/Lists.lean`. -/
def listsFile : Except String String :=
  exportCerts "rev (rev xs) = xs and its lemmas: the certificates of Cert.check as Lean theorems."
    "ListsEx" MM.Examples.listCtx MM.Examples.development

/-- Did the export succeed with exactly this text? -/
def exportIs (r : Except String String) (txt : String) : Bool :=
  match r with
  | .ok t => t == txt
  | .error _ => false

end MM.Export
