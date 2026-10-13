import MathematicalMethodology.Operational.Term

/-!
# Operational level: scoping

Syntactic checks on free variables, used by the checker (statements must be
well-scoped) and by the soundness proof.
-/

namespace MM

mutual
  /-- All free variables are `< n`. -/
  def Term.scoped (n : Nat) : Term → Bool
    | .var i => decide (i < n)
    | .con _ => true
    | .const _ => true
    | .app f a => f.scoped n && a.scoped n
    | .abs b => b.scoped (n + 1)
    | .cas s alts => s.scoped n && alts.scoped n

  def Alts.scoped (n : Nat) : Alts → Bool
    | .nil => true
    | .alt _ k b rest => b.scoped (n + k) && rest.scoped n
end

/-- No free variables. -/
def Term.closed (t : Term) : Prop := t.scoped 0 = true

mutual
  /-- Does de Bruijn variable `v` occur free? -/
  def Term.mentions (v : Nat) : Term → Bool
    | .var i => decide (i = v)
    | .con _ => false
    | .const _ => false
    | .app f a => f.mentions v || a.mentions v
    | .abs b => b.mentions (v + 1)
    | .cas s alts => s.mentions v || alts.mentions v

  def Alts.mentions (v : Nat) : Alts → Bool
    | .nil => false
    | .alt _ k b rest => b.mentions (v + k) || rest.mentions v
end

end MM
