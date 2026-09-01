/-!
# Priv Is Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.priv_is_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA

section PCA

variable {P R : Type}

/-- A caller `c` can access a resource `r` when the resource is in the caller's scope,
or the caller is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A privileged caller always has access (models the admin bypass). -/
theorem priv_is_escape (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : isPriv c) : canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inl h)

end PCA

end PCA

#print axioms PCA.priv_is_escape

