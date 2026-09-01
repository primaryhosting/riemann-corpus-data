/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA

section PCA

variable {P R : Type}

/-- Access policy: caller `c` may access row `r` when the row is in the caller's
scope, the caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Any caller can reach an unowned row (models the `IS NULL` hole). -/
theorem unowned_is_hole {inScope : P → R → Prop} {isPriv : P → Prop}
    {isUnowned : R → Prop} {c : P} {r : R} (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end PCA

end PCA

#print axioms PCA.unowned_is_hole

