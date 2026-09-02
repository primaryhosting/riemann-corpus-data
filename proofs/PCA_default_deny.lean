/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- A capability `c` can access a resource `r` when `r` lies in the scope of `c`,
or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Default deny: with an empty scope relation, no privileged principals and no
unowned resources, nothing is accessible. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hScope : ∀ c r, ¬ inScope c r) (hPriv : ∀ c, ¬ isPriv c) (hUnowned : ∀ r, ¬ isUnowned r)
    (c : P) (r : R) : ¬ canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact hScope c r h
  · exact hPriv c h
  · exact hUnowned r h

end

end PCA

#print axioms PCA.default_deny

