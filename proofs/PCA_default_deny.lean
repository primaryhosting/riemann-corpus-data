/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` when the resource is in the
principal's scope, or the principal is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Default deny: with an empty scope and no escape hatches (no privileged
principals, no unowned resources), nothing is accessible. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hscope : ∀ c r, ¬ inScope c r) (hpriv : ∀ c, ¬ isPriv c)
    (hunowned : ∀ r, ¬ isUnowned r) (c : P) (r : R) :
    ¬ canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact hscope c r h
  · exact hpriv c h
  · exact hunowned r h

end PCA

#print axioms PCA.default_deny

