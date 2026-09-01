/-!
# No Escape No Leak
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_escape_no_leak
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource,
or the principal is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- With no privileged principals and no unowned resources, any granted access is in-scope. -/
theorem no_escape_no_leak (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (hpriv c)
  · exact absurd h (hunowned r)

end

end PCA

