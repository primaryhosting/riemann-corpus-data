/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including
-- module doc comments. Since the required header comment must begin the file, no
-- `import` line can follow it; the development below is self-contained and needs
-- nothing beyond core Lean (it is, of course, also valid in a Mathlib project).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- A principal `c` may access a resource `r` when the resource is in the
principal's scope, or the principal is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **Default deny**: with an empty scope relation, no privileged principals and no
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

