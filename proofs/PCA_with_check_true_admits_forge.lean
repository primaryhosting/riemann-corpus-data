/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps (Lean)
Target: PCA.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c`
is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits every principal/row pair: with
`canWrite := fun _ _ => True`, every principal may write every row, so the
policy models "forge any row". -/
theorem with_check_true_admits_forge
    (canWrite : P → R → Prop) (hcanWrite : canWrite = fun (_ : P) (_ : R) => True) :
    ∀ (c : P) (r : R), canWrite c r := by
  subst hcanWrite
  intro c r
  trivial

end PCA

end PCA

