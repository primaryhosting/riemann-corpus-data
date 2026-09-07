import Mathlib

/-! # The depth-holonomy LOOP MAP is an additive homomorphism.

Over the residue cycle `ZMod 6` with fiber `ZMod 6`, the transfer operator `K h` advances the
residue and, at the seam `j = 5 → 0`, increments the fiber depth by the holonomy `h ∈ ZMod 6`.
Winding the cycle once (`K h` applied six times) translates the fiber by exactly `h`, and this
loop-holonomy is an additive homomorphism `ZMod 6 → (translations of ZMod 6)`. -/

namespace Brockian.HolonomyHomomorphism

/-- The transfer operator: advance the residue by one and, at the seam `j = 5`, add the
    holonomy `h` to the fiber depth. -/
def K (h : ZMod 6) (x : ZMod 6 × ZMod 6) : ZMod 6 × ZMod 6 :=
  (x.1 + 1, x.2 + (if x.1 = 5 then h else 0))

/-- **Loop translates the fiber by `h`.** Winding the residue cycle once returns to the same
    residue and shifts the fiber depth by exactly the holonomy `h`. -/
theorem loop_translates (h : ZMod 6) (x : ZMod 6 × ZMod 6) :
    (K h)^[6] x = (x.1, x.2 + h) := by revert h x; decide

/-- **The loop-holonomy is an additive homomorphism.** Applying the `h'`-loop then the
    `h`-loop equals the `(h + h')`-loop: the holonomy composes additively. -/
theorem loop_homomorphism : ∀ (h h' : ZMod 6) (x : ZMod 6 × ZMod 6),
    (K h)^[6] ((K h')^[6] x) = (K (h + h'))^[6] x := by decide

/-- **The zero holonomy loop is the identity.** The homomorphism sends `0` to the identity
    translation. -/
theorem loop_identity : ∀ (x : ZMod 6 × ZMod 6), (K (0 : ZMod 6))^[6] x = x := by decide

/-- **Bundle.** The loop map both translates the fiber by `h` and composes additively — the
    two facts that make the depth-holonomy an additive homomorphism `ZMod 6 →` translations. -/
theorem loop_hom_bundle :
    (∀ (h : ZMod 6) x, (K h)^[6] x = (x.1, x.2 + h)) ∧
    (∀ (h h' : ZMod 6) x, (K h)^[6] ((K h')^[6] x) = (K (h + h'))^[6] x) :=
  ⟨loop_translates, loop_homomorphism⟩

end Brockian.HolonomyHomomorphism
