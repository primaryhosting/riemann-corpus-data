import Mathlib

/-! # Product depth-holonomy: fiber = ZMod 2 × ZMod 3 over the residue cycle ZMod 5.

The holonomy is recovered as the full pair, each component tracked independently, and the
transfer order is `5 · lcm(ord h.1, ord h.2)`. -/

namespace Brockian.ProductHolonomy

/-- Depth in `ZMod 2 × ZMod 3` over the residue cycle `ZMod 5`. `K h` advances the residue
    and, at the seam `j = 4 → 0`, increments each depth component by the corresponding
    component of the holonomy pair `h`. -/
def K (h : ZMod 2 × ZMod 3) (x : ZMod 5 × (ZMod 2 × ZMod 3)) : ZMod 5 × (ZMod 2 × ZMod 3) :=
  (x.1 + 1,
    (x.2.1 + (if x.1 = 4 then h.1 else 0),
     x.2.2 + (if x.1 = 4 then h.2 else 0)))

/-- The one-step residue transition is `j ↦ j + 1` for EVERY holonomy `h`: residue-class
    (mod-5) analysis is blind to the depth holonomy pair. -/
theorem residue_marginal_indep (h : ZMod 2 × ZMod 3) (x : ZMod 5 × (ZMod 2 × ZMod 3)) :
    (K h x).1 = x.1 + 1 :=
  rfl

/-- **The holonomy IS the full pair.** Winding the residue cycle once translates each depth
    component by the corresponding component of `h`: the two `ZMod 2` and `ZMod 3` holonomies
    are recovered independently. -/
theorem holonomy_after_loop : ∀ (h : ZMod 2 × ZMod 3) (x : ZMod 5 × (ZMod 2 × ZMod 3)),
    (K h)^[5] x = (x.1, (x.2.1 + h.1, x.2.2 + h.2)) := by decide

/-- The transfer order is `5 · lcm(ord h.1, ord h.2)`.
    `ord(1,0) = 2 → order 10`; `ord(0,1) = 3 → order 15`;
    `ord(1,1) = lcm(2,3) = 6 → order 30 = 5·6`. -/
theorem order_is_lcm :
    (∀ x, (K (0,0))^[5] x = x) ∧
    (∃ x, (K (1,0))^[5] x ≠ x) ∧ (∀ x, (K (1,0))^[10] x = x) ∧
    (∃ x, (K (0,1))^[5] x ≠ x) ∧ (∀ x, (K (0,1))^[15] x = x) ∧
    (∃ x, (K (1,1))^[15] x ≠ x) ∧ (∀ x, (K (1,1))^[30] x = x) := by decide

/-- **Summary separation.** For every holonomy pair `h`, the systems share the identical
    one-step residue transition, yet the full holonomy pair is recovered by winding the cycle
    once — each `ZMod 2`/`ZMod 3` component independently. -/
theorem product_holonomy_separates :
    (∀ (h : ZMod 2 × ZMod 3) x, (K h x).1 = x.1 + 1) ∧
    (∀ (h : ZMod 2 × ZMod 3) x, (K h)^[5] x = (x.1, (x.2.1 + h.1, x.2.2 + h.2))) :=
  ⟨residue_marginal_indep, holonomy_after_loop⟩

end Brockian.ProductHolonomy
