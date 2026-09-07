import Mathlib

/-! # Depth-holonomy separation over `ZMod 4` (residue cycle `ZMod 5`). -/

namespace Brockian.DepthHolonomyZMod4

/-- Depth in `ZMod 4` over the residue cycle `ZMod 5`. `K h` advances the residue and, at
    the seam `j = 4 → 0`, increments the depth by the holonomy `h ∈ ZMod 4`. -/
def K (h : ZMod 4) (x : ZMod 5 × ZMod 4) : ZMod 5 × ZMod 4 :=
  (x.1 + 1, x.2 + (if x.1 = 4 then h else 0))

/-- The one-step residue transition is `j ↦ j + 1` for EVERY holonomy `h`: residue-class
    (mod-5) Fourier analysis is blind to the depth holonomy. -/
theorem residue_marginal_indep (h : ZMod 4) (x : ZMod 5 × ZMod 4) : (K h x).1 = x.1 + 1 :=
  rfl

/-- **The holonomy IS recovered.** Winding the residue cycle once translates the depth by
    exactly `h`: the depth-holonomy around the cycle is the full `ZMod 4` element `h`. -/
theorem holonomy_after_loop : ∀ (h : ZMod 4) (x : ZMod 5 × ZMod 4),
    (K h)^[5] x = (x.1, x.2 + h) := by decide

/-- The orbit structure is governed by the order of `h`: distinct holonomy classes are
    distinguished. `K 0` closes after one loop (order `5·1`); `K 2` needs two loops (order
    `5·2`); `K 1` needs the full four loops (order `5·4`). -/
theorem order_separates :
    (∀ x, (K 0)^[5] x = x) ∧
    (∃ x, (K 2)^[5] x ≠ x) ∧ (∀ x, (K 2)^[10] x = x) ∧
    (∃ x, (K 1)^[10] x ≠ x) ∧ (∀ x, (K 1)^[20] x = x) := by decide

/-- **The invariant is the cyclic subgroup ⟨h⟩, not `h` itself.** `h = 1` and `h = 3`
    generate the same subgroup `⟨1⟩ = ⟨3⟩ = ZMod 4`, so their systems have identical orbit
    structure (both order `20`) — a determinant collision. -/
theorem gcd_collision :
    (∀ x, (K 1)^[20] x = (K 3)^[20] x) ∧
    (∃ x, (K 1)^[10] x ≠ x) ∧ (∃ x, (K 3)^[10] x ≠ x) := by decide

/-- **Summary separation.** For every holonomy `h`, the systems share the identical
    one-step residue transition, yet the depth-holonomy `h` is fully recovered by winding
    the cycle once. The depth-holonomy is a complete `ZMod 4`-valued invariant invisible to
    residue-Fourier analysis. -/
theorem general_depth_holonomy_separates :
    (∀ (h : ZMod 4) x, (K h x).1 = x.1 + 1) ∧
    (∀ (h : ZMod 4) x, (K h)^[5] x = (x.1, x.2 + h)) :=
  ⟨residue_marginal_indep, holonomy_after_loop⟩

end Brockian.DepthHolonomyZMod4
