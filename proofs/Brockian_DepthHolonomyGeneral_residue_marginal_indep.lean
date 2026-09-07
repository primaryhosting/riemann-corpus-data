import Mathlib

/-! # General depth-holonomy: the residue-Fourier-invisible invariant is the full holonomy. -/

namespace Brockian.DepthHolonomyGeneral

/-- Depth in `ZMod 6` over the residue cycle `ZMod 5`. `K h` advances the residue and, at
    the seam `j = 4 → 0`, increments the depth by the holonomy `h ∈ ZMod 6`. -/
def K (h : ZMod 6) (x : ZMod 5 × ZMod 6) : ZMod 5 × ZMod 6 :=
  (x.1 + 1, x.2 + (if x.1 = 4 then h else 0))

/-- The one-step residue transition is `j ↦ j + 1` for EVERY holonomy `h`: residue-class
    (mod-5) Fourier analysis is blind to the depth holonomy. -/
theorem residue_marginal_indep (h : ZMod 6) (x : ZMod 5 × ZMod 6) : (K h x).1 = x.1 + 1 :=
  rfl

/-- **The holonomy IS recovered.** Winding the residue cycle once translates the depth by
    exactly `h`: the depth-holonomy around the cycle is the full `ZMod 6` element `h`. This
    is a complete `ZMod 6`-valued invariant that the residue marginal (identical for all `h`)
    cannot see. -/
theorem holonomy_after_loop : ∀ (h : ZMod 6) (x : ZMod 5 × ZMod 6),
    (K h)^[5] x = (x.1, x.2 + h) := by decide

/-- The orbit structure (hence `det(I − zK_h)`) is governed by the order of `h`: distinct
    holonomy classes are distinguished. `K 0` closes after one loop; `K 2` and `K 3` do not
    (orders `5·3` and `5·2`), and `K 1` needs the full `5·6` steps. Three residue-Fourier-
    identical systems, three different determinants. -/
theorem order_separates :
    (∀ x, (K 0)^[5] x = x) ∧
    (∃ x, (K 2)^[5] x ≠ x) ∧ (∀ x, (K 2)^[15] x = x) ∧
    (∃ x, (K 3)^[5] x ≠ x) ∧ (∀ x, (K 3)^[10] x = x) ∧
    (∃ x, (K 1)^[15] x ≠ x) ∧ (∀ x, (K 1)^[30] x = x) := by decide

/-- **The invariant is the cyclic subgroup ⟨h⟩, not `h` itself.** `h = 1` and `h = 5`
    generate the same subgroup `⟨1⟩ = ⟨5⟩ = ZMod 6`, so their systems have identical orbit
    structure (both order `30`) — a determinant collision. Likewise `h = 2` and `h = 4`
    (`⟨2⟩ = ⟨4⟩`, order `15`). So the det-visible content is exactly `⟨h⟩`. -/
theorem gcd_collision :
    (∀ x, (K 1)^[30] x = (K 5)^[30] x) ∧
    (∀ x, (K 2)^[15] x = x) ∧ (∀ x, (K 4)^[15] x = x) ∧
    (∃ x, (K 1)^[15] x ≠ x) ∧ (∃ x, (K 5)^[15] x ≠ x) := by decide

/-- **Summary separation.** For every holonomy `h`, the systems share the identical
    one-step residue transition, yet the depth-holonomy `h` is fully recovered by winding
    the cycle once. The depth-holonomy is a complete `ZMod 6`-valued invariant invisible to
    residue-Fourier analysis. -/
theorem general_depth_holonomy_separates :
    (∀ (h : ZMod 6) x, (K h x).1 = x.1 + 1) ∧
    (∀ (h : ZMod 6) x, (K h)^[5] x = (x.1, x.2 + h)) :=
  ⟨residue_marginal_indep, holonomy_after_loop⟩

end Brockian.DepthHolonomyGeneral
