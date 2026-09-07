import Mathlib

/-! # Nonabelian depth-holonomy separation.

The depth fiber is the dihedral group `DihedralGroup 3` (order 6, nonabelian). The transfer
operator `K` advances the residue in `ZMod 5` and LEFT-MULTIPLIES the fiber by a fixed group
element `σ` at the seam `j = 4`. Winding the residue cycle once therefore conjugates the fiber
by the holonomy `σ`; its ORDER (hence the order of the transfer operator / its determinant) is
conjugacy-class data — a rotation and a reflection give residue-Fourier-identical systems with
different orders, invisible to residue (mod-5) Fourier analysis. -/

namespace Brockian.NonabelianHolonomy

/-- Transfer operator: advance the residue, and at the seam `j = 4` left-multiply the
    nonabelian depth fiber by `σ`. -/
def K (σ : DihedralGroup 3) (x : ZMod 5 × DihedralGroup 3) : ZMod 5 × DihedralGroup 3 :=
  (x.1 + 1, (if x.1 = 4 then σ else 1) * x.2)

/-- The one-step residue transition is `j ↦ j + 1` for EVERY holonomy `σ`: residue-class
    (mod-5) Fourier analysis is blind to the depth holonomy. -/
theorem residue_marginal_indep (σ : DihedralGroup 3) (x : ZMod 5 × DihedralGroup 3) :
    (K σ x).1 = x.1 + 1 := rfl

/-- **The holonomy IS the group element `σ`.** Winding the residue cycle once left-multiplies
    the depth fiber by exactly `σ`. -/
theorem holonomy_after_loop :
    ∀ (σ : DihedralGroup 3) (x : ZMod 5 × DihedralGroup 3), (K σ)^[5] x = (x.1, σ * x.2) := by
  decide

/-- The order of the transfer operator is governed by the conjugacy class of `σ`. The
    rotation `r 1` has order 3, so `K (r 1)` has order `5·3 = 15`; the reflection `sr 0` has
    order 2, so `K (sr 0)` has order `5·2 = 10`. Both are residue-Fourier-identical, yet have
    different determinants — this is conjugacy-class data invisible to residue analysis. -/
theorem order_by_conjugacy :
    (∃ x, (K (DihedralGroup.r 1))^[5] x ≠ x) ∧
    (∀ x, (K (DihedralGroup.r 1))^[15] x = x) ∧
    (∃ x, (K (DihedralGroup.sr 0))^[5] x ≠ x) ∧
    (∀ x, (K (DihedralGroup.sr 0))^[10] x = x) := by
  decide

/-- **Summary separation.** Every holonomy `σ` yields the identical one-step residue
    transition, yet winding the cycle once recovers the full nonabelian group element `σ`. -/
theorem nonabelian_holonomy_separates :
    (∀ (σ : DihedralGroup 3) x, (K σ x).1 = x.1 + 1) ∧
    (∀ (σ : DihedralGroup 3) x, (K σ)^[5] x = (x.1, σ * x.2)) :=
  ⟨residue_marginal_indep, holonomy_after_loop⟩

end Brockian.NonabelianHolonomy
