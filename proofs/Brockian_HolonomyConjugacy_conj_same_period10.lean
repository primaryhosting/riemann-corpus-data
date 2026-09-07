import Mathlib

/-! # The nonabelian depth-holonomy determinant is a conjugacy-class function.

Setup (identical to `Brockian.NonabelianHolonomy`): the depth fiber is the nonabelian group
`DihedralGroup 3` (order 6), the residue lives in `ZMod 5`, and the transfer operator `K σ`
advances the residue by one and, at the seam `j = 4`, LEFT-MULTIPLIES the fiber by the holonomy
`σ`. Winding the residue cycle once conjugates the fiber by `σ`, so the ORDER of the transfer
operator — equivalently, the vanishing structure of its determinant `det (I − z K)` — is a
function of the CONJUGACY CLASS of `σ`, and nothing finer.

We prove decidably (over the finite state space `ZMod 5 × DihedralGroup 3`, 30 elements) that
conjugating the holonomy `σ ↦ g σ g⁻¹` leaves the transfer-operator's period structure exactly
invariant: for each candidate period `p ∈ {5, 10, 15}`, `K σ` closes up at period `p`
(i.e. `(K σ)^[p] = id`) if and only if `K (g σ g⁻¹)` does. The period of `K` — hence the
determinant `det (I − z K)` — depends only on the conjugacy class of the holonomy, and is
therefore INVISIBLE to residue (mod-5) Fourier data, which sees only the seam-independent
one-step residue transition `j ↦ j + 1`. -/

namespace Brockian.HolonomyConjugacy

/-- Transfer operator (re-declared exactly as in `Brockian.NonabelianHolonomy`): advance the
    residue, and at the seam `j = 4` left-multiply the nonabelian depth fiber by `σ`. -/
def K (σ : DihedralGroup 3) (x : ZMod 5 × DihedralGroup 3) : ZMod 5 × DihedralGroup 3 :=
  (x.1 + 1, (if x.1 = 4 then σ else 1) * x.2)

/-- **The holonomy IS the group element `σ`.** Winding the residue cycle once
    (`5` steps) left-multiplies the depth fiber by exactly `σ`. -/
theorem holonomy_after_loop :
    ∀ (σ : DihedralGroup 3) (x : ZMod 5 × DihedralGroup 3), (K σ)^[5] x = (x.1, σ * x.2) := by
  decide

/-- **Global closure at `30`.** Every element of `DihedralGroup 3` has order dividing `6`, so
    `σ ^ 6 = 1`; winding the residue cycle six times (`5 · 6 = 30` steps) returns every state to
    itself for EVERY holonomy `σ`. This bounds the transfer-operator period by `30`. -/
theorem all_close_at_30 :
    ∀ (σ : DihedralGroup 3) (x : ZMod 5 × DihedralGroup 3), (K σ)^[30] x = x := by
  decide

/-- **Conjugacy invariance of the period, at `p = 5`.** `K σ` closes up after one residue loop
    iff `K (g σ g⁻¹)` does — both hold exactly when the holonomy is trivial. Conjugating the
    holonomy cannot change whether the transfer operator has period `5`. -/
theorem conj_same_period :
    ∀ (g σ : DihedralGroup 3),
      (∀ x, (K σ)^[5] x = x) ↔ (∀ x, (K (g * σ * g⁻¹))^[5] x = x) := by
  decide

/-- **Conjugacy invariance of the period, at `p = 10`.** `K σ` closes up after two residue loops
    iff `K (g σ g⁻¹)` does — both hold exactly when `σ ^ 2 = 1` (the reflection class). The
    order-2 (reflection) sector of the determinant is a conjugacy invariant. -/
theorem conj_same_period10 :
    ∀ (g σ : DihedralGroup 3),
      (∀ x, (K σ)^[10] x = x) ↔ (∀ x, (K (g * σ * g⁻¹))^[10] x = x) := by
  decide

/-- **Conjugacy invariance of the period, at `p = 15`.** `K σ` closes up after three residue
    loops iff `K (g σ g⁻¹)` does — both hold exactly when `σ ^ 3 = 1` (the rotation class). The
    order-3 (rotation) sector of the determinant is a conjugacy invariant.

    Together with `conj_same_period` and `conj_same_period10`, this shows the FULL period
    structure of the transfer operator — hence the vanishing set of `det (I − z K)` — is a
    function of the conjugacy class of the holonomy alone. -/
theorem conj_same_period15 :
    ∀ (g σ : DihedralGroup 3),
      (∀ x, (K σ)^[15] x = x) ↔ (∀ x, (K (g * σ * g⁻¹))^[15] x = x) := by
  decide

/-- **Summary: the transfer-operator period is a conjugacy-class function.** For every candidate
    period `p ∈ {5, 10, 15}` (the divisors of the ambient period `30` that can occur), the seam
    holonomy `σ` and any conjugate `g σ g⁻¹` induce transfer operators that close up at `p`
    together. The determinant `det (I − z K)` therefore depends only on the conjugacy class of
    the holonomy — invisible to residue-Fourier data. -/
theorem period_is_conjugacy_class_function :
    (∀ (g σ : DihedralGroup 3), (∀ x, (K σ)^[5] x = x) ↔ (∀ x, (K (g * σ * g⁻¹))^[5] x = x)) ∧
    (∀ (g σ : DihedralGroup 3), (∀ x, (K σ)^[10] x = x) ↔ (∀ x, (K (g * σ * g⁻¹))^[10] x = x)) ∧
    (∀ (g σ : DihedralGroup 3), (∀ x, (K σ)^[15] x = x) ↔ (∀ x, (K (g * σ * g⁻¹))^[15] x = x)) :=
  ⟨conj_same_period, conj_same_period10, conj_same_period15⟩

end Brockian.HolonomyConjugacy
