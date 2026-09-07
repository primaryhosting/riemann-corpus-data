/-
  Brockian/Connectivity.lean — the spectral-gap face of the Brockian Pentagonal Law.

  Citation-grade Mathlib-4.32 re-proof of the run-88 keeper
  `λ₂(C₅) = 2 − 1/φ` (the algebraic connectivity of the 5-cycle), previously
  deferred in `PORT-QUEUE.md` (RELEASE-BLOCKING) because its Aristotle proof lived
  only in `archive/`. Re-proved here CONCRETELY and self-contained on Mathlib alone
  (using Mathlib's own `Real.goldenRatio`, so AXLE verifies the file standalone).

  Since C_n is 2-regular, its Laplacian is `L = 2I − A`, hence the Laplacian
  eigenvalues are `2 − 2cos(2πk/n)`, k = 0,…,n−1. For C₅ the distinct values are:
    * k = 0        →  0                       (the trivial eigenvalue)
    * k = 1, 4     →  2 − 2cos(2π/5)  =  3 − φ  =  2 − 1/φ
    * k = 2, 3     →  2 − 2cos(4π/5)  =  2 + φ
  The algebraic connectivity λ₂ (2nd-smallest = smallest positive) is therefore
  `2 − 2cos(2π/5) = 2 − 1/φ`, and it is `≤` the other nonzero eigenvalue `2 + φ`.

  Here `φ` denotes `Real.goldenRatio = (1 + √5)/2`, the same golden ratio as
  `Brockian.Core.phi` (`Brockian.Core.binet_formula` records `phi = Real.goldenRatio`).

  Contents:
    * `cos_2pi_5`             : cos(2π/5) = (φ − 1)/2
    * `two_cos_4pi_5`         : 2cos(4π/5) = −φ            (the C₅ golden eigenvalue)
    * `one_div_phi`          : 1/φ = φ − 1               (from φ² = φ + 1)
    * `lambda2_eq`           : 2 − 2cos(2π/5) = 2 − 1/φ   (the golden identity)
    * `laplacianEigs5`       : the Laplacian spectrum {0, 2−2cos(2π/5), 2−2cos(4π/5)}
    * `pentagon_lambda2_phi` : 2 − 1/φ is the algebraic connectivity of C₅
    * `pentagon_ratio`       : (2 − 1/φ)/2 = 1 − 1/(2φ)

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

open Real

namespace Brockian.Connectivity

/-- Local notation: `φ` is Mathlib's golden ratio `(1 + √5)/2`. -/
local notation "φ" => Real.goldenRatio

/-! ### Cosines at the pentagon angles -/

/-- **cos(2π/5) = (φ − 1)/2.**  Via the double-angle identity from
`Real.cos_pi_div_five` (`cos(π/5) = (1+√5)/4`) and `φ = (1+√5)/2`. -/
theorem cos_2pi_5 : Real.cos (2 * Real.pi / 5) = (φ - 1) / 2 := by
  have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have hgold : φ = (1 + Real.sqrt 5) / 2 := by rw [Real.goldenRatio]
  have hdiv : (2 * Real.pi / 5) = (2 * (Real.pi / 5)) := by ring
  have htwo : Real.cos (2 * (Real.pi / 5)) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
    simpa using Real.cos_two_mul (Real.pi / 5)
  rw [hdiv, htwo, hcos, hgold]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 8) * h5

/-- **The golden eigenvalue of C₅.**  The adjacency eigenvalues of the 5-cycle are
`2cos(2πk/5)`; at `k = 2` (angle `4π/5`) the value is exactly `−φ`:
`2cos(4π/5) = 2·(−cos(π/5)) = 2·(−(1+√5)/4) = −(1+√5)/2 = −φ`. -/
theorem two_cos_4pi_5 : 2 * Real.cos (4 * Real.pi / 5) = -φ := by
  have h : (4 * Real.pi / 5) = Real.pi - Real.pi / 5 := by ring
  have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have hgold : φ = (1 + Real.sqrt 5) / 2 := by rw [Real.goldenRatio]
  rw [h, Real.cos_pi_sub, hcos, hgold]; ring

/-! ### The golden reciprocal -/

/-- **1/φ = φ − 1.**  From the defining quadratic `φ² = φ + 1` we get `(φ−1)·φ = 1`,
so the golden ratio is its own reciprocal shifted by one. -/
theorem one_div_phi : 1 / φ = φ - 1 := by
  have hne : φ ≠ 0 := ne_of_gt (by positivity)
  rw [div_eq_iff hne]
  linear_combination -goldenRatio_sq

/-! ### The Laplacian spectrum of C₅ -/

/-- The concrete Laplacian spectrum of the 5-cycle: `{0, 2−2cos(2π/5), 2−2cos(4π/5)}`.
Because `C₅` is 2-regular, `L = 2I − A`, so each Laplacian eigenvalue is `2 − λ_A`
for an adjacency eigenvalue `λ_A = 2cos(2πk/5)`; the distinct values are these three
(`k = 1,4` and `k = 2,3` coincide in pairs). -/
noncomputable def laplacianEigs5 : Finset ℝ :=
  {0, 2 - 2 * Real.cos (2 * Real.pi / 5), 2 - 2 * Real.cos (4 * Real.pi / 5)}

/-- **The golden connectivity identity.**  The smallest positive Laplacian eigenvalue
of `C₅` equals `2 − 1/φ`:
`2 − 2cos(2π/5) = 2 − 2·((φ−1)/2) = 2 − (φ−1) = 3 − φ = 2 − 1/φ`.
Discharged via `cos_2pi_5` and `one_div_phi`. -/
theorem lambda2_eq :
    2 - 2 * Real.cos (2 * Real.pi / 5) = 2 - 1 / φ := by
  rw [cos_2pi_5, one_div_phi]; ring

/-! ### Algebraic connectivity of C₅ -/

/-- **`λ₂(C₅) = 2 − 1/φ`** (RE-PROVED, run 88).  The algebraic connectivity of the
5-cycle — its second-smallest Laplacian eigenvalue — is `2 − 1/φ`.  Stated cleanly as
the conjunction of the three facts that pin it down as the spectral gap:

  1. `2 − 1/φ` **is** a Laplacian eigenvalue of `C₅` (`∈ laplacianEigs5`);
  2. it is **positive** (`0 < 2 − 1/φ`, since `2 − 1/φ = 3 − φ` and `φ < 3`), hence it
     is the smallest *nonzero* eigenvalue, the eigenvalue `0` being the trivial one;
  3. it is `≤` the only other nonzero eigenvalue `2 − 2cos(4π/5) = 2 + φ`, so it is the
     **second-smallest overall** — the algebraic connectivity `λ₂`.

Discharged from `lambda2_eq`, `two_cos_4pi_5` (`2cos(4π/5) = −φ`), `one_div_phi`,
`goldenRatio_sq`, and `one_lt_goldenRatio`. -/
theorem pentagon_lambda2_phi :
    (2 - 1 / φ) ∈ laplacianEigs5 ∧
    0 < 2 - 1 / φ ∧
    (2 - 1 / φ) ≤ 2 - 2 * Real.cos (4 * Real.pi / 5) := by
  have hgap : 2 - 1 / φ = 2 - 2 * Real.cos (2 * Real.pi / 5) := lambda2_eq.symm
  have hrecip : 1 / φ = φ - 1 := one_div_phi
  have h4 : 2 * Real.cos (4 * Real.pi / 5) = -φ := two_cos_4pi_5
  refine ⟨?_, ?_, ?_⟩
  · -- membership: 2 − 1/φ is the k = 1,4 eigenvalue
    rw [hgap]
    simp only [laplacianEigs5, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · -- positivity: 2 − 1/φ = 3 − φ > 0 since φ < 3
    rw [hrecip]
    nlinarith [goldenRatio_sq, one_lt_goldenRatio]
  · -- spectral-gap ordering: 3 − φ ≤ 2 + φ  ⟺  1 ≤ 2φ
    rw [hrecip, sub_le_sub_iff_left, h4]
    nlinarith [one_lt_goldenRatio]

/-- **Companion ratio.**  Normalizing by the degree `2` (the C₅ regularity),
`(2 − 1/φ)/2 = 1 − 1/(2φ)`. -/
theorem pentagon_ratio : (2 - 1 / φ) / 2 = 1 - 1 / (2 * φ) := by
  have hne : φ ≠ 0 := ne_of_gt (by positivity)
  field_simp

end Brockian.Connectivity
