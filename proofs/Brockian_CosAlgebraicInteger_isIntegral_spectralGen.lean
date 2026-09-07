/-
  Brockian/CosAlgebraicInteger.lean — algebraic-integer status of the cycle
  spectral generator `α_n = 2 cos(2π/n)`, with degree hooks into the Galois files.

  ## What is proved

    * `isIntegral_two_cos_two_pi_div` — for every `n ≠ 0`,
        `IsIntegral ℤ (2 cos(2π/n))`
      (Mathlib: `Real.isIntegral_two_mul_cos_rat_mul_pi` at rational angle `2/n`).
    * `isIntegral_spectralGen` — same for the Brockian spectral generator
        `α_p = 2 cos(2π/p)` (`GaloisWhyFive.spectralGen`), any prime `p`.
    * `isIntegral_spectralGen_ℚ` — integrality over `ℚ` (tower from `ℤ`).
    * Degree packaging (already proved in GaloisWhyFive / GaloisGeneralDegree):
        `degree_three / five / seven`, `real_subfield_degree`,
        `quadratic_iff_five_general` re-exported under this namespace as
        named hooks for the algebraic-integer reading path.
    * Concrete monic integer annihilators for the three small primes:
        `p = 3`: `X + 1`; `p = 5`: `X² + X − 1`; `p = 7`: `X³ + X² − 2X − 1`.

  ## What is NOT claimed

    * No numerology: "why five" is the degree statement
      `[ℚ(α_p):ℚ] = (p−1)/2` (quadratic iff `p = 5`), not a mystical selection.
    * Explicit general Chebyshev / real-cyclotomic minpoly family is out of scope
      here (Lane B sibling `GaloisMinPolyFamily` if present).
-/
import Mathlib
import Brockian.GaloisWhyFive
import Brockian.GaloisGeneralDegree

namespace Brockian.CosAlgebraicInteger

open Polynomial
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree

/-! ### Algebraic integer: `2 cos(2π/n)` -/

/-- Argument identity: `2π/n = (2/n) · π` as reals (for `n ≠ 0`). -/
theorem two_pi_div_eq_rat_mul_pi {n : ℕ} (hn : n ≠ 0) :
    (2 * Real.pi / (n : ℝ)) = ((2 / n : ℚ) : ℝ) * Real.pi := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcast : ((2 / n : ℚ) : ℝ) = (2 : ℝ) / (n : ℝ) := by
    simp [Rat.cast_div, Rat.cast_ofNat]
  rw [hcast]
  field_simp [hn0]

/-- **`2 cos(2π/n)` is an algebraic integer** for every positive `n`.
Mathlib's Niven-theory integrality of `2 cos(q π)` at rational `q = 2/n`. -/
theorem isIntegral_two_cos_two_pi_div {n : ℕ} (hn : n ≠ 0) :
    IsIntegral ℤ (2 * Real.cos (2 * Real.pi / n)) := by
  have harg := two_pi_div_eq_rat_mul_pi hn
  simpa [harg] using Real.isIntegral_two_mul_cos_rat_mul_pi (2 / n : ℚ)

/-- Specialization: the spectral generator `α_p = 2 cos(2π/p)` is an algebraic
integer for every prime `p` (including the degenerate `p = 2` boundary). -/
theorem isIntegral_spectralGen {p : ℕ} (hp : p.Prime) :
    IsIntegral ℤ (spectralGen p) := by
  unfold spectralGen
  exact isIntegral_two_cos_two_pi_div hp.ne_zero

/-- Integrality over `ℚ` follows by base change from `ℤ`. -/
theorem isIntegral_spectralGen_ℚ {p : ℕ} (hp : p.Prime) :
    IsIntegral ℚ (spectralGen p) :=
  (isIntegral_spectralGen hp).tower_top

/-- Same for general `n ≠ 0`, over `ℚ`. -/
theorem isIntegral_two_cos_two_pi_div_ℚ {n : ℕ} (hn : n ≠ 0) :
    IsIntegral ℚ (2 * Real.cos (2 * Real.pi / n)) :=
  (isIntegral_two_cos_two_pi_div hn).tower_top

/-! ### Concrete monic integer annihilators (p ∈ {3,5,7}) -/

/-- `α_3 = −1` is a root of the monic integer polynomial `X + 1`. -/
theorem aeval_spectralGen_three_X_add_one :
    (aeval (spectralGen 3)) (X + 1 : Polynomial ℤ) = 0 := by
  simp [spectralGen_three]

/-- `α_5 = φ − 1` is a root of the monic integer polynomial `X² + X − 1`. -/
theorem aeval_spectralGen_five_X_sq_add_X_sub_one :
    (aeval (spectralGen 5)) (X ^ 2 + X - 1 : Polynomial ℤ) = 0 := by
  rw [spectralGen_five]
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  simp only [map_sub, map_add, map_pow, aeval_X, map_one]
  linear_combination hsq

/-- `α_7` is a root of the monic integer cubic `X³ + X² − 2X − 1`
(`GaloisWhyFive.cubic7`). -/
theorem aeval_spectralGen_seven_cubic7 :
    (aeval (spectralGen 7)) cubic7 = 0 := by
  unfold cubic7
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one, map_ofNat]
  rw [spectralGen_seven]
  exact cubic_identity_seven

/-! ### Degree packaging (hooks into GaloisWhyFive / GaloisGeneralDegree) -/

/-- Degree of `α_3` over `ℚ` is `1`. -/
theorem degree_three_pack : (minpoly ℚ (spectralGen 3)).natDegree = 1 :=
  degree_three

/-- Degree of `α_5` over `ℚ` is `2` (golden quadratic). -/
theorem degree_five_pack : (minpoly ℚ (spectralGen 5)).natDegree = 2 :=
  degree_five

/-- Degree of `α_7` over `ℚ` is `3`. -/
theorem degree_seven_pack : (minpoly ℚ (spectralGen 7)).natDegree = 3 :=
  degree_seven

/-- **General degree package.** For every prime `p ≠ 2`,
`[ℚ(2 cos(2π/p)) : ℚ] = (p − 1)/2`. -/
theorem real_subfield_degree_pack {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (minpoly ℚ (spectralGen p)).natDegree = (p - 1) / 2 :=
  real_subfield_degree hp hp2

/-- **General "why five" package.** For every prime `p ≠ 2`, the spectral field is
quadratic iff `p = 5`. No numerology: this is the degree count `(p−1)/2 = 2`. -/
theorem quadratic_iff_five_pack {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (minpoly ℚ (spectralGen p)).natDegree = 2 ↔ p = 5 :=
  quadratic_iff_five_general hp hp2

/-- Combined arithmetic face: `α_p` is an algebraic integer of degree
`(p−1)/2` over `ℚ`, for every odd prime `p`. -/
theorem isIntegral_and_degree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIntegral ℤ (spectralGen p) ∧
      (minpoly ℚ (spectralGen p)).natDegree = (p - 1) / 2 :=
  ⟨isIntegral_spectralGen hp, real_subfield_degree_pack hp hp2⟩

end Brockian.CosAlgebraicInteger
