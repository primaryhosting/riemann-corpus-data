/-
  Brockian/MetallicFamily.lean

  A small, finite algebra foothold for the "metallic family" direction.

  The point of this file is deliberately modest: pin the metallic mean
  `M_a = (a + sqrt(a^2+4))/2`, prove its quadratic identities, and connect the
  two verified special cases already present in the project:

    * `a = 1`: the golden mean, feeding `golden_unique_to_five`;
    * `a = 2`: the silver mean `1+sqrt 2`, feeding the length-3 sieve block.

  It does not claim that the whole Brockian construction generalizes to every
  metallic mean.  It gives later agents named algebraic hooks for doing that
  carefully.
-/
import Mathlib
import Brockian.Spectral
import Brockian.Sieve

namespace Brockian.MetallicFamily

open Brockian.Spectral
open Brockian.Sieve

/-! ### Metallic means -/

/-- The positive metallic root `M_a = (a + sqrt(a^2+4))/2`. -/
noncomputable def metallicMean (a : ℝ) : ℝ :=
  (a + Real.sqrt (a ^ 2 + 4)) / 2

/-- The conjugate root `m_a = (a - sqrt(a^2+4))/2`. -/
noncomputable def metallicConj (a : ℝ) : ℝ :=
  (a - Real.sqrt (a ^ 2 + 4)) / 2

theorem metallic_radicand_nonneg (a : ℝ) :
    0 ≤ a ^ 2 + 4 := by
  nlinarith [sq_nonneg a]

/-- The two metallic roots have sum `a`. -/
theorem metallicMean_add_conj (a : ℝ) :
    metallicMean a + metallicConj a = a := by
  unfold metallicMean metallicConj
  ring

/-- The two metallic roots differ by the discriminant square root. -/
theorem metallicMean_sub_conj (a : ℝ) :
    metallicMean a - metallicConj a = Real.sqrt (a ^ 2 + 4) := by
  unfold metallicMean metallicConj
  ring

/-- The two metallic roots have product `-1`. -/
theorem metallicMean_mul_conj (a : ℝ) :
    metallicMean a * metallicConj a = -1 := by
  unfold metallicMean metallicConj
  have hs : Real.sqrt (a ^ 2 + 4) ^ 2 = a ^ 2 + 4 :=
    Real.sq_sqrt (metallic_radicand_nonneg a)
  nlinarith

/-- The positive metallic root satisfies `M_a^2 = a M_a + 1`. -/
theorem metallicMean_sq (a : ℝ) :
    metallicMean a ^ 2 = a * metallicMean a + 1 := by
  unfold metallicMean
  have hs : Real.sqrt (a ^ 2 + 4) ^ 2 = a ^ 2 + 4 :=
    Real.sq_sqrt (metallic_radicand_nonneg a)
  nlinarith [hs]

/-- The conjugate metallic root satisfies the same quadratic. -/
theorem metallicConj_sq (a : ℝ) :
    metallicConj a ^ 2 = a * metallicConj a + 1 := by
  unfold metallicConj
  have hs : Real.sqrt (a ^ 2 + 4) ^ 2 = a ^ 2 + 4 :=
    Real.sq_sqrt (metallic_radicand_nonneg a)
  nlinarith [hs]

/-- For nonnegative `a`, the positive metallic root is strictly positive. -/
theorem metallicMean_pos_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 < metallicMean a := by
  unfold metallicMean
  have hs : 0 < Real.sqrt (a ^ 2 + 4) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])
  positivity

/-- For nonnegative `a`, `1/M_a = M_a - a`. -/
theorem inv_metallicMean_eq_sub {a : ℝ} (ha : 0 ≤ a) :
    1 / metallicMean a = metallicMean a - a := by
  have hpos := metallicMean_pos_of_nonneg ha
  have hne : metallicMean a ≠ 0 := ne_of_gt hpos
  have hsq := metallicMean_sq a
  field_simp [hne]
  nlinarith

/-! ### Golden and silver specializations -/

/-- `M_1` is Mathlib's golden ratio. -/
theorem metallicMean_one :
    metallicMean 1 = Real.goldenRatio := by
  unfold metallicMean Real.goldenRatio
  norm_num

/-- `M_2` is the silver mean `1 + sqrt 2`. -/
theorem metallicMean_two :
    metallicMean 2 = 1 + Real.sqrt 2 := by
  unfold metallicMean
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs8 : Real.sqrt ((2 : ℝ) ^ 2 + 4) = 2 * Real.sqrt 2 := by
    rw [show ((2 : ℝ) ^ 2 + 4) = 4 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
  rw [hs8]; ring

/-- The `a=1` metallic specialization is exactly the existing C5 rigidity theorem. -/
theorem metallic_one_unique_to_five {p : ℕ} (hp : p.Prime) :
    (metallicMean 1 - 1) ∈ cycleSpectrum p ↔ p = 5 := by
  simpa [metallicMean_one] using golden_unique_to_five hp

/-- The silver sieve gap is `3 - M_2`. -/
theorem silverGap_eq_three_sub_metallicMean_two :
    silverGap = 3 - metallicMean 2 := by
  rw [metallicMean_two]
  unfold silverGap
  ring

/-- The verified `H3` ground mode can be written in metallic-family coordinates. -/
theorem H3_ground_metallic :
    H3.mulVec ![1, metallicMean 2 - 1, 1] =
      (3 - metallicMean 2) • ![1, metallicMean 2 - 1, 1] := by
  have hv : metallicMean 2 - 1 = Real.sqrt 2 := by rw [metallicMean_two]; ring
  have he : 3 - metallicMean 2 = silverGap := by
    rw [metallicMean_two]; unfold silverGap; ring
  rw [hv, he]; exact H3_ground

end Brockian.MetallicFamily
