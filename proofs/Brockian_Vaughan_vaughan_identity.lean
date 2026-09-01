/-
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Vaughan

open ArithmeticFunction

/-- Truncation of an arithmetic function to arguments `≤ U`. -/
def truncLE (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- Truncation of an arithmetic function to arguments `> U`. -/
def truncGT (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma truncLE_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncLE U f n = if n ≤ U then f n else 0 := rfl

@[simp] lemma truncGT_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncGT U f n = if U < n then f n else 0 := rfl

/-- Splitting an arithmetic function into its `≤ U` and `> U` parts. -/
lemma truncLE_add_truncGT (U : ℕ) (f : ArithmeticFunction ℝ) :
    truncLE U f + truncGT U f = f := by
  ext n
  by_cases h : n ≤ U <;> simp [h, Nat.not_lt.mpr, Nat.lt_of_not_le]

/-- **Vaughan's identity**, as an identity of arithmetic functions under Dirichlet
convolution. -/
theorem vaughan_identity (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) =
      truncLE V vonMangoldt
        + truncLE U (moebius : ArithmeticFunction ℝ) * log
        - truncLE U (moebius : ArithmeticFunction ℝ) * truncLE V vonMangoldt
            * (zeta : ArithmeticFunction ℝ)
        + truncGT U (moebius : ArithmeticFunction ℝ) * truncGT V vonMangoldt
            * (zeta : ArithmeticFunction ℝ) := by
  set A := truncLE U (moebius : ArithmeticFunction ℝ) with hA
  set B := truncGT U (moebius : ArithmeticFunction ℝ) with hB
  set C := truncLE V (vonMangoldt : ArithmeticFunction ℝ) with hC
  set D := truncGT V (vonMangoldt : ArithmeticFunction ℝ) with hD
  have h1 : A + B = (moebius : ArithmeticFunction ℝ) := truncLE_add_truncGT U _
  have h2 : C + D = (vonMangoldt : ArithmeticFunction ℝ) := truncLE_add_truncGT V _
  have h3 : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
    coe_moebius_mul_coe_zeta
  have h4 : (vonMangoldt : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = log :=
    vonMangoldt_mul_zeta
  have h5 : (moebius : ArithmeticFunction ℝ) * log = vonMangoldt :=
    moebius_mul_log_eq_vonMangoldt
  linear_combination (norm := ring_nf)
    (-1 : ArithmeticFunction ℝ) * h5 + (-log + C * (zeta : ArithmeticFunction ℝ)) * h1
      + (-B) * h4 + (-(B * (zeta : ArithmeticFunction ℝ))) * h2 + C * h3

end Brockian.Vaughan

