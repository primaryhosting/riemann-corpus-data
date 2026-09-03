import Mathlib

/-!
# The Fermi–Dirac moment integral

This file proves the classical evaluation

  `∫_0^∞ x / (1 + eˣ) dx = π² / 12`,

which is the analytic input for the base case of Mirzakhani's recursion.
-/

open MeasureTheory Set Real Filter Asymptotics

namespace Frontier

/-- `t ↦ t e^{-rt}` is integrable on any right half-line, for `r > 0`. -/
theorem integrableOn_id_mul_exp_neg {r : ℝ} (hr : 0 < r) (c : ℝ) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(r * t))) (Ioi c) := by
  apply integrable_of_isBigO_exp_neg (b := r / 2) (by positivity)
  · exact (continuous_id.mul (Real.continuous_exp.comp (by fun_prop))).continuousOn
  · apply Asymptotics.IsBigO.of_bound (2 / r)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h1 : r * t / 2 + 1 ≤ Real.exp (r * t / 2) := Real.add_one_le_exp _
    have h2 : t ≤ 2 / r * Real.exp (r * t / 2) := by
      rw [show (2 : ℝ) / r * Real.exp (r * t / 2) = 2 * Real.exp (r * t / 2) / r by ring,
        le_div_iff₀ hr]
      nlinarith
    have e1 : Real.exp (-(r * t)) = Real.exp (-(r * t / 2)) * Real.exp (-(r * t / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have hpos : 0 < Real.exp (-(r * t / 2)) := Real.exp_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.exp_pos _).le, e1]
    have hb : t * Real.exp (-(r * t / 2)) ≤ 2 / r := by
      have := mul_le_mul_of_nonneg_right h2 hpos.le
      rw [mul_assoc, ← Real.exp_add] at this
      simpa using this
    have e2 : Real.exp (-(r / 2) * t) = Real.exp (-(r * t / 2)) := by ring_nf
    rw [e2]
    calc t * (Real.exp (-(r * t / 2)) * Real.exp (-(r * t / 2)))
        = t * Real.exp (-(r * t / 2)) * Real.exp (-(r * t / 2)) := by ring
      _ ≤ 2 / r * Real.exp (-(r * t / 2)) := mul_le_mul_of_nonneg_right hb hpos.le

/-- `∫_0^∞ t e^{-rt} dt = 1/r²` for `r > 0`. -/
theorem integral_id_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(r * t)) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) two_pos hr
  simp only [show ((2 : ℝ) - 1) = 1 by norm_num, Real.Gamma_two, mul_one, div_pow,
    one_pow] at h
  rw [← h]
  exact (setIntegral_congr_fun measurableSet_Ioi fun x _ => by rw [Real.rpow_one])

/-- Geometric expansion of the Fermi–Dirac weight. -/
theorem hasSum_fermi_expansion (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (x * Real.exp (-(((n : ℝ) + 1) * x))))
      (x / (1 + Real.exp x)) := by
  have hlt : ‖(-Real.exp (-x))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_norm_lt_one hlt).mul_left (x * Real.exp (-x))
  have hterm : ∀ n : ℕ, x * Real.exp (-x) * (-Real.exp (-x)) ^ n
      = (-1 : ℝ) ^ n * (x * Real.exp (-(((n : ℝ) + 1) * x))) := by
    intro n
    rw [show (-Real.exp (-x)) ^ n = (-1 : ℝ) ^ n * Real.exp (-x) ^ n by
        rw [← neg_one_mul, mul_pow], ← Real.exp_nat_mul,
      show x * Real.exp (-x) * ((-1 : ℝ) ^ n * Real.exp ((n : ℝ) * -x))
        = (-1) ^ n * (x * (Real.exp (-x) * Real.exp ((n : ℝ) * -x))) by ring, ← Real.exp_add]
    ring_nf
  have hval : x * Real.exp (-x) * (1 - -Real.exp (-x))⁻¹ = x / (1 + Real.exp x) := by
    have h : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have h2 : (1 : ℝ) + Real.exp x ≠ 0 := by positivity
    rw [sub_neg_eq_add, Real.exp_neg,
      show (1 : ℝ) + (Real.exp x)⁻¹ = (1 + Real.exp x) * (Real.exp x)⁻¹ by field_simp; ring]
    field_simp
  rw [← hval]
  exact hg.congr_fun hterm

/-- Basel's sum, shifted so that the index starts at `1`. -/
theorem hasSum_inv_sq_shift : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  refine (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr ?_
  simpa using hasSum_zeta_two

/-- The alternating Basel sum `∑ (-1)ⁿ/(n+1)² = π²/12`. -/
theorem hasSum_alternating_inv_sq :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  have hz := hasSum_inv_sq_shift
  -- the odd-index part
  have hodd : HasSum (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) (π ^ 2 / 24) := by
    have h := hz.mul_left (1 / 4)
    have : ∀ k : ℕ, (1 : ℝ) / 4 * (1 / ((k : ℝ) + 1) ^ 2)
        = 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      intro k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    have h2 := h.congr_fun this
    simpa using h2
  -- the even-index part, obtained by subtraction
  have hsummable : Summable fun k : ℕ => 1 / ((((2 * k : ℕ)) : ℝ) + 1) ^ 2 := by
    have : Function.Injective fun k : ℕ => 2 * k := fun a b hab => by omega
    exact (hz.summable.comp_injective this)
  set E := ∑' k : ℕ, 1 / ((((2 * k : ℕ)) : ℝ) + 1) ^ 2 with hE
  have heven : HasSum (fun k : ℕ => 1 / ((((2 * k : ℕ)) : ℝ) + 1) ^ 2) E := hsummable.hasSum
  have hsum := heven.even_add_odd hodd
  have hEval : E = π ^ 2 / 8 := by
    have := hsum.unique hz
    linarith
  -- now assemble the alternating series
  have heven' : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k) / (((2 * k : ℕ) : ℝ) + 1) ^ 2)
      (π ^ 2 / 8) := by
    rw [← hEval]
    refine heven.congr_fun fun k => ?_
    rw [pow_mul]
    norm_num
  have hodd' : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2)
      (-(π ^ 2 / 24)) := by
    refine hodd.neg.congr_fun fun k => ?_
    rw [pow_succ, pow_mul]
    norm_num
  have := heven'.even_add_odd hodd'
  have hfin : π ^ 2 / 8 + -(π ^ 2 / 24) = π ^ 2 / 12 := by ring
  rwa [hfin] at this

/-- **The Fermi–Dirac moment integral**: `∫_0^∞ x/(1 + eˣ) dx = π²/12`. -/
theorem integral_id_div_one_add_exp :
    ∫ x in Ioi (0 : ℝ), x / (1 + Real.exp x) = π ^ 2 / 12 := by
  set F : ℕ → ℝ → ℝ := fun n x => (-1 : ℝ) ^ n * (x * Real.exp (-(((n : ℝ) + 1) * x))) with hF
  have hint : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := by
    intro n
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact (integrableOn_id_mul_exp_neg hr 0).const_mul _
  have hnorm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖F n x‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show (∫ x in Ioi (0 : ℝ), ‖F n x‖)
        = ∫ x in Ioi (0 : ℝ), x * Real.exp (-(((n : ℝ) + 1) * x)) from
      setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
    · exact integral_id_mul_exp_neg_mul_Ioi hr
    · have hx0 : (0 : ℝ) < x := hx
      rw [hF]
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
  have hsummable : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    refine (hasSum_inv_sq_shift.summable).congr fun n => (hnorm n).symm
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (F := F) (μ := volume.restrict (Ioi (0 : ℝ))) hint hsummable
  have hpt : ∫ x in Ioi (0 : ℝ), ∑' n : ℕ, F n x = ∫ x in Ioi (0 : ℝ), x / (1 + Real.exp x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    exact (hasSum_fermi_expansion x hx).tsum_eq
  rw [hpt] at hHS
  have hvals : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), F n x) = (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hF]
    simp only
    rw [integral_const_mul, integral_id_mul_exp_neg_mul_Ioi hr]
    ring
  exact (hHS.congr_fun hvals).unique hasSum_alternating_inv_sq |>.symm

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

