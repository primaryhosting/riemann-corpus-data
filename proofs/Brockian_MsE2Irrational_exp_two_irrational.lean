import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/
private lemma fact_div_cast (n k : ℕ) (h : k ≤ n) :
    ((n ! / k ! : ℕ) : ℝ) = (n ! : ℝ) / (k ! : ℝ) := by
  have hdvd : k ! ∣ n ! := Nat.factorial_dvd_factorial h
  have heq : k ! * (n ! / k !) = n ! := Nat.mul_div_cancel' hdvd
  field_simp
  exact mod_cast (mul_comm (k ! : ℕ) (n ! / k !) ▸ heq)

/-- Any integer combination of the numbers `n !/k !`, `k ≤ n`, is an integer. -/
private lemma exists_int_sum (n : ℕ) (c : ℕ → ℤ) :
    ∃ A : ℤ, (A : ℝ) = ∑ k ∈ range (n + 1), (c k : ℝ) * ((n ! : ℝ) / (k ! : ℝ)) := by
  use ∑ k ∈ range (n + 1), c k * (n ! / k !)
  simp only [Int.cast_sum]
  rw [Finset.sum_congr rfl]
  intro k hk
  rw [Int.cast_mul]
  have hkn : k ≤ n := by linarith [mem_range.mp hk]
  congr 1
  exact fact_div_cast n k hkn

private lemma fact_ratio_one (n : ℕ) : (n ! : ℝ) / ((n + 1)! : ℝ) = 1 / (n + 1) := by
  rw [factorial_succ]
  field_simp
  push_cast
  ring

private lemma fact_ratio_two (n : ℕ) :
    (n ! : ℝ) / ((n + 2)! : ℝ) = 1 / ((n + 1) * (n + 2)) := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  field_simp
  norm_cast
  ring

private lemma fact_ratio_err (n : ℕ) :
    (n ! : ℝ) * ((n + 4) / (((n + 3)! : ℝ) * (n + 3)))
      = (n + 4) / ((n + 1) * (n + 2) * (n + 3) * (n + 3)) := by
  have h1 : (n + 3)! = (n + 3) * (n + 2) * (n + 1) * n ! := by
    simp [Nat.factorial_succ, mul_assoc]
  simp [h1]
  field_simp

/-- `n ! * (partial sum of the series for `e`)` is an integer. -/
private lemma exists_int_e (n : ℕ) :
    ∃ A : ℤ, (A : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / (i ! : ℝ) := by
  have key : (n ! : ℝ) * ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / (i ! : ℝ)
           = ∑ i ∈ range (n + 1), (n ! : ℝ) / (i ! : ℝ) := by
    simp [Finset.mul_sum, div_eq_mul_inv, mul_comm]
  obtain ⟨A, hA⟩ := exists_int_sum n (fun _ => 1)
  simp at hA
  exact ⟨A, hA.trans key.symm⟩

/-- `n ! * (partial sum of the series for `e⁻¹`)` is an integer. -/
private lemma exists_int_einv (n : ℕ) :
    ∃ B : ℤ, (B : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i / (i ! : ℝ) := by
  obtain ⟨B, hB⟩ := exists_int_sum n (fun i => (-1) ^ i)
  refine ⟨B, ?_⟩
  simp only [hB]
  simp [Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_assoc]

private lemma sum_split3 (x : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)
      = (∑ i ∈ range (n + 1), x ^ i / (i ! : ℝ)) + x ^ (n + 1) / ((n + 1)! : ℝ)
          + x ^ (n + 2) / ((n + 2)! : ℝ) := by
  simp only [← Finset.sum_range_succ]

private lemma num_bound_le (n : ℕ) :
    1 / ((n : ℝ) + 1) + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
        + ((n : ℝ) + 4) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 3))
      ≤ 2 / ((n : ℝ) + 1) := by
  field_simp
  ring_nf
  nlinarith [sq_nonneg (n : ℝ)]

private lemma num_bound_lt (n : ℕ) :
    ((n : ℝ) + 4) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 3))
      < 1 / ((n : ℝ) + 1) + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  field_simp
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 1), sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 3)]

/-- Truncation error of the exponential series after `n + 3` terms, for `|x| ≤ 1`. -/
private lemma exp_err (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |Real.exp x - ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)|
      ≤ ((n : ℝ) + 4) / (((n + 3)! : ℝ) * ((n : ℝ) + 3)) := by
  have key : Real.exp x = ∑' i, x ^ i / (i ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div x
  rw [key]
  -- Need to bound the tail of the exponential series
  have hs := Real.summable_pow_div_factorial x
  rw [← hs.sum_add_tsum_nat_add (k := n + 3)]
  ring_nf
  -- Goal is now in a complicated form; simplify it first
  have hrhs : (n : ℝ) * ((n : ℝ) * ((3 + n)! : ℝ) + ((3 + n)! : ℝ) * 3)⁻¹ +
              ((n : ℝ) * ((3 + n)! : ℝ) + ((3 + n)! : ℝ) * 3)⁻¹ * 4 =
              ((n : ℝ) + 4) / (((n + 3)! : ℝ) * ((n : ℝ) + 3)) := by
    field_simp
    ring_nf
  rw [hrhs]
  -- Need to show |∑' i, x^(3+n+i) / (3+n+i)!| ≤ (n+4) / ((n+3)! * (n+3))
  have hsumm : Summable (fun i => x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ)) := by
    exact Real.summable_pow_div_factorial x |>.comp_injective (add_left_injective (n + 3))
  have heq : ∀ i : ℕ, x ^ 3 * x ^ n * x ^ i * ((3 + n + i)! : ℝ)⁻¹ = x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ) := by
    intro i
    ring_nf
  simp_rw [heq]
  calc |∑' (i : ℕ), x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ)|
      ≤ ∑' (i : ℕ), |x ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ)| := by
        simp only [← Real.norm_eq_abs]
        apply norm_tsum_le_tsum_norm
        exact hsumm.norm
      _ = ∑' (i : ℕ), |x| ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ) := by
        congr 1
        ext i
        rw [abs_div, abs_pow]
        rw [abs_of_pos (by positivity : (0 : ℝ) < ((i + (n + 3))! : ℝ))]
      _ ≤ ∑' (i : ℕ), (1 : ℝ) ^ (i + (n + 3)) / ((i + (n + 3))! : ℝ) := by
        apply Summable.tsum_le_tsum
        · intro i
          gcongr
        · exact Real.summable_pow_div_factorial |x| |>.comp_injective (add_left_injective (n + 3))
        · exact Real.summable_pow_div_factorial 1 |>.comp_injective (add_left_injective (n + 3))
      _ = ∑' (i : ℕ), ((i + (n + 3))! : ℝ)⁻¹ := by simp
      _ ≤ ((n : ℝ) + 4) / (((n + 3)! : ℝ) * ((n : ℝ) + 3)) := by
        -- Each term 1/(n+3+i)! ≤ 1/((n+3)! * (n+4)^i)
        -- So the sum is ≤ 1/(n+3)! * ∑_{i=0}^∞ (1/(n+4))^i = 1/(n+3)! * (n+4)/(n+3)
        have hfact_bound : ∀ i : ℕ, ((i + (n + 3))! : ℝ) ≥ ((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ i) := by
          intro i
          induction i with
          | zero => simp
          | succ i ih =>
            have step1 : ((i + 1) + (n + 3))! = (i + 1 + (n + 3)) * (i + (n + 3))! := by
              rw [Nat.add_right_comm, Nat.factorial_succ]
            have step2 : ((i + 1) + (n + 3)) ≥ (n + 4) := by omega
            have step3 : ((i + 1 + (n + 3)) : ℝ) ≥ (n + 4) := by exact_mod_cast step2
            calc (((i + 1) + (n + 3))! : ℝ) = ((i + 1 + (n + 3)) : ℝ) * ((i + (n + 3))! : ℝ) := by
                  rw [step1]; push_cast; ring
              _ ≥ (n + 4) * ((i + (n + 3))! : ℝ) := by gcongr
              _ ≥ (n + 4) * (((n + 3)! : ℝ) * (n + 4 : ℝ) ^ i) := by gcongr
              _ = ((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ (i + 1)) := by ring
        have hbound : ∀ i : ℕ, ((i + (n + 3))! : ℝ)⁻¹ ≤ ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i := by
          intro i
          have hfact := hfact_bound i
          have hrhs_eq : ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i =
              (((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ i))⁻¹ := by
            rw [mul_inv, inv_pow]
          rw [hrhs_eq]
          exact inv_le_inv₀ (by positivity : (0 : ℝ) < ((i + (n + 3))! : ℝ))
                           (by positivity : (0 : ℝ) < ((n + 3)! : ℝ) * ((n + 4 : ℝ) ^ i)) |>.mpr hfact
        -- Sum the geometric series
        have hinv_lt_one : (n + 4 : ℝ)⁻¹ < 1 := by
          rw [inv_lt_one₀]
          · linarith
          · linarith
        have hgeom_summable : Summable (fun i : ℕ => ((n + 4 : ℝ)⁻¹) ^ i) :=
          summable_geometric_of_lt_one (by positivity) hinv_lt_one
        have hsum_bound : ∑' i : ℕ, ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i =
            ((n + 3)! : ℝ)⁻¹ * ((n + 4) / (n + 3)) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv_lt_one]
          have hpos : (n : ℝ) + 3 ≠ 0 := by linarith
          have hpos2 : (1 - (n + 4 : ℝ)⁻¹) ≠ 0 := by
            have : (n + 4 : ℝ)⁻¹ < 1 := hinv_lt_one
            linarith
          have heq2 : (1 - (n + 4 : ℝ)⁻¹)⁻¹ = (n + 4) / (n + 3) := by
            have h1 : (1 - (n + 4 : ℝ)⁻¹) = ((n + 3) : ℝ) / (n + 4) := by
              field_simp
              ring
            rw [h1]
            field_simp
          rw [heq2]
        have hfinal : ((n + 3)! : ℝ)⁻¹ * ((n + 4) / (n + 3)) = (n + 4) / ((n + 3)! * (n + 3)) := by
          field_simp
        rw [hfinal] at hsum_bound
        have hsumm2 : Summable (fun i => ((n + 3)! : ℝ)⁻¹ * ((n + 4 : ℝ)⁻¹) ^ i) :=
          hgeom_summable.mul_left _
        have hsumm1 : Summable (fun i => ((i + (n + 3))! : ℝ)⁻¹) := by
          have := Real.summable_pow_div_factorial (1 : ℝ) |>.comp_injective (add_left_injective (n + 3))
          simp only [one_pow] at this
          simp only [one_div] at this
          exact this
        exact le_trans (Summable.tsum_le_tsum hbound hsumm1 hsumm2) hsum_bound.le

/-- Rewriting `n !` times the partial sum of length `n + 3`. -/
private lemma partial_sum_mul (x : ℝ) (n : ℕ) (A : ℤ)
    (hA : (A : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), x ^ i / (i ! : ℝ)) :
    (n ! : ℝ) * ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)
      = A + (x ^ (n + 1) * (1 / ((n : ℝ) + 1))
          + x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) := by
  rw [sum_split3]
  rw [hA]
  have h1 : (n ! : ℝ) * (x ^ (n + 1) / ((n + 1)! : ℝ)) = x ^ (n + 1) * (1 / ((n : ℝ) + 1)) := by
    rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, fact_ratio_one]
  have h2 : (n ! : ℝ) * (x ^ (n + 2) / ((n + 2)! : ℝ)) = x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, fact_ratio_two]
  rw [mul_add, mul_add, h1, h2]
  ring

/-- The key approximation: if `A = n ! * (partial sum up to `n`)`, then `n ! * exp x` differs
from `A` by the two next terms of the series, up to a small error. -/
private lemma tail_key (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (A : ℤ)
    (hA : (A : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), x ^ i / (i ! : ℝ)) :
    |(n ! : ℝ) * Real.exp x - A
        - (x ^ (n + 1) * (1 / ((n : ℝ) + 1))
            + x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))))|
      ≤ ((n : ℝ) + 4) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 3)) := by
  have h1 := partial_sum_mul x n A hA
  have h2 := exp_err x hx n
  have h3 := fact_ratio_err n
  -- n! * exp x - A - main_terms = n! * (exp x - partial sum)
  have heq : (n ! : ℝ) * Real.exp x - A - (x ^ (n + 1) * (1 / ((n : ℝ) + 1))
      + x ^ (n + 2) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) =
      (n ! : ℝ) * (Real.exp x - ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)) := by
    linarith [h1]
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n !)]
  apply le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h3.le

/-- `n ! * e` is a positive amount (at most `2/(n+1)`) above an integer. -/
private lemma tail_exp_one (n : ℕ) :
    ∃ A : ℤ, 0 < (n ! : ℝ) * Real.exp 1 - A ∧ (n ! : ℝ) * Real.exp 1 - A ≤ 2 / (n + 1) := by
  obtain ⟨A, hA⟩ := exists_int_e n
  use A
  have hx : |(1 : ℝ)| ≤ 1 := by norm_num
  have hbound := tail_key 1 hx n A hA
  -- For x = 1: 1^(n+1) = 1, 1^(n+2) = 1, so main terms = 1/(n+1) + 1/((n+1)(n+2))
  simp only [one_pow] at hbound
  have hnum_lt := num_bound_lt n
  have hnum_le := num_bound_le n
  have habs := abs_le.mp hbound
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- For `n` even, `n ! * e⁻¹` is strictly below an integer, by at most `2/(n+1)`. -/
private lemma tail_exp_neg_one (n : ℕ) (hn : Even n) :
    ∃ B : ℤ, (n ! : ℝ) * Real.exp (-1) - B < 0 ∧
      -(2 / (n + 1)) ≤ (n ! : ℝ) * Real.exp (-1) - B := by
  obtain ⟨B, hB⟩ := exists_int_einv n
  use B
  have hx : |(-1 : ℝ)| ≤ 1 := by norm_num
  have hkey := tail_key (-1) hx n B hB
  -- Since n is even: (-1)^(n+1) = -1 and (-1)^(n+2) = 1
  have hexp1 : (-1 : ℝ) ^ (n + 1) = -1 := by
    rw [even_iff_two_dvd] at hn
    obtain ⟨k, hk⟩ := hn
    simp [hk, pow_add]
  have hexp2 : (-1 : ℝ) ^ (n + 2) = 1 := by
    rw [even_iff_two_dvd] at hn
    obtain ⟨k, hk⟩ := hn
    simp [hk, pow_add]
  rw [hexp1, hexp2] at hkey
  -- Simplify: -1/(n+1) + 1/((n+1)*(n+2)) = -1/(n+2)
  have hsimplify : -1 * (1 / ((n : ℝ) + 1)) + 1 * (1 / ((n + 1) * (n + 2) : ℝ)) = -1 / (n + 2) := by
    field_simp
    ring
  rw [hsimplify] at hkey
  -- hkey: |δ + 1/(n+2)| ≤ error where δ = n! * e^(-1) - B
  -- So: -error - 1/(n+2) ≤ δ ≤ error - 1/(n+2)
  set δ := (n ! : ℝ) * Real.exp (-1) - B with hδ_def
  set error := (n + 4 : ℝ) / ((n + 1) * (n + 2) * (n + 3) * (n + 3)) with herror_def
  have hneg : δ - -1 / (n + 2 : ℝ) = δ + 1 / (n + 2) := by ring
  have hkey' : -error - 1 / (n + 2) ≤ δ ∧ δ ≤ error - 1 / (n + 2) := by
    have := abs_le.mp hkey
    rw [hneg] at this
    constructor <;> linarith
  -- For δ < 0, need error < 1/(n+2)
  have herror_lt : error < 1 / (n + 2) := by
    rw [herror_def]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n + 1) * (n + 2) * (n + 3) * (n + 3)) (by positivity : (0 : ℝ) < n + 2)]
    ring_nf
    nlinarith [sq_nonneg (n : ℝ)]
  have h1 : δ < 0 := by linarith [hkey'.2, herror_lt]
  -- For -2/(n+1) ≤ δ, need error + 1/(n+2) ≤ 2/(n+1)
  -- num_bound_le: 1/(n+1) + 1/((n+1)*(n+2)) + error ≤ 2/(n+1)
  have h2 : -(2 / (n + 1)) ≤ δ := by
    have hkey'_lower := hkey'.1
    have hbound : -(2 / (n + 1)) ≤ -error - 1 / (n + 2) := by
      rw [herror_def]
      field_simp
      ring_nf
      nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 3)]
    linarith
  exact ⟨h1, h2⟩

/-- e² is irrational. -/
theorem exp_two_irrational : Irrational (Real.exp 2) := by
  -- Key insight: e² = (n! * e) / (n! * e^{-1})
  -- If e² = p/q, then q * (n! * e) = p * (n! * e^{-1})
  -- This leads to pB - qA = qδ₁ + pδ₂ where δ₁, δ₂ are small
  -- For large n, qδ₁ + pδ₂ < 1, but pB - qA is a positive integer, contradiction!
  by_contra h
  rw [Irrational] at h
  push_neg at h
  obtain ⟨r, hr⟩ := h
  -- We'll use n = 2 * (|p| + q) to ensure n is even and large enough
  -- First, establish that r > 0 so p > 0
  have hr_pos : (r : ℝ) > 0 := by rw [hr]; exact Real.exp_pos 2
  have hr_pos_rat : r > 0 := by contrapose! hr_pos; exact mod_cast hr_pos
  have hp_pos' : r.num > 0 := Rat.num_pos.mpr hr_pos_rat
  -- Use n = 2 * (|p| + q) to ensure n is even and large enough
  set n := 2 * (r.num.natAbs + r.den) with hn_def
  have hn_even : Even n := even_two_mul _
  have hq_pos : 0 < r.den := r.pos
  -- Get bounds on n! * e and n! * e^{-1}
  obtain ⟨A, hA_pos, hA_bound⟩ := tail_exp_one n
  obtain ⟨B, hB_neg, hB_bound⟩ := tail_exp_neg_one n hn_even
  -- n! * e = A + δ₁ where 0 < δ₁ ≤ 2/(n+1)
  set δ₁ := (n ! : ℝ) * Real.exp 1 - A with hδ₁_def
  have hδ₁_pos : 0 < δ₁ := hA_pos
  have hδ₁_bound : δ₁ ≤ 2 / (n + 1) := hA_bound
  -- n! * e^{-1} = B - δ₂ where 0 < δ₂ ≤ 2/(n+1)
  set δ₂ := B - (n ! : ℝ) * Real.exp (-1) with hδ₂_def
  have hδ₂_pos : 0 < δ₂ := by linarith
  have hδ₂_bound : δ₂ ≤ 2 / (n + 1) := by linarith
  -- e² = (n! * e) / (n! * e^{-1}) = (A + δ₁) / (B - δ₂)
  have he2_eq : Real.exp 2 = Real.exp 1 / Real.exp (-1) := by
    rw [← Real.exp_sub]; norm_num
  have hexp_ratio : Real.exp 2 = ((n ! : ℝ) * Real.exp 1) / ((n ! : ℝ) * Real.exp (-1)) := by
    rw [mul_div_mul_left _ _ (by positivity : (n ! : ℝ) ≠ 0)]
    exact he2_eq
  -- Let X = n! * e = A + δ₁ and Y = n! * e^{-1} = B - δ₂
  set X := (n ! : ℝ) * Real.exp 1 with hX_def
  set Y := (n ! : ℝ) * Real.exp (-1) with hY_def
  have hX_eq : X = A + δ₁ := by rw [hδ₁_def]; ring
  have hY_eq : Y = B - δ₂ := by rw [hδ₂_def]; ring
  -- If e² = r = p/q, then X / Y = r, so X = r * Y
  -- This means q * X = p * Y, so q(A + δ₁) = p(B - δ₂)
  -- Therefore pB - qA = qδ₁ + pδ₂ > 0
  have hr_eq_exp2 : (r : ℝ) = Real.exp 2 := hr
  have hXY_ne_zero : Y ≠ 0 := by simp [hY_def]; positivity
  have hXY_ratio : X / Y = r := by rw [← hexp_ratio, hr_eq_exp2]
  have hqX_eq_pY : (r.den : ℝ) * X = r.num * Y := by
    have h1 : X = r * Y := by field_simp [hXY_ne_zero] at hXY_ratio ⊢; linarith
    calc (r.den : ℝ) * X = r.den * (r * Y) := by rw [h1]
      _ = (r.den * r) * Y := by ring
      _ = r.num * Y := by rw [show (r.den : ℝ) * r = r.num from by simp [Rat.cast_def]; field_simp]
  -- pB - qA = qδ₁ + pδ₂
  set p := r.num with hp_def
  set q := r.den with hq_def
  have hpB_qA : (p : ℝ) * B - (q : ℝ) * A = (q : ℝ) * δ₁ + (p : ℝ) * δ₂ := by
    rw [hX_eq, hY_eq] at hqX_eq_pY
    linarith
  -- p > 0 since r = exp(2) > 0
  have hp_pos : p > 0 := hp_pos'
  -- pB - qA > 0
  have hpB_qA_pos : (p : ℝ) * B - (q : ℝ) * A > 0 := by
    rw [hpB_qA]
    have hp_pos_real : (p : ℝ) > 0 := mod_cast hp_pos
    have hq_pos_real : (q : ℝ) > 0 := mod_cast hq_pos
    nlinarith [hδ₁_pos, hδ₂_pos]
  -- But q * δ₁ + p * δ₂ < 1 for our choice of n
  -- The sum q * δ₁ + p * δ₂ ≤ (p + q) * 2 / (n + 1)
  have hsum_bound : (q : ℝ) * δ₁ + (p : ℝ) * δ₂ ≤ ((p.natAbs : ℝ) + q) * 2 / (n + 1) := by
    have hp_pos_real : (p : ℝ) = (p.natAbs : ℝ) := by
      simp [abs_of_pos (by exact_mod_cast hp_pos : (p : ℝ) > 0)]
    rw [hp_pos_real]
    have h1 : (q : ℝ) * δ₁ + (p.natAbs : ℝ) * δ₂ ≤ (q : ℝ) * (2 / (n + 1)) + (p.natAbs : ℝ) * (2 / (n + 1)) := by
      nlinarith [hδ₁_bound, hδ₂_bound]
    have h2 : (q : ℝ) * (2 / (n + 1)) + (p.natAbs : ℝ) * (2 / (n + 1)) = ((p.natAbs : ℝ) + q) * 2 / (n + 1) := by ring
    linarith
  -- With n = 2 * (p.natAbs + q), we have (p.natAbs + q) * 2 / (n + 1) < 1
  have hlt_one : ((p.natAbs : ℝ) + q) * 2 / (n + 1) < 1 := by
    rw [hn_def]
    have hpq_pos : (p.natAbs : ℝ) + q > 0 := by positivity
    rw [div_lt_one (by linarith : (n : ℝ) + 1 > 0)]
    rw [hn_def]
    norm_cast
    linarith
  -- Therefore p * B - q * A < 1
  have hpbqa_lt_one : (p : ℝ) * B - (q : ℝ) * A < 1 := by linarith [hsum_bound, hlt_one]
  -- But p * B - q * A is a positive integer, so ≥ 1, contradiction!
  have hpbqa_int : ∃ m : ℤ, (p : ℝ) * B - (q : ℝ) * A = m := ⟨p * B - q * A, by push_cast; ring⟩
  obtain ⟨m, hm⟩ := hpbqa_int
  have hm_pos : m > 0 := Int.cast_pos.mp (hm ▸ hpB_qA_pos)
  have hm_ge_one : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
  linarith

end Brockian.MsE2Irrational

