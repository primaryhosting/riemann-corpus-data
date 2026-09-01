import Mathlib
namespace MS.Foundations

theorem fundamental_theorem_of_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z, p.eval z = 0 :=
  Complex.exists_root hp

theorem infinitude_of_primes : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOf_prime

theorem irrational_sqrt_two : Irrational (Real.sqrt 2) := _root_.irrational_sqrt_two

section ExpIrrational

open Nat Finset

/-- The `n`-th partial sum of the exponential series at `1`, i.e. `∑_{m < n+1} 1/m!`. -/
private noncomputable def expPartial (n : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), (1 : ℝ) ^ m / m !

/-- `n! * (e - S_{n+1})` is strictly positive, since the exponential series has positive terms. -/
private theorem expTail_pos (n : ℕ) : 0 < (n ! : ℝ) * (Real.exp 1 - expPartial n) := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (n + 2)
  rw [Finset.sum_range_succ] at h
  have hfn : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hp : (0 : ℝ) < 1 ^ (n + 1) / (((n + 1)! : ℕ) : ℝ) := by positivity
  have hgt : (0 : ℝ) < Real.exp 1 - expPartial n := by
    simp only [expPartial]; linarith
  exact mul_pos hfn hgt

/-- `n! * (e - S_{n+1}) < 1` for `n ≥ 1`, from the standard tail bound on the exponential series. -/
private theorem expTail_lt_one (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) * (Real.exp 1 - expPartial n) < 1 := by
  have hb := Real.exp_bound (x := 1) (by norm_num) (n := n + 1) (by omega)
  have hfn : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfac : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have key : Real.exp 1 - expPartial n ≤ ((n : ℝ) + 2) / ((((n + 1)! : ℕ) : ℝ) * ((n : ℝ) + 1)) := by
    refine (le_abs_self _).trans (hb.trans_eq ?_)
    push_cast
    norm_num
    ring
  have hlt : (n ! : ℝ) * (((n : ℝ) + 2) / ((((n + 1)! : ℕ) : ℝ) * ((n : ℝ) + 1))) < 1 := by
    rw [hfac, show (n ! : ℝ) * (((n : ℝ) + 2) / (((n : ℝ) + 1) * (n ! : ℝ) * ((n : ℝ) + 1)))
        = ((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1)) by field_simp,
      div_lt_one (by positivity)]
    nlinarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left key hfn.le) hlt

/-- `n! * S_{n+1}` is a natural number. -/
private theorem factorial_mul_expPartial (n : ℕ) :
    ((∑ m ∈ Finset.range (n + 1), n ! / m ! : ℕ) : ℝ) = (n ! : ℝ) * expPartial n := by
  rw [expPartial, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
  ring

/-- If `x` is rational then `q.den ! * x` is an integer. -/
private theorem exists_int_factorial_mul (q : ℚ) : ∃ k : ℤ, (k : ℝ) = ((q.den)! : ℝ) * (q : ℝ) := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos (le_refl q.den)
  refine ⟨(c : ℤ) * q.num, ?_⟩
  have h : ((q.den : ℝ)) * (q : ℝ) = (q.num : ℝ) := by rw [Rat.cast_def]; field_simp
  rw [hc]
  push_cast
  rw [show ((q.den : ℝ) * c * q) = c * ((q.den : ℝ) * q) by ring, h]

theorem irrational_e : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  set n := q.den
  have hn1 : 1 ≤ n := q.pos
  obtain ⟨k, hk⟩ := exists_int_factorial_mul q
  rw [hq] at hk
  refine absurd (expTail_lt_one n hn1) (not_lt.mpr ?_)
  set M : ℤ := k - (∑ m ∈ Finset.range (n + 1), n ! / m ! : ℕ) with hM
  have hMR : (M : ℝ) = (n ! : ℝ) * (Real.exp 1 - expPartial n) := by
    rw [hM, Int.cast_sub, Int.cast_natCast, factorial_mul_expPartial n, mul_sub, ← hk]
  have hMpos : 0 < M := by
    have := expTail_pos n
    rw [← hMR] at this
    exact_mod_cast this
  have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
  rw [hMR] at this
  exact this

end ExpIrrational

theorem exists_prime_factorization (n : ℕ) (hn : 2 ≤ n) :
    ∃ l : Multiset ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n :=
  ⟨(n.primeFactorsList : Multiset ℕ), fun _ hp => Nat.prime_of_mem_primeFactorsList hp,
    by simpa using Nat.prod_primeFactorsList (by omega)⟩

end MS.Foundations

