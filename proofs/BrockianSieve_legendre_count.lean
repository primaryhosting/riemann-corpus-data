import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve

open ArithmeticFunction Finset

/-- Legendre's identity: the number of `n ∈ [1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`. -/
lemma legendre_count (x P : ℕ) (hP : P ≠ 0) :
    ((((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ))
      = ∑ d ∈ P.divisors, (moebius d : ℤ) * ((x / d : ℕ) : ℤ) := by
  have hdelta : ∀ n : ℕ, ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    intro n
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (moebius : ArithmeticFunction ℤ)) (x := n),
      moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n; simp [Nat.lt_iff_add_one_le]
  have step1 : ((((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ))
      = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ P.divisors, (if d ∣ n then (moebius d : ℤ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hgcd : (Nat.gcd n P).divisors = P.divisors.filter (· ∣ n) := by
      ext d
      simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hP, Nat.gcd_eq_zero_iff, hn0]
      tauto
    have h := hdelta (Nat.gcd n P)
    rw [hgcd, Finset.sum_filter] at h
    rw [← h]
  rw [step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [hIcc]
  exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) (Nat.Ioc_filter_dvd_card_eq_div x d)

/-- Expanding the product over the prime factors of `P`:
`∏_{p ∣ P} (1 - 1/p) = ∑_{d ∣ P} μ(d)/d`. -/
lemma prod_one_sub_inv_eq_sum (P : ℕ) (hP : P ≠ 0) :
    ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) = ∑ d ∈ P.divisors, (moebius d : ℝ) * (d : ℝ)⁻¹ := by
  have hL : ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)
      = ∑ t ∈ P.primeFactors.powerset, ∏ p ∈ t, (-(p : ℝ)⁻¹) := by
    have := Finset.prod_add (fun p : ℕ => (-(p : ℝ)⁻¹)) (fun _ => (1 : ℝ)) P.primeFactors
    simpa [sub_eq_neg_add] using this
  have hfil : ∑ d ∈ P.divisors, (moebius d : ℝ) * (d : ℝ)⁻¹
      = ∑ d ∈ P.divisors.filter Squarefree, (moebius d : ℝ) * (d : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hs : Squarefree d
    · simp [hs]
    · simp [hs, moebius_eq_zero_of_not_squarefree hs]
  have h2 : (UniqueFactorizationMonoid.normalizedFactors P).toFinset = P.primeFactors := by
    rw [Nat.factors_eq]; rfl
  have hR := Nat.sum_divisors_filter_squarefree (n := P) hP
    (f := fun d => (moebius d : ℝ) * (d : ℝ)⁻¹)
  rw [h2] at hR
  rw [hL, hfil, hR]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_powerset] at ht
  have hprod : t.val.prod = ∏ p ∈ t, p := by rw [Finset.prod_eq_multiset_prod]; simp
  simp only [hprod]
  have hcop : (↑t : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (ht ha))
      (Nat.prime_of_mem_primeFactors (ht hb))).2 hab
  have hmu : (moebius (∏ p ∈ t, p) : ℤ) = ∏ p ∈ t, (moebius p) :=
    isMultiplicative_moebius.map_prod (fun p : ℕ => p) t hcop
  have hmu' : ((moebius (∏ p ∈ t, p) : ℤ) : ℝ) = ∏ p ∈ t, (-1 : ℝ) := by
    rw [hmu]
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [moebius_apply_prime (Nat.prime_of_mem_primeFactors (ht hp))]
    norm_num
  rw [hmu', Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by ring

/-- The number of squarefree divisors of `P` is `2 ^ ω(P)`. -/
lemma card_squarefree_divisors (P : ℕ) (hP : P ≠ 0) :
    (P.divisors.filter Squarefree).card = 2 ^ P.primeFactors.card := by
  have h := Nat.sum_divisors_filter_squarefree (n := P) hP (f := fun _ => (1 : ℕ))
  have h2 : (UniqueFactorizationMonoid.normalizedFactors P).toFinset = P.primeFactors := by
    rw [Nat.factors_eq]; rfl
  simpa [h2, Finset.card_powerset] using h

/-- Each term `μ(d)(⌊x/d⌋ - x/d)` has absolute value at most `1`, and vanishes unless `d`
is squarefree. -/
lemma term_bound (x d : ℕ) (hd : d ≠ 0) :
    |(moebius d : ℝ) * (((x / d : ℕ) : ℝ) - (x : ℝ) * (d : ℝ)⁻¹)|
      ≤ if Squarefree d then 1 else 0 := by
  by_cases hs : Squarefree d
  · simp only [hs, if_true]
    rw [abs_mul]
    have h1 : |(moebius d : ℝ)| = 1 := by
      have := abs_moebius_eq_one_of_squarefree hs
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [h1, one_mul]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hle : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) * (d : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hdR]
      exact_mod_cast Nat.div_mul_le_self x d
    have hgt : (x : ℝ) * (d : ℝ)⁻¹ < ((x / d : ℕ) : ℝ) + 1 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hdR]
      have hx : x < (x / d + 1) * d := by
        have h1 := Nat.div_add_mod x d
        have h2 := Nat.mod_lt x hdpos
        nlinarith [h1, h2]
      exact_mod_cast hx
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · simp [hs, moebius_eq_zero_of_not_squarefree hs]

/-- The count of integers in `[1, x]` coprime to `P` differs from the heuristic main term
`x · ∏_{p ∣ P} (1 − 1/p)` by at most `2^{ω(P)}` (the number of squarefree divisors of `P`).
(Sanity: `x=10, P=6`: count `=3`, main term `=10·(1/2)(2/3)=10/3`, `|3−10/3|=1/3 ≤ 4 = 2²`.)
Proof idea: count `= ∑_{d ∣ P} μ(d) ⌊x/d⌋` (Legendre); main term `= ∑_{d ∣ P} μ(d) · x/d`; the
difference is `∑_{d ∣ P} μ(d)(⌊x/d⌋ − x/d)` with each term of absolute value `< 1`, and there are
`2^{ω(P)}` nonzero (squarefree-`d`) terms. -/
theorem legendre_sieve_error (x P : ℕ) (hP : P ≠ 0) :
    |(((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℝ)
        - (x : ℝ) * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)|
      ≤ (2 : ℝ) ^ P.primeFactors.card := by
  have hcount : (((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℝ)
      = ∑ d ∈ P.divisors, (moebius d : ℝ) * ((x / d : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (legendre_count x P hP)
    push_cast at this
    exact this
  have hmain : (x : ℝ) * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)
      = ∑ d ∈ P.divisors, (moebius d : ℝ) * ((x : ℝ) * (d : ℝ)⁻¹) := by
    rw [prod_one_sub_inv_eq_sum P hP, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcount, hmain, ← Finset.sum_sub_distrib]
  have hle : |∑ d ∈ P.divisors, ((moebius d : ℝ) * ((x / d : ℕ) : ℝ)
        - (moebius d : ℝ) * ((x : ℝ) * (d : ℝ)⁻¹))|
      ≤ ∑ d ∈ P.divisors, (if Squarefree d then (1 : ℝ) else 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hd)
    calc |(moebius d : ℝ) * ((x / d : ℕ) : ℝ) - (moebius d : ℝ) * ((x : ℝ) * (d : ℝ)⁻¹)|
        = |(moebius d : ℝ) * (((x / d : ℕ) : ℝ) - (x : ℝ) * (d : ℝ)⁻¹)| := by ring_nf
      _ ≤ _ := term_bound x d hd0
  refine hle.trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  rw [card_squarefree_divisors P hP]
  push_cast
  ring_nf
  rfl

end BrockianSieve

