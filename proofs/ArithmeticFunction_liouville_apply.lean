import Mathlib

/-!
# Parity/sieve arithmetic: two missing Liouville / Möbius divisor identities

Both statements are about the Liouville function `λ` (`ArithmeticFunction.liouville`) and the
Möbius function `μ` (`ArithmeticFunction.moebius`). The Möbius function is Mathlib's; the
Liouville function is *not* present in the Mathlib version pinned by this project, so it is
defined below in the `ArithmeticFunction` namespace, together with the facts that it is
completely multiplicative (`liouville_apply_mul`, `isMultiplicative_liouville`) and its value on
prime powers. Mathlib does not prove the classical square-indicator divisor identity below.
These are the arithmetic backbone of the parity phenomenon in sieve theory.
-/

namespace ArithmeticFunction

/-- The Liouville function `λ n = (-1) ^ Ω n` (with `λ 0 = 0`), where `Ω n` is the number of
prime factors of `n` counted with multiplicity.

Note: the current Mathlib version pinned by this project (`v4.28.0`) does not contain a
definition named `ArithmeticFunction.liouville`, so it is supplied here, in Mathlib's own
`ArithmeticFunction` namespace, exactly as the classical function. -/
def liouville : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else (-1) ^ cardFactors n
  map_zero' := by simp

@[simp]
theorem liouville_apply {n : ℕ} (hn : n ≠ 0) : liouville n = (-1) ^ cardFactors n := by
  simp [liouville, hn]

/-- `λ` is completely multiplicative. -/
theorem liouville_apply_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    liouville (m * n) = liouville m * liouville n := by
  rw [liouville_apply (by positivity), liouville_apply hm, liouville_apply hn,
    cardFactors_mul hm hn, pow_add]

theorem isMultiplicative_liouville : liouville.IsMultiplicative := by
  constructor
  · simp [liouville]
  · intro m n _
    rcases eq_or_ne m 0 with rfl | hm
    · simp [liouville]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [liouville]
    exact liouville_apply_mul hm hn

theorem liouville_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    liouville (p ^ k) = (-1) ^ k := by
  rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]

/-- Local factor: the sum of `λ` over the divisors of a prime power. -/
theorem sum_liouville_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, liouville d = if Even k then 1 else 0 := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [liouville_prime_pow hp]
  rw [neg_one_geom_sum]
  rcases Nat.even_or_odd k with hk | hk
  · rw [if_pos hk, if_neg fun h => (Nat.even_add_one.mp h) hk]
  · have hk' : ¬ Even k := by simpa [Nat.not_even_iff_odd] using hk
    rw [if_neg hk', if_pos (Nat.even_add_one.mpr hk')]

end ArithmeticFunction

namespace BrockianParity

/-- A positive natural number is a square iff every exponent in its prime factorization
is even. -/
theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp
  · intro h
    refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨t, ht⟩ := h p
    omega

/-- **Liouville divisor-sum identity** (the Dirichlet convolution `λ ⋆ 1`).
For `n ≥ 1`, the sum of the Liouville function over the divisors of `n` is `1` when `n`
is a perfect square and `0` otherwise.

Intuition/proof sketch: `λ` is completely multiplicative, so `∑_{d ∣ n} λ(d)` is multiplicative
in `n`; on a prime power `p^a` it is `∑_{j=0}^{a} (-1)^j = 1` if `a` is even, `0` if `a` is odd;
the product over the prime factorization is therefore `1` iff every exponent is even, i.e. iff `n`
is a perfect square. Useful Mathlib: `ArithmeticFunction.liouville`, `liouville_apply`,
`liouville_apply_mul`, `isMultiplicative_liouville`, `Nat.ArithmeticFunction.IsMultiplicative`
divisor-sum lemmas, `Nat.isSquare_iff_...`/`Nat.factorization` characterisations of squares. -/
theorem liouville_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ArithmeticFunction.liouville d = if IsSquare n then 1 else 0 := by
  have hmul : ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
      ArithmeticFunction.liouville).IsMultiplicative :=
    (ArithmeticFunction.IsMultiplicative.natCast ArithmeticFunction.isMultiplicative_zeta).mul
      ArithmeticFunction.isMultiplicative_liouville
  rw [← ArithmeticFunction.coe_zeta_mul_apply, hmul.multiplicative_factorization _ hn]
  have hfac : ∀ p ∈ n.factorization.support,
      ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * ArithmeticFunction.liouville)
          (p ^ n.factorization p)
        = if Even (n.factorization p) then 1 else 0 := by
    intro p hp
    rw [ArithmeticFunction.coe_zeta_mul_apply,
      ArithmeticFunction.sum_liouville_divisors_prime_pow
        (Nat.prime_of_mem_primeFactors (by simpa using hp))]
  rw [Finsupp.prod, Finset.prod_congr rfl hfac]
  by_cases hsq : IsSquare n
  · rw [if_pos hsq]
    exact Finset.prod_eq_one fun p _ => if_pos ((isSquare_iff_even_factorization hn).mp hsq p)
  · rw [if_neg hsq]
    obtain ⟨p, hp⟩ : ∃ p, ¬ Even (n.factorization p) := by
      by_contra h
      push_neg at h
      exact hsq ((isSquare_iff_even_factorization hn).mpr h)
    refine Finset.prod_eq_zero (i := p) ?_ (by rw [if_neg hp])
    simp only [Finsupp.mem_support_iff]
    intro h
    rw [h] at hp
    exact hp Even.zero

/-- **Squarefree-divisor count.** For `n ≥ 1`, `∑_{d ∣ n} μ(d)^2` counts the squarefree divisors
of `n`, which equals `2 ^ ω(n)` where `ω(n) = n.primeFactors.card` is the number of distinct
primes dividing `n`.

Intuition/proof sketch: `μ(d)^2 = 1` iff `d` is squarefree and `0` otherwise
(`moebius_sq_eq_one_of_squarefree`), so the sum counts squarefree divisors; a squarefree divisor is
exactly a product of a subset of the distinct prime factors, giving `2 ^ ω(n)`. -/
theorem squarefree_divisor_count (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) ^ 2 = 2 ^ n.primeFactors.card := by
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors Squarefree]
  have h2 : ∑ d ∈ n.divisors with ¬ Squarefree d, (ArithmeticFunction.moebius d) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter] at hd
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd.2]
    ring
  rw [h2, add_zero, Finset.sum_congr rfl fun d hd =>
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree (Finset.mem_filter.mp hd).2]
  rw [Nat.sum_divisors_filter_squarefree hn]
  simp [Nat.factors_eq]

end BrockianParity

