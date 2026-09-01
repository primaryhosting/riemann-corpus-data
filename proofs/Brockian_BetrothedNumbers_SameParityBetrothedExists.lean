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

/-
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- `sigmaOne n` is the sum of all divisors of `n`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `Betrothed m n` says that `m` and `n` form a *betrothed* (quasi-amicable) pair:
they are distinct positive integers such that the sum of the proper divisors of each
one is one more than the other, i.e. `σ(m) = σ(n) = m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- A number is of *square type* if it is a perfect square or twice a perfect square. -/
def SquareType (n : ℕ) : Prop := ∃ a, n = a ^ 2 ∨ n = 2 * a ^ 2

section SigmaParity

lemma sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = (sigma 1) n := by
  rw [sigma_one_apply]; rfl

/-- For an odd prime `p`, `σ(p ^ k)` is odd exactly when `k` is even. -/
lemma odd_sigmaOne_prime_pow_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    Odd (sigmaOne (p ^ k)) ↔ Even k := by
  have key : sigmaOne (p ^ k) % 2 = (k + 1) % 2 := by
    unfold sigmaOne
    rw [Nat.sum_divisors_prime_pow hp, Finset.sum_nat_mod]
    rw [Finset.sum_congr rfl (fun i _ => Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow (n := i)))]
    simp
  rw [Nat.odd_iff, Nat.even_iff, key]
  omega

/-- If `σ(n)` is odd then every odd prime occurs to an even power in `n`. -/
lemma even_factorization_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Even (n.factorization p) := by
  by_cases hmem : p ∈ n.factorization.support
  · have hprod := (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hn
    have hdvd : (sigma 1) (p ^ n.factorization p) ∣ (sigma 1) n := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem (fun q => (sigma 1) (q ^ n.factorization q)) hmem
    rw [← sigmaOne_eq_sigma, ← sigmaOne_eq_sigma] at hdvd
    refine (odd_sigmaOne_prime_pow_iff hp hp2 _).mp ?_
    rcases Nat.even_or_odd (sigmaOne (p ^ n.factorization p)) with he | ho
    · exfalso
      have h2 : 2 ∣ sigmaOne n := dvd_trans he.two_dvd hdvd
      have := Nat.odd_iff.mp h
      omega
    · exact ho
  · simp [Finsupp.notMem_support_iff.mp hmem]

/-- If `σ(n)` is odd then `n` is a square or twice a square. -/
theorem squareType_of_odd_sigmaOne {n : ℕ} (hn : 0 < n) (h : Odd (sigmaOne n)) :
    SquareType n := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have ha2 : ∀ {d : ℕ}, d.Prime → d ∣ a → d = 2 := by
    intro d hd hda
    by_contra hne
    have hdn : n.factorization d = 2 * b.factorization d + a.factorization d := by
      rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne']
      simp [Nat.factorization_pow, two_mul]
    have h1 : a.factorization d = 1 :=
      le_antisymm (hsq.natFactorization_le_one d) (hd.factorization_pos_of_dvd ha.ne' hda)
    obtain ⟨c, hc⟩ := even_factorization_of_odd_sigmaOne hn.ne' h hd hne
    omega
  have hpow : a = 2 ^ a.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd ha.ne' ha2
  have hL : a.primeFactorsList.length ≤ 1 := by
    have h2 := hsq.natFactorization_le_one 2
    rw [hpow] at h2
    simpa [Nat.Prime.factorization_pow, Nat.prime_two] using h2
  interval_cases hle : a.primeFactorsList.length
  · exact ⟨b, Or.inl (by simp [hpow] at *; omega)⟩
  · refine ⟨b, Or.inr ?_⟩
    rw [hpow] at hab
    simp at hab
    omega

end SigmaParity

/-- Both members of a same-parity betrothed pair are of square type. -/
theorem squareType_of_betrothed_sameParity {m n : ℕ} (hb : Betrothed m n)
    (hpar : m % 2 = n % 2) : SquareType m ∧ SquareType n := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := hb
  have hodd : Odd (m + n + 1) := by rw [Nat.odd_iff]; omega
  exact ⟨squareType_of_odd_sigmaOne hm (hsm ▸ hodd),
    squareType_of_odd_sigmaOne hn (hsn ▸ hodd)⟩

/-- The classical smallest betrothed pair `(48, 75)`; it has *opposite* parity.
This witnesses that `Betrothed` is not vacuous. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> (unfold sigmaOne; decide)

/-- **Conditional reduction for the same-parity betrothed number problem.**

Whether a betrothed (quasi-amicable) pair of the same parity exists is an open problem;
all known betrothed pairs consist of one even and one odd number.  What is proved here is
a reduction: such a pair exists if and only if one exists in which *both* members are a
perfect square or twice a perfect square. -/
theorem SameParityBetrothedExists :
    (∃ m n, Betrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n, Betrothed m n ∧ m % 2 = n % 2 ∧ SquareType m ∧ SquareType n) := by
  constructor
  · rintro ⟨m, n, hb, hpar⟩
    exact ⟨m, n, hb, hpar, (squareType_of_betrothed_sameParity hb hpar).1,
      (squareType_of_betrothed_sameParity hb hpar).2⟩
  · rintro ⟨m, n, hb, hpar, -, -⟩
    exact ⟨m, n, hb, hpar⟩

/-- If a betrothed pair of two odd numbers exists, both members are (odd) perfect squares. -/
theorem odd_betrothed_isSquare {m n : ℕ} (hb : Betrothed m n)
    (hm : Odd m) (hn : Odd n) : (∃ a, m = a ^ 2) ∧ (∃ b, n = b ^ 2) := by
  have hpar : m % 2 = n % 2 := by
    rw [Nat.odd_iff] at hm hn; omega
  obtain ⟨⟨a, hA⟩, ⟨b, hB⟩⟩ := squareType_of_betrothed_sameParity hb hpar
  rw [Nat.odd_iff] at hm hn
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · rcases hA with hA | hA
    · exact hA
    · omega
  · rcases hB with hB | hB
    · exact hB
    · omega

end Brockian.BetrothedNumbers

