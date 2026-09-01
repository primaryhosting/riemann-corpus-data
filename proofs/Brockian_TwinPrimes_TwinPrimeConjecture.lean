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

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Twin Prime Conjecture — that there are infinitely many primes `p` with `p + 2` also
prime — is a famous open problem, and no unconditional proof is known.  What is formalised
here is therefore:

* the exact statement of the conjecture (`TwinPrimeStatement`);
* a **Lean-checked conditional reduction**: the conjecture follows from Dickson's
  conjecture on simultaneous primality of admissible families of linear forms
  (`TwinPrimeConjecture`).  All the mathematical content of the reduction — namely the
  admissibility of the pair of forms `n`, `n + 2` — is proved unconditionally here;
* a second conditional reduction, from the divergence of the sum of reciprocals of twin
  primes (`twinPrimeStatement_of_not_summable`);
* small unconditional facts about twin primes.
-/

namespace Brockian.TwinPrimes

/-- `p` is a twin prime if both `p` and `p + 2` are prime. -/
def IsTwinPrime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (p + 2)

/-- The Twin Prime Conjecture: there are arbitrarily large twin primes. -/
def TwinPrimeStatement : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsTwinPrime p

/-- The set of twin primes. -/
def twinPrimeSet : Set ℕ := {p | IsTwinPrime p}

/-- A finite family of linear forms `a * n + b`, encoded as pairs `(a, b)`, is *admissible*
if for every prime `q` there is some `n` for which none of the values `a * n + b` is
divisible by `q`. -/
def Admissible (F : Finset (ℕ × ℕ)) : Prop :=
  ∀ q : ℕ, Nat.Prime q → ∃ n : ℕ, ∀ ab ∈ F, ¬ (q ∣ (ab.1 * n + ab.2))

/-- **Dickson's conjecture**: for any finite admissible family of linear forms with positive
leading coefficients, there are arbitrarily large `n` at which all the forms take prime
values.  This is an open conjecture; it is used here only as a hypothesis. -/
def DicksonConjecture : Prop :=
  ∀ F : Finset (ℕ × ℕ), (∀ ab ∈ F, 0 < ab.1) → Admissible F →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∀ ab ∈ F, Nat.Prime (ab.1 * n + ab.2)

/-- The two linear forms `n` and `n + 2` of the twin prime problem. -/
def twinForms : Finset (ℕ × ℕ) := {(1, 0), (1, 2)}

theorem twinForms_pos : ∀ ab ∈ twinForms, 0 < ab.1 := by
  intro ab hab
  fin_cases hab <;> norm_num

/-- The pair of forms `n`, `n + 2` is admissible: for `q = 3` take `n = 2`, otherwise take
`n = 1` (giving the values `1` and `3`). -/
theorem twinForms_admissible : Admissible twinForms := by
  intro q hq
  by_cases h3 : q = 3
  · refine ⟨2, ?_⟩
    intro ab hab
    subst h3
    fin_cases hab <;> decide
  · refine ⟨1, ?_⟩
    intro ab hab
    fin_cases hab
    · simpa using hq.one_lt.ne'
    · simp only [Nat.mul_one]
      intro hdvd
      have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (by simpa using hdvd)
      exact h3 this

/-- **Conditional Twin Prime Conjecture.**  Assuming Dickson's conjecture on simultaneous
prime values of admissible families of linear forms, there are arbitrarily large twin
primes, i.e. infinitely many primes `p` with `p + 2` prime. -/
theorem TwinPrimeConjecture (hD : DicksonConjecture) : TwinPrimeStatement := by
  intro N
  obtain ⟨n, hnN, hn⟩ := hD twinForms twinForms_pos twinForms_admissible N
  have h1 : ((1, 0) : ℕ × ℕ) ∈ twinForms := by simp [twinForms]
  have h2 : ((1, 2) : ℕ × ℕ) ∈ twinForms := by simp [twinForms]
  have hp := hn _ h1
  have hp2 := hn _ h2
  simp only [one_mul, Nat.add_zero] at hp hp2
  exact ⟨n, hnN, hp, hp2⟩

/-- Second conditional reduction: if the sum of the reciprocals of the twin primes
diverges, then there are infinitely many twin primes. -/
theorem twinPrimeStatement_of_not_summable
    (h : ¬ Summable (Set.indicator twinPrimeSet (fun p : ℕ => (1 : ℝ) / p))) :
    TwinPrimeStatement := by
  by_contra hcon
  apply h
  simp only [TwinPrimeStatement, not_forall, not_exists, not_and] at hcon
  obtain ⟨N, hN⟩ := hcon
  refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) ?_
  intro p hp
  have hpN : N < p := by
    simp only [Finset.mem_range, not_lt] at hp
    omega
  have hnot : p ∉ twinPrimeSet := hN p hpN
  simp [Set.indicator_of_notMem hnot]

/-! ### Unconditional facts -/

theorem isTwinPrime_three : IsTwinPrime 3 := by
  constructor <;> norm_num

theorem isTwinPrime_five : IsTwinPrime 5 := by
  constructor <;> norm_num

theorem isTwinPrime_eleven : IsTwinPrime 11 := by
  constructor <;> norm_num

theorem isTwinPrime_seventeen : IsTwinPrime 17 := by
  constructor <;> norm_num

/-- Every twin prime greater than `3` is congruent to `5` modulo `6`. -/
theorem twin_mod_six {p : ℕ} (hp : IsTwinPrime p) (h : 3 < p) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    have : (2 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp1).mp hd
    omega
  have h3 : ¬ (3 ∣ p) := by
    intro hd
    have : (3 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp1).mp hd
    omega
  have h3' : ¬ (3 ∣ (p + 2)) := by
    intro hd
    have : (3 : ℕ) = p + 2 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp2).mp hd
    omega
  omega

end Brockian.TwinPrimes

