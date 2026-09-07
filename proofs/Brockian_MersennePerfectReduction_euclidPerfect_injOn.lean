import Mathlib

/-!
# Mersenne / Even-Perfect reduction equivalences (Euclid–Euler)

REDUCTION-EQUIVALENCE (CONDITIONAL): each theorem below proves an unconditional
equivalence `A ↔ B`; **both sides remain OPEN**.  These are Lean-checked reductions
(via the Euclid–Euler theorem), **NOT** a resolution of either the infinitude of even
perfect numbers or the infinitude of Mersenne primes.

* `EvenPerfectInfinitude` : the even perfect numbers are infinite **iff** the Mersenne
  prime exponents are infinite.
* `MersennePrimeInfinitude` : the Mersenne primes (exponents `p` with `p` and `2^p - 1`
  both prime) are infinite **iff** the even perfect numbers are infinite.

Both statements on each side are unknown open problems.

The Euclid–Euler correspondence lemmas live only in Mathlib's `Archive`
(`Theorems100.Nat`), which is **not** part of `import Mathlib`.  They are therefore
re-proved here from main-library API only (Author of the original Archive proof:
Aaron Anderson); no `sorry`, `admit`, `native_decide`, or added axiom is used.
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Brockian.MersennePerfectReduction

open Nat
open ArithmeticFunction Finset
open scoped sigma

/-! ## Euclid–Euler machinery (re-proved from main-library API) -/

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- **Euclid's direction**: a Mersenne prime induces an even perfect number. -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Euler's direction**: every even perfect number is `2 ^ k · mersenne (k+1)`
with `mersenne (k+1)` prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply _root_.ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

/-- **Euclid–Euler**, as an `iff` (re-proved locally, replacing the Archive lemma
`Theorems100.Nat.even_and_perfect_iff`): `n` is even and perfect iff `n = 2^k·(2^(k+1)-1)`
with `2^(k+1)-1` a Mersenne prime. -/
theorem even_and_perfect_iff {n : ℕ} :
    (Even n ∧ Nat.Perfect n) ↔ ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, hk, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k hk, perfect_two_pow_mul_mersenne_of_prime k hk⟩

/-! ## Theorem 1 — EvenPerfectInfinitude -/

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n | Even n ∧ Nat.Perfect n}

/-- The set of `k` such that the Mersenne number `2 ^ (k + 1) - 1` is prime. -/
def MersenneExponents : Set ℕ := {k | Nat.Prime (mersenne (k + 1))}

/-- The Euclid map `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)`. -/
def euclidMap (k : ℕ) : ℕ := 2 ^ k * mersenne (k + 1)

lemma mersenne_succ_pos (k : ℕ) : 0 < mersenne (k + 1) := by
  have h : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [mersenne]
  omega

lemma euclidMap_strictMono : StrictMono euclidMap := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 : (2 : ℕ) ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne (n + 1) < mersenne (n + 1 + 1) := by
    have hlt : (2 : ℕ) ^ (n + 1) < 2 ^ (n + 1 + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hp := mersenne_succ_pos n
    simp only [mersenne] at *
    omega
  have h3 : 2 ^ n * mersenne (n + 1) ≤ 2 ^ (n + 1) * mersenne (n + 1) :=
    Nat.mul_le_mul_right _ h1
  have h4 : 2 ^ (n + 1) * mersenne (n + 1) < 2 ^ (n + 1) * mersenne (n + 1 + 1) :=
    by gcongr
  simpa [euclidMap] using lt_of_le_of_lt h3 h4

lemma euclidMap_injective : Function.Injective euclidMap :=
  euclidMap_strictMono.injective

/-- **Euclid–Euler**, restated as a set identity: the even perfect numbers are exactly the
image of the Mersenne prime exponents under `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)`. -/
theorem evenPerfects_eq_image : EvenPerfects = euclidMap '' MersenneExponents := by
  ext n
  simp only [EvenPerfects, MersenneExponents, Set.mem_setOf_eq, Set.mem_image, euclidMap]
  rw [even_and_perfect_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

/-- **Even Perfect Infinitude (conditional reduction).**  There are infinitely many even perfect
numbers if and only if there are infinitely many Mersenne primes. -/
theorem EvenPerfectInfinitude : EvenPerfects.Infinite ↔ MersenneExponents.Infinite := by
  rw [evenPerfects_eq_image, Set.infinite_image_iff euclidMap_injective.injOn]

/-- The conditional form: infinitely many Mersenne primes yields infinitely many even
perfect numbers. -/
theorem evenPerfect_infinite_of_mersenne_infinite (h : MersenneExponents.Infinite) :
    EvenPerfects.Infinite :=
  EvenPerfectInfinitude.mpr h

/-- Conversely, infinitely many even perfect numbers yields infinitely many Mersenne primes. -/
theorem mersenne_infinite_of_evenPerfect_infinite (h : EvenPerfects.Infinite) :
    MersenneExponents.Infinite :=
  EvenPerfectInfinitude.mp h

/-- A sanity check that the sets involved are non-vacuous: `6` is an even perfect number,
witnessed by the Mersenne prime `3 = 2 ^ 2 - 1`. -/
theorem six_mem_evenPerfects : 6 ∈ EvenPerfects := by
  have hp : Nat.Prime (mersenne (1 + 1)) := by norm_num [mersenne]
  refine ⟨⟨3, by norm_num⟩, ?_⟩
  have := perfect_two_pow_mul_mersenne_of_prime 1 hp
  norm_num [mersenne] at this
  exact this

/-! ## Theorem 2 — MersennePrimeInfinitude -/

/-- The Euclid perfect number attached to an exponent `p`: `2 ^ (p - 1) * (2 ^ p - 1)`. -/
def euclidPerfect (p : ℕ) : ℕ := 2 ^ (p - 1) * mersenne p

/-- The set of exponents `p` such that `p` and `mersenne p = 2 ^ p - 1` are both prime. -/
def mersennePrimeExponents : Set ℕ := {p : ℕ | p.Prime ∧ (mersenne p).Prime}

/-- The set of even perfect numbers (predicate form for Theorem 2). -/
def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

lemma euclidPerfect_mem_evenPerfects {p : ℕ} (hp : p.Prime) (h : (mersenne p).Prime) :
    euclidPerfect p ∈ evenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd h (by decide)
    · exact hk
  have hperf : (euclidPerfect (k + 1)).Perfect := by
    simpa [euclidPerfect] using perfect_two_pow_mul_mersenne_of_prime k h
  refine ⟨?_, hperf⟩
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have : (2 : ℕ) ∣ euclidPerfect (k + 1) := by
    simpa [euclidPerfect] using h2.mul_right (mersenne (k + 1))
  exact (even_iff_two_dvd).2 this

lemma evenPerfects_subset_image :
    evenPerfects ⊆ euclidPerfect '' mersennePrimeExponents := by
  rintro n ⟨hne, hnp⟩
  obtain ⟨k, hk, rfl⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect hne hnp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact absurd hk (by decide)
  have hp : (k + 1).Prime := (Nat.prime_of_pow_sub_one_prime (by omega) hk).2
  exact ⟨k + 1, ⟨hp, hk⟩, by simp [euclidPerfect]⟩

lemma euclidPerfect_strictMonoOn : StrictMonoOn euclidPerfect {p : ℕ | 1 ≤ p} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  have h1 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h3 : (1 : ℕ) ≤ 2 ^ a := Nat.one_le_two_pow
  have h4 : (0 : ℕ) < 2 ^ (b - 1) := Nat.two_pow_pos _
  have h5 : mersenne a < mersenne b := by simp only [mersenne]; omega
  exact Nat.mul_lt_mul_of_le_of_lt h1 h5 h4

lemma euclidPerfect_injOn : Set.InjOn euclidPerfect mersennePrimeExponents := by
  intro a ha b hb hab
  have h : ∀ p ∈ mersennePrimeExponents, p ∈ {q : ℕ | 1 ≤ q} := by
    rintro p ⟨hp, -⟩
    exact hp.one_lt.le
  exact euclidPerfect_strictMonoOn.injOn (h a ha) (h b hb) hab

/-- **Reduction of the infinitude of Mersenne primes.**
There are infinitely many Mersenne primes (equivalently, infinitely many exponents `p` with
`p` and `2 ^ p - 1` both prime) if and only if there are infinitely many even perfect numbers.
Both statements are open; this is a Lean-checked equivalence, via Euclid–Euler. -/
theorem MersennePrimeInfinitude :
    {p : ℕ | p.Prime ∧ (mersenne p).Prime}.Infinite ↔ {n : ℕ | Even n ∧ n.Perfect}.Infinite := by
  constructor
  · intro h
    have himg : (euclidPerfect '' mersennePrimeExponents).Infinite := h.image euclidPerfect_injOn
    refine himg.mono ?_
    rintro n ⟨p, ⟨hp, hmp⟩, rfl⟩
    exact euclidPerfect_mem_evenPerfects hp hmp
  · intro h
    have himg : (euclidPerfect '' mersennePrimeExponents).Infinite :=
      Set.Infinite.mono evenPerfects_subset_image h
    exact himg.of_image _

end Brockian.MersennePerfectReduction
