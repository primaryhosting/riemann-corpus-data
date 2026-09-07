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
# Polignac's Conjecture — CONDITIONAL reduction

CONDITIONAL: Polignac's conjecture (for every positive even `n` there are infinitely
many consecutive prime pairs with gap `n`) assuming the two-form Dickson hypothesis
(`DicksonPairHypothesis`).

This module records the genuine proven implication
`DicksonPairHypothesis → ∀ n, Even n → 0 < n → {p | ConsecutivePrimeGap n p}.Infinite`.
The namespace is `Brockian.PolignacPrimesReduction` to avoid clashing with the existing
`Brockian.PolignacPrimes` module that records the bare conjecture.
-/

open Finset

namespace Brockian.PolignacPrimesReduction

/-- `ConsecutivePrimeGap n p` says that `p` and `p + n` are primes and that there is no
prime strictly between them, i.e. `p` and `p + n` are *consecutive* primes with gap `n`. -/
def ConsecutivePrimeGap (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + n) ∧ ∀ q, p < q → q < p + n → ¬ Nat.Prime q

/-- The two-form Dickson (prime-tuples) hypothesis: for an arithmetic progression `a * x + b`
with `a > 0`, if the pair of linear forms `a * x + b`, `a * x + b + c` is admissible — i.e. for
every prime `Q` there is some `x` for which `Q` divides neither value — then both forms are
simultaneously prime for infinitely many `x`. -/
def DicksonPairHypothesis : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < c →
    (∀ Q : ℕ, Nat.Prime Q → ∃ x : ℕ, ¬ Q ∣ (a * x + b) ∧ ¬ Q ∣ (a * x + b + c)) →
    {x : ℕ | Nat.Prime (a * x + b) ∧ Nat.Prime (a * x + b + c)}.Infinite

/-- An auxiliary family of large primes: `bigPrime n j` is the `(n + j)`-th prime,
so it is always larger than `n` as soon as `j ≥ 1`. -/
noncomputable def bigPrime (n j : ℕ) : ℕ := Nat.nth Nat.Prime (n + j)

lemma bigPrime_prime (n j : ℕ) : Nat.Prime (bigPrime n j) := Nat.prime_nth_prime _

lemma lt_bigPrime {n j : ℕ} (hj : 1 ≤ j) : n < bigPrime n j := by
  have h : n + j ≤ bigPrime n j :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).le_apply (x := n + j)
  omega

lemma bigPrime_inj (n : ℕ) : Function.Injective (bigPrime n) := by
  intro i j h
  have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h
  omega

/-- The modulus of the arithmetic progression used to prove Polignac's conjecture from
Dickson's hypothesis: the product of the auxiliary primes `bigPrime n j`, `1 ≤ j < n`. -/
noncomputable def modulus (n : ℕ) : ℕ := ∏ j ∈ Finset.Ico 1 n, bigPrime n j

lemma modulus_pos (n : ℕ) : 0 < modulus n :=
  Finset.prod_pos fun j _ => (bigPrime_prime n j).pos

lemma bigPrime_dvd_modulus {n j : ℕ} (hj : j ∈ Finset.Ico 1 n) : bigPrime n j ∣ modulus n :=
  Finset.dvd_prod_of_mem _ hj

/-- The chosen residue class, via the Chinese remainder theorem: a natural number `k` with
`k ≡ -j (mod bigPrime n j)` for every `1 ≤ j < n`. -/
noncomputable def shiftSub (n : ℕ) :
    {k : ℕ // ∀ j ∈ Finset.Ico 1 n, k ≡ bigPrime n j - j [MOD bigPrime n j]} :=
  Nat.chineseRemainderOfFinset (fun j => bigPrime n j - j) (bigPrime n) (Finset.Ico 1 n)
    (fun j _ => (bigPrime_prime n j).pos.ne') (by
      intro i _ j _ hij
      exact (Nat.coprime_primes (bigPrime_prime n i) (bigPrime_prime n j)).2
        (fun h => hij (bigPrime_inj n h)))

/-- The residue class used in the construction. -/
noncomputable def shift (n : ℕ) : ℕ := (shiftSub n : ℕ)

lemma bigPrime_dvd_shift_add {n j : ℕ} (hj : j ∈ Finset.Ico 1 n) :
    bigPrime n j ∣ (shift n + j) := by
  have h := (shiftSub n).prop j hj
  have hj1 : 1 ≤ j := by simp at hj; omega
  have hjn : j < n := by simp at hj; omega
  have hle : j ≤ bigPrime n j := le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hjn (le_refl n))
    (le_of_lt (lt_bigPrime (n := n) (j := j) hj1)))
  have h2 : shift n + j ≡ (bigPrime n j - j) + j [MOD bigPrime n j] := h.add_right j
  rw [Nat.sub_add_cancel hle] at h2
  have h3 : shift n + j ≡ 0 [MOD bigPrime n j] := h2.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
  exact Nat.modEq_zero_iff_dvd.1 h3

/-- Admissibility of the pair of forms `modulus n * x + shift n`, `modulus n * x + shift n + n`. -/
lemma admissible {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) (Q : ℕ) (hQ : Nat.Prime Q) :
    ∃ x : ℕ, ¬ Q ∣ (modulus n * x + shift n) ∧ ¬ Q ∣ (modulus n * x + shift n + n) := by
  set M := modulus n with hMdef
  set r := shift n with hrdef
  by_cases hQM : Q ∣ M
  · -- `Q` is one of the auxiliary primes `bigPrime n j`
    obtain ⟨j, hj, hjd⟩ := (Prime.dvd_finset_prod_iff hQ.prime _).1 (hMdef ▸ hQM)
    have hQj : Q = bigPrime n j := ((Nat.prime_dvd_prime_iff_eq hQ (bigPrime_prime n j)).1 hjd)
    have hj1 : 1 ≤ j := by simp at hj; omega
    have hjn : j < n := by simp at hj; omega
    have hdvd : Q ∣ (r + j) := hQj ▸ bigPrime_dvd_shift_add hj
    have hQn : n < Q := hQj ▸ lt_bigPrime (n := n) (j := j) hj1
    refine ⟨0, ?_, ?_⟩
    · intro h
      have hr : Q ∣ r := by simpa using h
      have hdj : Q ∣ j := by
        simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdvd hr
      have := Nat.le_of_dvd (by omega) hdj
      omega
    · intro h
      have h' : Q ∣ (r + n) := by simpa using h
      have hdn : Q ∣ (n - j) := by
        have := Nat.dvd_sub h' hdvd
        simpa [Nat.add_sub_add_left] using this
      have := Nat.le_of_dvd (by omega) hdn
      omega
  · -- `Q` does not divide the modulus
    rcases eq_or_lt_of_le hQ.two_le with hQ2 | hQ3
    · -- `Q = 2`
      have hQ2' : Q = 2 := hQ2.symm
      subst hQ2'
      have hMo : M % 2 = 1 := by
        rcases Nat.even_or_odd M with h | h
        · exact absurd h.two_dvd hQM
        · omega
      have hne : n % 2 = 0 := by
        rcases hn with ⟨k, hk⟩; omega
      rcases Nat.even_or_odd r with h | h
      · refine ⟨1, ?_, ?_⟩ <;> rw [Nat.dvd_iff_mod_eq_zero] <;> rcases h with ⟨k, hk⟩ <;> omega
      · refine ⟨0, ?_, ?_⟩ <;> rw [Nat.dvd_iff_mod_eq_zero] <;> rcases h with ⟨k, hk⟩ <;> omega
    · -- `Q ≥ 3`
      by_contra hcon
      push_neg at hcon
      have step : ∀ (c x y : ℕ), x < y → y ≤ x + 2 →
          Q ∣ (M * x + r + c) → Q ∣ (M * y + r + c) → False := by
        intro c x y hxy hy h1 h2
        obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
        have he : M * (x + d) + r + c = (M * x + r + c) + M * d := by ring
        rw [he] at h2
        have hd : Q ∣ M * d := (Nat.dvd_add_right h1).1 h2
        rcases (Nat.Prime.dvd_mul hQ).1 hd with h | h
        · exact hQM h
        · have := Nat.le_of_dvd (by omega) h
          omega
      have h0 := hcon 0
      have h1 := hcon 1
      have h2 := hcon 2
      rcases Classical.em (Q ∣ (M * 0 + r)) with a0 | a0 <;>
        rcases Classical.em (Q ∣ (M * 1 + r)) with a1 | a1 <;>
          rcases Classical.em (Q ∣ (M * 2 + r)) with a2 | a2 <;>
      first
        | exact step 0 0 1 (by omega) (by omega) (by simpa using a0) (by simpa using a1)
        | exact step 0 0 2 (by omega) (by omega) (by simpa using a0) (by simpa using a2)
        | exact step 0 1 2 (by omega) (by omega) (by simpa using a1) (by simpa using a2)
        | exact step n 0 1 (by omega) (by omega) (h0 a0) (h1 a1)
        | exact step n 0 2 (by omega) (by omega) (h0 a0) (h2 a2)
        | exact step n 1 2 (by omega) (by omega) (h1 a1) (h2 a2)

/-- **Polignac's conjecture, conditional on the two-form Dickson hypothesis.**
For every positive even `n` there are infinitely many primes `p` such that `p` and `p + n`
are consecutive primes. -/
theorem PolignacConjecture (H : DicksonPairHypothesis) (n : ℕ) (hn : Even n) (hpos : 0 < n) :
    {p : ℕ | ConsecutivePrimeGap n p}.Infinite := by
  have hn2 : 2 ≤ n := by rcases hn with ⟨k, hk⟩; omega
  set M := modulus n with hMdef
  set r := shift n with hrdef
  have hM0 : 0 < M := modulus_pos n
  have hinf := H M r n hM0 hpos (admissible hn hn2)
  have hinf' : ({x : ℕ | Nat.Prime (M * x + r) ∧ Nat.Prime (M * x + r + n)} \ {0}).Infinite :=
    hinf.diff (Set.finite_singleton 0)
  have hinj : Set.InjOn (fun x => M * x + r)
      ({x : ℕ | Nat.Prime (M * x + r) ∧ Nat.Prime (M * x + r + n)} \ {0}) := by
    intro x _ y _ hxy
    simp only at hxy
    have : M * x = M * y := by omega
    exact Nat.eq_of_mul_eq_mul_left hM0 this
  refine Set.Infinite.mono ?_ (hinf'.image hinj)
  rintro p ⟨x, ⟨⟨hp1, hp2⟩, hx0⟩, rfl⟩
  show ConsecutivePrimeGap n (M * x + r)
  have hx1 : 1 ≤ x := by
    simp only [Set.mem_singleton_iff] at hx0
    omega
  refine ⟨hp1, hp2, ?_⟩
  intro q hq1 hq2 hqp
  set j := q - (M * x + r) with hjdef
  have hj : j ∈ Finset.Ico 1 n := by simp [hjdef]; omega
  have hqj : q = M * x + r + j := by omega
  have hdvd : bigPrime n j ∣ q := by
    rw [hqj]
    have h1 : bigPrime n j ∣ M * x := Dvd.dvd.mul_right (bigPrime_dvd_modulus hj) x
    have h2 : bigPrime n j ∣ (r + j) := bigPrime_dvd_shift_add hj
    have hrw : M * x + r + j = M * x + (r + j) := by ring
    rw [hrw]
    exact Nat.dvd_add h1 h2
  have hle : bigPrime n j ≤ M := Nat.le_of_dvd hM0 (bigPrime_dvd_modulus hj)
  have hMx : M ≤ M * x := Nat.le_mul_of_pos_right M hx1
  have hlt : bigPrime n j < q := by omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hqp _ hdvd) with h | h
  · exact (bigPrime_prime n j).one_lt.ne' h
  · omega

end Brockian.PolignacPrimesReduction
