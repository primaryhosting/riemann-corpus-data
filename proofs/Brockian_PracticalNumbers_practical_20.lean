import Mathlib

/-!
# Practical numbers

A **practical number** `n` is a positive integer such that every integer `m` with
`1 ≤ m ≤ n` can be written as a sum of *distinct* divisors of `n`. Equivalently (allowing
the empty sum for `m = 0`), every `m ≤ n` is the sum of some subset of `n.divisors`.

The first practical numbers are `1, 2, 4, 6, 8, 12, 16, 20, 24, 28, …`. Every power of two
is practical — this is the structural heart of the file — because the divisors of `2 ^ k`
are exactly the powers `1, 2, 4, …, 2 ^ k`, and every `m ≤ 2 ^ k` is a sum of distinct
powers of two (its binary expansion), each of which is a divisor.

A **practical twin** is a pair `p, p + 2` with both members practical (the additive analogue
of twin primes for practicality). Whether there are **infinitely many** practical twins is a
Margenstern-type OPEN problem. This file:

* proves the general structural theorem `practical_pow_two` — *every* power of two is
  practical (real induction, not a table lookup);
* verifies concrete practical numbers `6, 12, 20, 28` and the non-example `10`
  (kernel `decide`, no `native_decide`);
* records the practical-twin infinitude question as an unproven `def`
  (`PracticalTwinInfinitude`) — it is **not** claimed to be resolved here, in either
  direction.
-/

namespace Brockian.PracticalNumbers

/-- `n` is a **practical number**: every `m ≤ n` is a sum of a subset of the divisors of
`n`. (The `m = 0` case uses the empty subset; positivity is recorded explicitly.) -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ∈ n.divisors.powerset, (∑ d ∈ s, d) = m

/-- OPEN (Margenstern-type): are there infinitely many **practical twins** `p, p + 2` with
both `p` and `p + 2` practical? Recorded as an unproven `def`; this file does **not** prove
it (nor its negation). -/
def PracticalTwinInfinitude : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Practical p ∧ Practical (p + 2)

/-! ## Flagship general theorem: every power of two is practical -/

/-- **Every power of two is practical.**

The divisors of `2 ^ k` are `{1, 2, 4, …, 2 ^ k}`, and every `m ≤ 2 ^ k` is a sum of
distinct powers of two. Formalised by induction on `k`: given the claim for `2 ^ k` and a
target `m ≤ 2 ^ (k+1) = 2 · 2 ^ k`,

* if `m ≤ 2 ^ k`, the inductive subset already lies in `divisors (2 ^ (k+1))`
  (since `2 ^ k ∣ 2 ^ (k+1)`);
* if `m = 2 ^ (k+1)`, the singleton `{2 ^ (k+1)}` works;
* otherwise `2 ^ k < m < 2 ^ (k+1)`, so `m - 2 ^ k < 2 ^ k`; the inductive subset `s`
  summing to `m - 2 ^ k` cannot contain `2 ^ k` (its sum is too small), so
  `insert (2 ^ k) s` is a subset of the divisors summing to `m`. -/
theorem practical_pow_two (k : ℕ) : Practical (2 ^ k) := by
  induction k with
  | zero =>
    refine ⟨by norm_num, ?_⟩
    intro m hm
    norm_num at hm
    interval_cases m <;> decide
  | succ k ih =>
    obtain ⟨_, ihf⟩ := ih
    have hne : (2 : ℕ) ^ (k + 1) ≠ 0 := (pow_pos (by norm_num) _).ne'
    have hsucc : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hdvd : (2 : ℕ) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
    have hsub : ((2 : ℕ) ^ k).divisors ⊆ (2 ^ (k + 1)).divisors :=
      Nat.divisors_subset_of_dvd hne hdvd
    refine ⟨by positivity, ?_⟩
    intro m hm
    rw [hsucc] at hm
    by_cases h : m ≤ 2 ^ k
    · -- `m ≤ 2 ^ k`: reuse the inductive subset, which still lies in the larger divisor set.
      obtain ⟨s, hs, hsum⟩ := ihf m h
      refine ⟨s, ?_, hsum⟩
      rw [Finset.mem_powerset] at hs ⊢
      exact hs.trans hsub
    · -- `2 ^ k < m ≤ 2 · 2 ^ k`.
      have hm' : m - 2 ^ k ≤ 2 ^ k := by omega
      rcases eq_or_lt_of_le hm' with heq | hlt
      · -- `m = 2 ^ (k+1)`: the singleton top divisor.
        refine ⟨{2 ^ (k + 1)}, ?_, ?_⟩
        · rw [Finset.mem_powerset, Finset.singleton_subset_iff, Nat.mem_divisors]
          exact ⟨dvd_refl _, hne⟩
        · rw [Finset.sum_singleton, hsucc]; omega
      · -- `m - 2 ^ k < 2 ^ k`: adjoin `2 ^ k` to the inductive subset.
        obtain ⟨s, hs, hsum⟩ := ihf (m - 2 ^ k) hm'
        rw [Finset.mem_powerset] at hs
        have hnotin : 2 ^ k ∉ s := by
          intro hc
          have hle : 2 ^ k ≤ ∑ d ∈ s, d :=
            Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) hc
          rw [hsum] at hle
          omega
        refine ⟨insert (2 ^ k) s, ?_, ?_⟩
        · rw [Finset.mem_powerset, Finset.insert_subset_iff]
          refine ⟨?_, hs.trans hsub⟩
          rw [Nat.mem_divisors]
          exact ⟨hdvd, hne⟩
        · rw [Finset.sum_insert hnotin, hsum]; omega

/-! ## Concrete practical numbers (kernel-checked) -/

set_option maxRecDepth 4000 in
/-- `6` is practical: divisors `1, 2, 3, 6` reach every `m ≤ 6`. -/
theorem practical_6 : Practical 6 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 4000 in
/-- `12` is practical: divisors `1, 2, 3, 4, 6, 12`. -/
theorem practical_12 : Practical 12 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 4000 in
/-- `20` is practical: divisors `1, 2, 4, 5, 10, 20`. -/
theorem practical_20 : Practical 20 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 6000 in
/-- `28` is practical: divisors `1, 2, 4, 7, 14, 28` (and `28` is also a perfect number). -/
theorem practical_28 : Practical 28 := ⟨by norm_num, by decide⟩

/-! ## A non-example -/

set_option maxRecDepth 4000 in
/-- `10` is **not** practical: its divisors are `1, 2, 5, 10`, and `4` cannot be written as
a sum of distinct divisors (the only subsets summing near `4` give `1, 2, 3, 5, …`, never
`4`). -/
theorem not_practical_10 : ¬ Practical 10 := by
  unfold Practical
  decide

end Brockian.PracticalNumbers
