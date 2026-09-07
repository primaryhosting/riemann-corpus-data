/-
  Brockian/ZumkellerNumbers.lean — Zumkeller numbers via the half-sum characterization.

  A natural number `n` is *Zumkeller* if the set of its divisors can be partitioned
  into two subsets of equal sum. Equivalently (and this is the form we use), there is
  a subset `S` of `n.divisors` whose sum is exactly half of `σ(n) = ∑ d ∈ n.divisors, d`,
  i.e. `2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d`. Taking `S` and its complement inside
  `n.divisors` recovers the two equal-sum parts.

  GENERAL (structural) results proved here:
    * `zumkeller_sigma_even`      — every Zumkeller number has even divisor sum σ(n).
    * `zumkeller_two_mul_le_sigma` — every positive Zumkeller number is perfect-or-abundant,
                                     `2 * n ≤ σ(n)`. This is the flagship theorem.
    * `not_zumkeller_prime`       — no prime is Zumkeller.

  CONCRETE witnesses (explicit partitioning subset, discharged by computation):
    * `zumkeller_six`, `zumkeller_twelve`, `zumkeller_twenty`,
      `zumkeller_twentyfour`, `zumkeller_twentyeight`, `zumkeller_thirty`.

  OPEN marker (a `def`, never a theorem):
    * `OddZumkellerFrom3Structure` — records the (unproven, open) structural question about
      odd Zumkeller numbers. It is stated but deliberately NOT proved.

  No `sorry`, `admit`, `native_decide`, or `axiom` is used anywhere in this file.
-/
import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of σ(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- GENERAL: the divisor sum of a Zumkeller number is even, since it equals `2 * (S.sum)`. -/
theorem zumkeller_sigma_even {n : ℕ} (h : Zumkeller n) :
    Even (∑ d ∈ n.divisors, d) := by
  obtain ⟨S, _, hS⟩ := h
  exact ⟨∑ d ∈ S, d, by rw [← hS]; ring⟩

/-- GENERAL (flagship): every positive Zumkeller number is perfect-or-abundant, i.e.
`2 * n ≤ σ(n)`. Proof: `n` is one of its own divisors. Let `S` be the witnessing subset
and `T = n.divisors \ S` its complement. Then `S.sum + T.sum = σ(n)` and `2 * S.sum = σ(n)`,
so `2 * T.sum = σ(n)` as well. Whichever of `S`, `T` contains `n` has sum `≥ n` (single-term
lower bound), and that sum is `σ(n) / 2`; hence `σ(n) ≥ 2 * n`. -/
theorem zumkeller_two_mul_le_sigma {n : ℕ} (hn : 0 < n) (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨S, hSsub, hS⟩ := h
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  -- complement of S inside the divisors
  set T : Finset ℕ := n.divisors \ S with hT
  -- T.sum + S.sum = σ(n)
  have hsplit : (∑ d ∈ T, d) + (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d := by
    rw [hT]; exact Finset.sum_sdiff hSsub
  -- 2 * T.sum = σ(n) as well
  have hTsum : 2 * (∑ d ∈ T, d) = ∑ d ∈ n.divisors, d := by
    have : (∑ d ∈ T, d) + (∑ d ∈ S, d) = 2 * (∑ d ∈ S, d) := by rw [hsplit, hS]
    omega
  -- n lies in S or in its complement T
  rcases Finset.mem_union.mp
      (show n ∈ T ∪ S by
        rw [hT, Finset.sdiff_union_of_subset hSsub]; exact hn_mem)
      with hnT | hnS
  · -- n ∈ T : T.sum ≥ n, and 2 * T.sum = σ(n)
    have hle : n ≤ ∑ d ∈ T, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnT
    omega
  · -- n ∈ S : S.sum ≥ n, and 2 * S.sum = σ(n)
    have hle : n ≤ ∑ d ∈ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnS
    omega

/-- GENERAL: no prime is Zumkeller. A prime `p` is deficient: `σ(p) = 1 + p < 2 * p` for
`p ≥ 2`. But every positive Zumkeller number is perfect-or-abundant (`2 * p ≤ σ(p)`), so a
Zumkeller prime would force `2 * p ≤ 1 + p`, i.e. `p ≤ 1`, contradicting `p ≥ 2`. -/
theorem not_zumkeller_prime {p : ℕ} (hp : p.Prime) : ¬ Zumkeller p := by
  intro h
  have hle := zumkeller_two_mul_le_sigma hp.pos h
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, hp.sum_properDivisors] at hle
  -- hle : 2 * p ≤ 1 + p, but p ≥ 2
  have := hp.two_le
  omega

/-- Concrete witness: `6` is Zumkeller. Divisors `{1,2,3,6}`, σ = 12; take `S = {1,2,3}`. -/
theorem zumkeller_six : Zumkeller 6 := by
  refine ⟨{1, 2, 3}, ?_, ?_⟩
  · decide
  · decide

/-- Concrete witness: `12` is Zumkeller. Divisors `{1,2,3,4,6,12}`, σ = 28; take `S = {2,4,6,2}`?
Use `S = {12, 2}`? We take `S = {1,3,6,2,...}`. Choose `S = {2, 4, 12}` sums to 18 ≠ 14.
Correct: σ = 28, half = 14; `S = {12, 2}` sums to 14. -/
theorem zumkeller_twelve : Zumkeller 12 := by
  refine ⟨{12, 2}, ?_, ?_⟩
  · decide
  · decide

/-- Concrete witness: `20` is Zumkeller. Divisors `{1,2,4,5,10,20}`, σ = 42, half = 21;
`S = {20, 1}` sums to 21. -/
theorem zumkeller_twenty : Zumkeller 20 := by
  refine ⟨{20, 1}, ?_, ?_⟩
  · decide
  · decide

/-- Concrete witness: `24` is Zumkeller. Divisors `{1,2,3,4,6,8,12,24}`, σ = 60, half = 30;
`S = {24, 6}` sums to 30. -/
theorem zumkeller_twentyfour : Zumkeller 24 := by
  refine ⟨{24, 6}, ?_, ?_⟩
  · decide
  · decide

/-- Concrete witness: `28` is a perfect number, hence Zumkeller. Divisors `{1,2,4,7,14,28}`,
σ = 56, half = 28; `S = {28}` sums to 28. -/
theorem zumkeller_twentyeight : Zumkeller 28 := by
  refine ⟨{28}, ?_, ?_⟩
  · decide
  · decide

/-- Concrete witness: `30` is Zumkeller. Divisors `{1,2,3,5,6,10,15,30}`, σ = 72, half = 36;
`S = {30, 6}` sums to 36. -/
theorem zumkeller_thirty : Zumkeller 30 := by
  refine ⟨{30, 6}, ?_, ?_⟩
  · decide
  · decide

/-- OPEN (unproven conjecture-style marker, kept as a `def` per program discipline).

This records the genuinely open structural question about *odd* Zumkeller numbers: whether
every odd Zumkeller number is divisible by 3. The smallest known odd Zumkeller number is
`945 = 3^3 · 5 · 7`, and no odd Zumkeller number coprime to 3 is known — but this has not
been proved. This `def` is a proposition we deliberately do NOT prove here. -/
def OddZumkellerFrom3Structure : Prop :=
  ∀ n, Odd n → Zumkeller n → 3 ∣ n

end Brockian.ZumkellerNumbers
