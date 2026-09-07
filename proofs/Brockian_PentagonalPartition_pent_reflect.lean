/-
  Brockian/PentagonalPartition.lean — GENERALIZED PENTAGONAL NUMBERS
  and the Euler pentagonal ↔ partition bridge (Aug 1).

  The headline question "what connects Euler's pentagonal number theorem to
  Ramanujan's partitions" is the pentagonal number theorem:

        ∏_{n≥1} (1 − xⁿ)  =  ∑_{k∈ℤ} (−1)ᵏ x^{k(3k−1)/2},

  equivalently the partition recurrence
        p(n) = ∑_{k≠0} (−1)^{k−1} p(n − g_k),   g_k = k(3k−1)/2.

  This module formalizes the ARITHMETIC SPINE that both sides share: the
  generalized pentagonal number function g_k = k(3k−1)/2 as a total ℤ→ℤ map,
  proved well-defined (the numerator is always even), together with its
  structural laws — the doubling identity, nonnegativity, the reflection
  g_{−k} = g_k + k, the successor recurrence, strict growth, and (a genuinely
  non-trivial fact) global INJECTIVITY of g over ℤ, which is exactly what makes
  the exponents 0,1,2,5,7,12,15,… on the right-hand side pairwise distinct.

  The one honest tie to real partitions available at Mathlib 4.32 is the base
  count p(0) = 1, discharged against Mathlib's own `Nat.Partition`.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `pent`                — g_k = k(3k−1)/2 as a function ℤ → ℤ.
  * `two_dvd_pentNum`     — 2 ∣ k(3k−1): the numerator is always even, so the
                            division defining `pent` is exact (no ℤ-div collapse).
  * `two_mul_pent`        — 2 · g_k = k(3k−1): the exact doubling identity.
  * `two_mul_pent_expand` — 2 · g_k = 3k² − k.
  * `pent_nonneg`         — 0 ≤ g_k for every integer k.
  * `pent_reflect`        — g_{−k} = g_k + k  (pairs the two arms k, −k).
  * `pent_succ`           — g_{k+1} = g_k + (3k+1)  (the classic step recurrence).
  * `pent_lt_succ`        — g_k < g_{k+1} for k ≥ 0  (strict growth on the arm).
  * `pent_injective`      — g is injective on ℤ ⇒ the PST exponents are distinct.
  * `partition_zero_card` — Fintype.card (Nat.Partition 0) = 1, i.e. p(0) = 1,
                            anchored on Mathlib's `Nat.Partition`.

  ## COMPUTATION  (values discharged via the doubling identity, PROVED, not by
      trusting a kernel oracle — listed here because they are concrete instances)
  * `pent_values`         — g at k = 0,1,−1,2,−2,3,−3 equals 0,1,2,5,7,12,15,
                            the first generalized pentagonal numbers in order.

  ## What is NOT proved  (precise obstructions at Mathlib 4.32)
  * The pentagonal number theorem itself (the ∏(1−xⁿ) = ∑(−1)ᵏx^{g_k} identity,
    Franklin's involution) — Mathlib has `Nat.Partition` and Euler's
    odd = distinct theorem, but NOT the pentagonal number theorem nor the
    generating-function product ∏(1−xⁿ); a from-scratch Franklin involution is
    out of scope here.
  * The partition recurrence p(n) = ∑_{k≠0}(−1)^{k−1} p(n−g_k) — it is
    equivalent to the theorem above, so equally out of reach.
  * Partition counts p(n) for n ≥ 1 by evaluation — `Fintype.card (Nat.Partition n)`
    does NOT reduce under `decide` at Mathlib 4.32 (its `Fintype` instance is built
    through non-reducing `Multiset`/`Finset` machinery). Only p(0)=1 is reachable
    cheaply (via the `Unique (Nat.Partition 0)` instance).

  ## Relation to the C₅ spectral work in this repo
  NONE that is rigorous. Pentagonal numbers and the C₅/D₅ spectral modules share
  only the informal "five / pentagon" motif (a pentagon has 5 sides; nested
  pentagons count pentagonal numbers). There is no theorem here linking g_k to
  the cyclic-group Laplacian spectrum, and none is claimed.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.PentagonalPartition

/-- The generalized pentagonal number `g_k = k(3k−1)/2`, as a total map `ℤ → ℤ`.
Ordinary pentagonal numbers are the values at `k = 1, 2, 3, …`; the values at
`k = 0, ±1, ±2, …` enumerate the exponents in Euler's pentagonal number theorem. -/
def pent (k : ℤ) : ℤ := k * (3 * k - 1) / 2

/-- The numerator `k(3k−1)` is always even, so `pent` divides exactly (no ℤ-division
collapse). This is the well-definedness fact behind the `/2`. -/
theorem two_dvd_pentNum (k : ℤ) : 2 ∣ k * (3 * k - 1) := by
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- k = m + m
    exact ⟨m * (3 * (m + m) - 1), by rw [hm]; ring⟩
  · -- k = 2m + 1
    exact ⟨(2 * m + 1) * (3 * m + 1), by rw [hm]; ring⟩

/-- The exact doubling identity `2 · g_k = k(3k−1)`. Every structural fact below is
derived from this, so nothing depends on how `ediv` rounds. -/
theorem two_mul_pent (k : ℤ) : 2 * pent k = k * (3 * k - 1) :=
  Int.mul_ediv_cancel' (two_dvd_pentNum k)

/-- Expanded doubling identity `2 · g_k = 3k² − k`. -/
theorem two_mul_pent_expand (k : ℤ) : 2 * pent k = 3 * k ^ 2 - k := by
  rw [two_mul_pent]; ring

/-- Generalized pentagonal numbers are nonnegative: `0 ≤ g_k` for all `k ∈ ℤ`. -/
theorem pent_nonneg (k : ℤ) : 0 ≤ pent k := by
  have h : 2 * pent k = k * (3 * k - 1) := two_mul_pent k
  have hk : 0 ≤ k * (3 * k - 1) := by nlinarith [sq_nonneg k, sq_nonneg (k - 1)]
  nlinarith [h, hk]

/-- Reflection law `g_{−k} = g_k + k`: this is exactly why the two arms `k` and
`−k` of the pentagonal sum land on adjacent exponents (e.g. `g_2 = 5`, `g_{−2} = 7`). -/
theorem pent_reflect (k : ℤ) : pent (-k) = pent k + k := by
  have h1 : 2 * pent (-k) = (-k) * (3 * (-k) - 1) := two_mul_pent (-k)
  have h2 : 2 * pent k = k * (3 * k - 1) := two_mul_pent k
  nlinarith [h1, h2]

/-- Successor recurrence `g_{k+1} = g_k + (3k+1)`: the classic step law for
pentagonal numbers (`1 → 5 → 12 → 22 → …` on the positive arm). -/
theorem pent_succ (k : ℤ) : pent (k + 1) = pent k + (3 * k + 1) := by
  have h1 : 2 * pent (k + 1) = (k + 1) * (3 * (k + 1) - 1) := two_mul_pent (k + 1)
  have h2 : 2 * pent k = k * (3 * k - 1) := two_mul_pent k
  nlinarith [h1, h2]

/-- Strict growth on the nonnegative arm: `g_k < g_{k+1}` whenever `0 ≤ k`. -/
theorem pent_lt_succ {k : ℤ} (hk : 0 ≤ k) : pent k < pent (k + 1) := by
  rw [pent_succ]; linarith

/-- **Injectivity of `g` over `ℤ`.** Distinct integers give distinct generalized
pentagonal numbers; equivalently the exponents `0,1,2,5,7,12,15,…` on the
right-hand side of the pentagonal number theorem are pairwise distinct. -/
theorem pent_injective : Function.Injective pent := by
  intro a b h
  have ha : 2 * pent a = a * (3 * a - 1) := two_mul_pent a
  have hb : 2 * pent b = b * (3 * b - 1) := two_mul_pent b
  -- From `pent a = pent b` we get `(a − b)·(3(a+b) − 1) = 0`.
  have key : (a - b) * (3 * (a + b) - 1) = 0 := by nlinarith [ha, hb, h]
  rcases mul_eq_zero.mp key with hab | hodd
  · exact sub_eq_zero.mp hab
  · -- `3(a+b) − 1 = 0` has no integer solution.
    omega

/-- The first generalized pentagonal numbers, in the classic PST order
`k = 0, 1, −1, 2, −2, 3, −3`, are `0, 1, 2, 5, 7, 12, 15` — the exponents of
`∏(1−xⁿ) = 1 − x − x² + x⁵ + x⁷ − x¹² − x¹⁵ + …`. Each value is PROVED from the
doubling identity (not asserted). -/
theorem pent_values :
    pent 0 = 0 ∧ pent 1 = 1 ∧ pent (-1) = 2 ∧ pent 2 = 5 ∧
      pent (-2) = 7 ∧ pent 3 = 12 ∧ pent (-3) = 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · first
      | (have h := two_mul_pent 0; omega)
      | (have h := two_mul_pent 1; omega)
      | (have h := two_mul_pent (-1); omega)
      | (have h := two_mul_pent 2; omega)
      | (have h := two_mul_pent (-2); omega)
      | (have h := two_mul_pent 3; omega)
      | (have h := two_mul_pent (-3); omega)

/-- Partition base count `p(0) = 1`, discharged against Mathlib's own
`Nat.Partition`: the empty partition is the unique partition of `0`. This is the
one honest contact point with real partition theory available at Mathlib 4.32. -/
theorem partition_zero_card : Fintype.card (Nat.Partition 0) = 1 := by
  rw [Fintype.card_eq_one_iff_nonempty_unique]
  exact ⟨inferInstance⟩

end Brockian.PentagonalPartition
