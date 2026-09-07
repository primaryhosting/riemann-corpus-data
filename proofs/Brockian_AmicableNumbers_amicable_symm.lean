import Mathlib

/-!
# Amicable numbers and aliquot dynamics

The **aliquot sum** `s(n) = σ(n) − n` is the sum of the proper divisors of `n`.
Iterating `s` gives the *aliquot map*, whose orbits are the aliquot sequences.

* A **perfect number** is a fixed point of `s` (`s(n) = n`).
* An **amicable pair** is a 2-cycle of `s`: two distinct numbers `m ≠ n` with
  `s(m) = n` and `s(n) = m`.

Whether there are **infinitely many** amicable pairs is a long-standing OPEN problem.
This file proves specific pairs *are* amicable (concrete, kernel-verified instances),
records the elementary aliquot-dynamics framing (perfect = fixed point, amicable = a
symmetric 2-cycle that is never a fixed point), and records the infinitude question as an
unproven `def` — it is **not** claimed to be resolved here.
-/

namespace Brockian.AmicableNumbers

/-- Aliquot sum: sum of proper divisors, `σ(n) − n`. -/
def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- An amicable pair: each is the aliquot sum of the other, and they differ. -/
def Amicable (m n : ℕ) : Prop := m ≠ n ∧ aliquot m = n ∧ aliquot n = m

/-- OPEN: are there infinitely many amicable pairs? Recorded as an unproven `def`;
this file does **not** prove it. -/
def AmicableInfinitude : Prop := ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ Amicable m n

/-! ## Concrete verified amicable pairs -/

/-- FLAGSHIP — the classic amicable pair `(220, 284)` (Pythagoras / Thābit ibn Qurra):
`aliquot 220 = 284` and `aliquot 284 = 220`. -/
theorem amicable_220_284 : Amicable 220 284 :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 8000 in
/-- The amicable pair `(1184, 1210)` (Paganini, 1866).
`1184 = 2^5·37`, `1210 = 2·5·11²`. -/
theorem amicable_1184_1210 : Amicable 1184 1210 :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 8000 in
/-- The amicable pair `(2620, 2924)` (Euler).
`2620 = 2²·5·131`, `2924 = 2²·17·43`. -/
theorem amicable_2620_2924 : Amicable 2620 2924 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Aliquot dynamics framing -/

/-- A perfect number is exactly a fixed point of the aliquot map. -/
theorem perfect_iff_aliquot_fixed {n : ℕ} (hn : 0 < n) :
    Nat.Perfect n ↔ aliquot n = n :=
  Nat.perfect_iff_sum_properDivisors hn

/-- Amicability is symmetric: a 2-cycle `m → n → m` is also the 2-cycle `n → m → n`. -/
theorem amicable_symm {m n : ℕ} (h : Amicable m n) : Amicable n m :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- An amicable number is not perfect: a genuine 2-cycle is not a fixed point.
If `m` were perfect then `aliquot m = m`, but `aliquot m = n` with `m ≠ n`. -/
theorem amicable_not_perfect {m n : ℕ} (h : Amicable m n) : ¬ Nat.Perfect m := by
  rintro ⟨hsum, -⟩
  exact h.1 (hsum.symm.trans h.2.1)

end Brockian.AmicableNumbers
