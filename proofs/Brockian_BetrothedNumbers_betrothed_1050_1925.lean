import Mathlib

/-!
# Betrothed (quasi-amicable) numbers

The **aliquot sum** `s(n) = ∑ d ∈ n.properDivisors, d` is the sum of the proper divisors
of `n`. A **betrothed** (or **quasi-amicable**) pair `(m, n)` is a pair of distinct
numbers each of which is *one more* than the aliquot sum of the other:
`s(m) = n + 1` and `s(n) = m + 1`. Betrothed pairs are the "off-by-one" analogue of
amicable pairs (where `s(m) = n`, `s(n) = m`).

* The smallest betrothed pair is `(48, 75)`: `s(48) = 76 = 75 + 1`, `s(75) = 49 = 48 + 1`.
* The next is `(140, 195)`; then `(1050, 1925)`, `(1575, 1648)`, ....

Two long-standing questions are **OPEN**:

* whether there are **infinitely many** betrothed pairs;
* whether any betrothed pair has **both members of the same parity** — every known
  betrothed pair consists of one even and one odd number.

This file proves specific pairs *are* betrothed (concrete, kernel-verified instances),
records the elementary structure (betrothed is symmetric, its members are distinct), notes
that the two known small pairs have opposite parity, and records the two open questions as
unproven `def`s. Neither open question is claimed to be resolved here.
-/

namespace Brockian.BetrothedNumbers

/-- Aliquot sum: sum of proper divisors. -/
def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `(m, n)` is a betrothed / quasi-amicable pair: `s(m) = n + 1` and `s(n) = m + 1`,
with `m ≠ n`. -/
def Betrothed (m n : ℕ) : Prop := m ≠ n ∧ aliquot m = n + 1 ∧ aliquot n = m + 1

/-- OPEN: are there infinitely many betrothed pairs? Recorded as an unproven `def`;
this file does **not** prove it. -/
def BetrothedInfinitude : Prop := ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ Betrothed m n

/-- OPEN: does a betrothed pair with both members of the same parity exist? Every known
betrothed pair has opposite parity. Recorded as an unproven `def`; this file does **not**
resolve it (in either direction). -/
def SameParityBetrothedExists : Prop := ∃ m n : ℕ, Betrothed m n ∧ (Even m ↔ Even n)

/-! ## Concrete verified betrothed pairs -/

/-- FLAGSHIP — the smallest betrothed pair `(48, 75)`:
`aliquot 48 = 76 = 75 + 1` and `aliquot 75 = 49 = 48 + 1`. -/
theorem betrothed_48_75 : Betrothed 48 75 :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 8000 in
/-- The betrothed pair `(140, 195)`:
`aliquot 140 = 196 = 195 + 1` and `aliquot 195 = 141 = 140 + 1`. -/
theorem betrothed_140_195 : Betrothed 140 195 :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- The betrothed pair `(1050, 1925)`:
`aliquot 1050 = 1926 = 1925 + 1` and `aliquot 1925 = 1051 = 1050 + 1`. -/
theorem betrothed_1050_1925 : Betrothed 1050 1925 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Structural facts -/

/-- Betrothed is symmetric: reorder the defining conjunction. -/
theorem betrothed_symm {m n : ℕ} (h : Betrothed m n) : Betrothed n m :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- The members of a betrothed pair are distinct. -/
theorem betrothed_ne {m n : ℕ} (h : Betrothed m n) : m ≠ n :=
  h.1

/-! ## Parity of the known small pairs

The two smallest betrothed pairs each consist of one even and one odd member. This
illustrates the empirical "all known betrothed pairs have opposite parity" observation —
it does **not** assert the open `SameParityBetrothedExists` question in either direction. -/

/-- `(48, 75)` has opposite parity: `48` is even, `75` is odd. -/
theorem betrothed_48_75_opposite_parity : Even 48 ∧ Odd 75 := by decide

/-- `(140, 195)` has opposite parity: `140` is even, `195` is odd. -/
theorem betrothed_140_195_opposite_parity : Even 140 ∧ Odd 195 := by decide

end Brockian.BetrothedNumbers
