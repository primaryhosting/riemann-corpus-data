/-
  Brockian/OppermannConjecture.lean — Oppermann's conjecture (OPEN, strictly stronger
  than Legendre's conjecture and than Bertrand's postulate). Concrete two-sided prime
  witnesses for `n = 2 … 10` are proven by `norm_num`; the conjecture itself is recorded
  as an UNPROVEN `def` — a statement, never asserted as a theorem. As a bonus, we prove
  that Oppermann's *upper* clause implies Legendre's conclusion, since the Oppermann upper
  window `(n², n²+n)` sits strictly inside the Legendre window `(n², (n+1)²)`.

  Oppermann's conjecture states: for every `n > 1` there is a prime `p` with
  `n(n−1) < p < n²` AND a prime `q` with `n² < q < n(n+1)`. It is OPEN. This module does
  NOT resolve it. It:
    - verifies the concrete instances `n = 2 … 10` with explicit prime witnesses on both
      sides of `n²`;
    - records `OppermannLower`, `OppermannUpper`, and `OppermannConjecture` as `def`s
      (statements), never asserting the universal one;
    - proves the bridge `OppermannUpper n → PrimeBetweenSquares n` (Oppermann ⇒ Legendre),
      since `(n², n²+n) ⊆ (n², (n+1)²)`.

  Never claims to resolve Oppermann (or Legendre); never states them as theorems.

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (see PORT-QUEUE.md)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.LegendreConjecture

namespace Brockian.OppermannConjecture

/-- A prime strictly between `n(n−1)` and `n²`. (ℕ subtraction; harmless for `n ≥ 1`.) -/
def OppermannLower (n : ℕ) : Prop := ∃ p : ℕ, n * (n - 1) < p ∧ p < n ^ 2 ∧ p.Prime

/-- A prime strictly between `n²` and `n(n+1)`. -/
def OppermannUpper (n : ℕ) : Prop := ∃ p : ℕ, n ^ 2 < p ∧ p < n * (n + 1) ∧ p.Prime

/-- **Oppermann's conjecture** (**OPEN**): for every `n ≥ 2` there is a prime in each of
the two windows `(n(n−1), n²)` and `(n², n(n+1))` flanking `n²`. This is strictly stronger
than Legendre's conjecture (which asks only for a prime in `(n², (n+1)²)`) and than
Bertrand's postulate. Recorded here as an UNPROVEN `def` — the statement is never asserted
as a theorem, and this module does not resolve it. -/
def OppermannConjecture : Prop := ∀ n : ℕ, 2 ≤ n → OppermannLower n ∧ OppermannUpper n

/-! ## (1) Concrete two-sided Oppermann witnesses for `n = 2 … 10`

Each instance exhibits an explicit prime below `n²` and an explicit prime above `n²`,
each strictly inside the corresponding Oppermann window, discharged by `norm_num`
(`Nat.Prime` is decidable). These are true, verified instances of the conjecture's
conclusion — not a proof of the (open) universal statement. -/

/-- `n = 2`: lower `(2, 4)` ∋ `3`; upper `(4, 6)` ∋ `5`. -/
theorem oppermann_2 : OppermannLower 2 ∧ OppermannUpper 2 :=
  ⟨⟨3, by norm_num, by norm_num, by norm_num⟩, ⟨5, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 3`: lower `(6, 9)` ∋ `7`; upper `(9, 12)` ∋ `11`. -/
theorem oppermann_3 : OppermannLower 3 ∧ OppermannUpper 3 :=
  ⟨⟨7, by norm_num, by norm_num, by norm_num⟩, ⟨11, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 4`: lower `(12, 16)` ∋ `13`; upper `(16, 20)` ∋ `17`. -/
theorem oppermann_4 : OppermannLower 4 ∧ OppermannUpper 4 :=
  ⟨⟨13, by norm_num, by norm_num, by norm_num⟩, ⟨17, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 5`: lower `(20, 25)` ∋ `23`; upper `(25, 30)` ∋ `29`. -/
theorem oppermann_5 : OppermannLower 5 ∧ OppermannUpper 5 :=
  ⟨⟨23, by norm_num, by norm_num, by norm_num⟩, ⟨29, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 6`: lower `(30, 36)` ∋ `31`; upper `(36, 42)` ∋ `37`. -/
theorem oppermann_6 : OppermannLower 6 ∧ OppermannUpper 6 :=
  ⟨⟨31, by norm_num, by norm_num, by norm_num⟩, ⟨37, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 7`: lower `(42, 49)` ∋ `43`; upper `(49, 56)` ∋ `53`. -/
theorem oppermann_7 : OppermannLower 7 ∧ OppermannUpper 7 :=
  ⟨⟨43, by norm_num, by norm_num, by norm_num⟩, ⟨53, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 8`: lower `(56, 64)` ∋ `59`; upper `(64, 72)` ∋ `67`. -/
theorem oppermann_8 : OppermannLower 8 ∧ OppermannUpper 8 :=
  ⟨⟨59, by norm_num, by norm_num, by norm_num⟩, ⟨67, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 9`: lower `(72, 81)` ∋ `73`; upper `(81, 90)` ∋ `83`. -/
theorem oppermann_9 : OppermannLower 9 ∧ OppermannUpper 9 :=
  ⟨⟨73, by norm_num, by norm_num, by norm_num⟩, ⟨83, by norm_num, by norm_num, by norm_num⟩⟩

/-- `n = 10`: lower `(90, 100)` ∋ `97`; upper `(100, 110)` ∋ `101`. -/
theorem oppermann_10 : OppermannLower 10 ∧ OppermannUpper 10 :=
  ⟨⟨97, by norm_num, by norm_num, by norm_num⟩, ⟨101, by norm_num, by norm_num, by norm_num⟩⟩

/-! ## (2) Bridge: Oppermann strengthens Legendre

The Oppermann *upper* window `(n², n(n+1)) = (n², n²+n)` is strictly contained in the
Legendre window `(n², (n+1)²) = (n², n²+2n+1)`, because `n(n+1) < (n+1)²`. Hence any prime
witnessing `OppermannUpper n` also witnesses Legendre's `PrimeBetweenSquares n`. This shows
Oppermann ⇒ Legendre pointwise; it does NOT resolve either conjecture. -/

/-- **Oppermann's upper clause implies Legendre's conclusion.** From a prime `p` with
`n² < p < n(n+1)`, since `n(n+1) ≤ (n+1)²`, we get `n² < p < (n+1)²`, i.e.
`Brockian.LegendreConjecture.PrimeBetweenSquares n`. -/
theorem oppermannUpper_imp_legendre {n : ℕ} (hn : 1 ≤ n) (h : OppermannUpper n) :
    Brockian.LegendreConjecture.PrimeBetweenSquares n := by
  obtain ⟨p, hlo, hhi, hp⟩ := h
  refine ⟨p, hlo, ?_, hp⟩
  calc p < n * (n + 1) := hhi
    _ ≤ (n + 1) ^ 2 := by nlinarith

end Brockian.OppermannConjecture
