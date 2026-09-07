/-
  Brockian/LegendreConjecture.lean — Legendre's conjecture (Landau's third problem,
  OPEN): a prime strictly between every pair of consecutive squares. Concrete witnesses
  for `n = 1 … 12` are proven by `norm_num`; the conjecture itself is recorded as an
  UNPROVEN `def` — a statement, never asserted as a theorem. As a bonus, the proven
  weaker cousin — **Bertrand's postulate** (a theorem in Mathlib) — is re-exported and
  contrasted with Legendre in the docstrings.

  Legendre's conjecture states: for every `n ≥ 1` there is a prime `p` with
  `n² < p < (n+1)²`. It is OPEN. This module does NOT resolve it. It:
    - verifies the concrete instances `n = 1 … 12` with explicit prime witnesses;
    - records `PrimeBetweenSquares` and `LegendreConjecture` as `def`s (statements);
    - re-exports Bertrand's postulate `∃ p prime, n < p ≤ 2n` from Mathlib and notes
      that Legendre would strengthen the guaranteed gap from `(n, 2n]` to `(n², (n+1)²)`.

  Never claims to resolve Legendre; never states Bertrand as open (it is a theorem).

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (see PORT-QUEUE.md)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.LegendreConjecture

/-- There is a prime strictly between `n²` and `(n+1)²`. -/
def PrimeBetweenSquares (n : ℕ) : Prop := ∃ p : ℕ, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime

/-- **Legendre's conjecture** (Landau's third problem, **OPEN**): there is a prime
strictly between every pair of consecutive squares — for every `n ≥ 1` some prime `p`
satisfies `n² < p < (n+1)²`. This is an UNPROVEN `def` recording the statement; it is
never asserted as a theorem here, and this module does not resolve it. -/
def LegendreConjecture : Prop := ∀ n : ℕ, 1 ≤ n → PrimeBetweenSquares n

/-! ## (1) Concrete prime-between-squares witnesses for `n = 1 … 12`

Each instance exhibits an explicit prime `p` with `n² < p < (n+1)²`, discharged by
`norm_num` (`Nat.Prime` is decidable). These are true, verified instances of the
conjecture's conclusion — not a proof of the (open) universal statement. -/

/-- `n = 1`: `1 < 2 < 4`. -/
theorem legendre_1 : PrimeBetweenSquares 1 := ⟨2, by norm_num, by norm_num, by norm_num⟩

/-- `n = 2`: `4 < 5 < 9`. -/
theorem legendre_2 : PrimeBetweenSquares 2 := ⟨5, by norm_num, by norm_num, by norm_num⟩

/-- `n = 3`: `9 < 11 < 16`. -/
theorem legendre_3 : PrimeBetweenSquares 3 := ⟨11, by norm_num, by norm_num, by norm_num⟩

/-- `n = 4`: `16 < 17 < 25`. -/
theorem legendre_4 : PrimeBetweenSquares 4 := ⟨17, by norm_num, by norm_num, by norm_num⟩

/-- `n = 5`: `25 < 29 < 36`. -/
theorem legendre_5 : PrimeBetweenSquares 5 := ⟨29, by norm_num, by norm_num, by norm_num⟩

/-- `n = 6`: `36 < 37 < 49`. -/
theorem legendre_6 : PrimeBetweenSquares 6 := ⟨37, by norm_num, by norm_num, by norm_num⟩

/-- `n = 7`: `49 < 53 < 64`. -/
theorem legendre_7 : PrimeBetweenSquares 7 := ⟨53, by norm_num, by norm_num, by norm_num⟩

/-- `n = 8`: `64 < 67 < 81`. -/
theorem legendre_8 : PrimeBetweenSquares 8 := ⟨67, by norm_num, by norm_num, by norm_num⟩

/-- `n = 9`: `81 < 83 < 100`. -/
theorem legendre_9 : PrimeBetweenSquares 9 := ⟨83, by norm_num, by norm_num, by norm_num⟩

/-- `n = 10`: `100 < 101 < 121`. -/
theorem legendre_10 : PrimeBetweenSquares 10 := ⟨101, by norm_num, by norm_num, by norm_num⟩

/-- `n = 11`: `121 < 127 < 144`. -/
theorem legendre_11 : PrimeBetweenSquares 11 := ⟨127, by norm_num, by norm_num, by norm_num⟩

/-- `n = 12`: `144 < 149 < 169`. -/
theorem legendre_12 : PrimeBetweenSquares 12 := ⟨149, by norm_num, by norm_num, by norm_num⟩

/-! ## (2) The proven weaker cousin: Bertrand's postulate

Bertrand's postulate — for every `n ≠ 0` there is a prime `p` with `n < p ≤ 2n` — is a
**theorem** in Mathlib (`Nat.exists_prime_lt_and_le_two_mul`). It is re-exported here to
contrast with Legendre: Bertrand guarantees a prime in the multiplicative window
`(n, 2n]`, whereas Legendre (OPEN) would guarantee a prime in the far narrower window
`(n², (n+1)²)`, i.e. within a gap of only `2n + 1` around `n²`. Legendre would strengthen
Bertrand's gap from `(n, 2n]` to `(n², (n+1)²)`; it does not follow from Bertrand and
remains unproven. -/

/-- **Bertrand's postulate** (proven, via Mathlib): for every `n ≠ 0` there is a prime
`p` with `n < p ≤ 2n`. Direct re-export of `Nat.exists_prime_lt_and_le_two_mul`. This is
the weaker, *proven* cousin of the open Legendre conjecture. -/
theorem bertrand_holds {n : ℕ} (hn : n ≠ 0) : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n hn

end Brockian.LegendreConjecture
