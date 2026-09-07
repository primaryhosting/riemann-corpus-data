import Mathlib

/-!
# Gilbreath's Conjecture — concrete verification on the prime difference-triangle

Gilbreath's conjecture (OPEN, 1958): write the sequence of primes `2, 3, 5, 7, 11, …`,
then repeatedly form the row of absolute differences of adjacent terms. The first
element of every such difference row (row `k ≥ 1`) is `1`.

This file does two things, kept scrupulously honest:

* It **proves**, by finite kernel computation, that the leading entry of Gilbreath rows
  `1 … 10` over the first 25 primes is `1`. These are concrete arithmetic facts about a
  fixed finite list — not the conjecture.
* It **records** the open conjecture as an unproven `def GilbreathConjecture : Prop`.
  This is an *open marker only*: it is never proved and never asserted. Nothing in this
  file, and nothing downstream, may take it as an axiom or hypothesis-free theorem.

No `sorry`, no `admit`, no `native_decide`, no added axioms.
-/

namespace Brockian.GilbreathConjecture

/-- Adjacent absolute differences of a list (`Nat.dist` between consecutive entries). -/
def adjDiff : List ℕ → List ℕ
  | []        => []
  | [_]       => []
  | a :: b :: t => Nat.dist a b :: adjDiff (b :: t)

/-- The `k`-th Gilbreath row obtained by iterating `adjDiff` `k` times from a start list. -/
def gilbreathRow (start : List ℕ) (k : ℕ) : List ℕ := adjDiff^[k] start

/-- The first 25 primes (initial segment for the concrete checks). -/
def primes25 : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

/--
Gilbreath's conjecture (OPEN — unproven marker, never asserted).

Formulated over the abstract prime enumeration `Nat.nth Nat.Prime`: for every finite
initial segment of length `N` of the primes, every difference row `k` with `1 ≤ k < N`
has leading entry `1`. The finite theorems below are instances of this statement for the
particular segment `primes25`; the statement as a whole is an open problem and is
deliberately left as an unproven `def`.
-/
def GilbreathConjecture : Prop :=
  ∀ N : ℕ, ∀ k : ℕ, 1 ≤ k → k < N →
    (adjDiff^[k] (List.map (fun i => Nat.nth Nat.Prime i) (List.range N))).headI = 1

/-! ## Flagship: leading entry is `1` for Gilbreath rows 1 … 10 over `primes25`. -/

theorem gilbreath_row1_head  : (gilbreathRow primes25 1).headI = 1 := by
  rfl
theorem gilbreath_row2_head  : (gilbreathRow primes25 2).headI = 1 := by
  rfl
theorem gilbreath_row3_head  : (gilbreathRow primes25 3).headI = 1 := by
  rfl
theorem gilbreath_row4_head  : (gilbreathRow primes25 4).headI = 1 := by
  rfl
theorem gilbreath_row5_head  : (gilbreathRow primes25 5).headI = 1 := by
  rfl
theorem gilbreath_row6_head  : (gilbreathRow primes25 6).headI = 1 := by
  rfl
theorem gilbreath_row7_head  : (gilbreathRow primes25 7).headI = 1 := by
  rfl
theorem gilbreath_row8_head  : (gilbreathRow primes25 8).headI = 1 := by
  rfl
theorem gilbreath_row9_head  : (gilbreathRow primes25 9).headI = 1 := by
  rfl
theorem gilbreath_row10_head : (gilbreathRow primes25 10).headI = 1 := by
  rfl

/-! ## Illustrative: the first difference row shown explicitly. -/

theorem gilbreath_row1_eq :
    gilbreathRow primes25 1
      = [1,2,2,4,2,4,2,4,6,2,6,4,2,4,6,6,2,6,4,2,6,4,6,8] := by
  rfl

/-- Sanity: the head equalities also hold in the `Option` form via `List.head?`. -/
theorem gilbreath_row1_head?  : (gilbreathRow primes25 1).head? = some 1 := by
  rfl

end Brockian.GilbreathConjecture
