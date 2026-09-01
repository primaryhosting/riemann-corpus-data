import Mathlib
namespace BrockianFrontier.Gilbreath

/-- Absolute successive differences of a list. -/
def adj : List ℕ → List ℕ
  | a :: b :: t => Nat.dist a b :: adj (b :: t)
  | _ => []

/-- The first 25 primes. -/
def primes25 : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

/-- The k-th Gilbreath difference row. -/
def row (k : ℕ) : List ℕ := adj^[k] primes25

/-- Gilbreath's conjecture continues to hold through rows 9–16 for the first 25 primes:
    every such row begins with 1. (Rows 1–8 are already verified upstream.) -/
theorem gilbreath_rows_9_16 :
    (row 9).headI = 1 ∧ (row 10).headI = 1 ∧ (row 11).headI = 1 ∧ (row 12).headI = 1 ∧
    (row 13).headI = 1 ∧ (row 14).headI = 1 ∧ (row 15).headI = 1 ∧ (row 16).headI = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end BrockianFrontier.Gilbreath

