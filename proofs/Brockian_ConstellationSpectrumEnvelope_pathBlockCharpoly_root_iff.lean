import Mathlib
import Brockian.ConstellationSpectrum

/-
# Constellation sieve spectrum: the multiplicity-aware envelope

This module records the exact logical handoff needed after the graph Hamiltonian is reindexed into
`P1`, `P2`, and `P3` blocks. Arbitrary nonnegative block multiplicities give spectral containment in
the five-point alphabet. Equality with the entire alphabet additionally requires positive `P2` and
`P3` multiplicities; without that condition the reverse implication is false.
-/

namespace Brockian.ConstellationSpectrumEnvelope

open Polynomial
open Brockian.ConstellationSpectrum

/-- The characteristic polynomial prescribed by `n1` copies of `H1`, `n2` copies of `H2`, and
`n3` copies of `H3`. -/
noncomputable def pathBlockCharpoly (n1 n2 n3 : Nat) : Polynomial Real :=
  (X - C 2) ^ n1 *
    ((X - C 1) * (X - C 3)) ^ n2 *
      ((X - C 2) * (X ^ 2 - C 4 * X + C 2)) ^ n3

/-- Every root of a `P1/P2/P3` block-product characteristic polynomial belongs to the universal
five-point spectral envelope. No positivity assumption on the block multiplicities is needed. -/
theorem pathBlockCharpoly_root_mem (n1 n2 n3 : Nat) (x : Real)
    (hx : (pathBlockCharpoly n1 n2 n3).eval x = 0) :
    x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set Real) := by
  simp only [pathBlockCharpoly, eval_mul, eval_pow] at hx
  rcases mul_eq_zero.mp hx with hx | hx
  · rcases mul_eq_zero.mp hx with hx | hx
    · have hbase : eval x (X - C (2 : Real)) = 0 := eq_zero_of_pow_eq_zero hx
      have hroot : H1.charpoly.eval x = 0 := by
        rw [H1_charpoly]
        exact hbase
      have : x = 2 := (H1_eigenvalue x).mp hroot
      simp [this]
    · have hbase : eval x (X - C (1 : Real)) * eval x (X - C 3) = 0 :=
        eq_zero_of_pow_eq_zero hx
      have hroot : H2.charpoly.eval x = 0 := by
        rw [H2_charpoly]
        simpa only [eval_mul] using hbase
      rcases (H2_eigenvalues x).mp hroot with rfl | rfl <;> simp
  · have hbase : eval x (X - C (2 : Real)) * eval x (X ^ 2 - C 4 * X + C 2) = 0 :=
      eq_zero_of_pow_eq_zero hx
    have hroot : H3.charpoly.eval x = 0 := by
      rw [H3_charpoly]
      simpa only [eval_mul] using hbase
    rcases (H3_eigenvalues x).mp hroot with rfl | rfl | rfl <;> simp

/-- Positive `P2` and `P3` multiplicities are sufficient for the block-product spectrum to equal
the full five-point alphabet. A separate positive `P1` multiplicity is unnecessary because `H3`
already contributes the eigenvalue `2`. -/
theorem pathBlockCharpoly_root_iff (n1 n2 n3 : Nat) (hn2 : 0 < n2) (hn3 : 0 < n3) (x : Real) :
    (pathBlockCharpoly n1 n2 n3).eval x = 0 ↔
      x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set Real) := by
  constructor
  · exact pathBlockCharpoly_root_mem n1 n2 n3 x
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [pathBlockCharpoly, eval_mul, eval_pow]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff (Nat.ne_of_gt hn3)).mpr
      have hroot := (H3_eigenvalues (2 - Real.sqrt 2)).mpr (Or.inr (Or.inl rfl))
      simpa only [H3_charpoly, eval_mul] using hroot
    · apply mul_eq_zero.mpr
      left
      apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff (Nat.ne_of_gt hn2)).mpr
      have hroot := (H2_eigenvalues 1).mpr (Or.inl rfl)
      simpa only [H2_charpoly, eval_mul] using hroot
    · apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff (Nat.ne_of_gt hn3)).mpr
      have hroot := (H3_eigenvalues 2).mpr (Or.inl rfl)
      simpa only [H3_charpoly, eval_mul] using hroot
    · apply mul_eq_zero.mpr
      left
      apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff (Nat.ne_of_gt hn2)).mpr
      have hroot := (H2_eigenvalues 3).mpr (Or.inr rfl)
      simpa only [H2_charpoly, eval_mul] using hroot
    · apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff (Nat.ne_of_gt hn3)).mpr
      have hroot := (H3_eigenvalues (2 + Real.sqrt 2)).mpr (Or.inr (Or.inr rfl))
      simpa only [H3_charpoly, eval_mul] using hroot

/-- A single `P3` block does not have eigenvalue `1`. This is the concrete boundary witness showing
that five-point equality cannot be claimed for arbitrary zero block multiplicities. -/
theorem H3_only_not_root_one : (pathBlockCharpoly 0 0 1).eval 1 ≠ 0 := by
  norm_num [pathBlockCharpoly]

end Brockian.ConstellationSpectrumEnvelope
