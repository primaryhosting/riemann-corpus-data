/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace QC

/-- Computational basis states of 8 qubits, indexed by bit strings `Fin 8 → Fin 2`. -/
abbrev Qubits8 := Fin 8 → Fin 2

/-- The all-zeros bit string `|0…0⟩`. -/
def zeros8 : Qubits8 := fun _ => 0

/-- The all-ones bit string `|1…1⟩`. -/
def ones8 : Qubits8 := fun _ => 1

theorem zeros8_ne_ones8 : zeros8 ≠ ones8 := by
  intro h
  have := congrFun h ⟨0, by norm_num⟩
  simp [zeros8, ones8] at this

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the
256-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 8 → Fin 2)`. -/
noncomputable def ghz8 : EuclideanSpace ℂ Qubits8 :=
  WithLp.toLp 2 (fun s => if s = zeros8 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if s = ones8 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 8-qubit GHZ state is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  have hsum : ∑ s : Qubits8, ‖ghz8.ofLp s‖ ^ 2 = 1 := by
    have hpt : ∀ s : Qubits8, ‖ghz8.ofLp s‖ ^ 2
        = (if s = zeros8 then (1 / 2 : ℝ) else 0)
          + (if s = ones8 then (1 / 2 : ℝ) else 0) := by
      intro s
      by_cases h0 : s = zeros8
      · simp [ghz8, h0, zeros8_ne_ones8]
      · by_cases h1 : s = ones8
        · simp [ghz8, h1, zeros8_ne_ones8.symm]
        · simp [ghz8, h0, h1]
    rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ zeros8 (fun _ => (1 / 2 : ℝ)),
      Finset.sum_ite_eq' Finset.univ ones8 (fun _ => (1 / 2 : ℝ))]
    norm_num
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]

end QC

