/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 6 qubits: the (finite-dimensional) Hilbert space of complex
amplitudes indexed by bit strings `Fin 6 → Fin 2`. -/
abbrev Qubits6 : Type := EuclideanSpace ℂ (Fin 6 → Fin 2)

/-- The all-zeros bit string `|000000⟩`. -/
def allZeros : Fin 6 → Fin 2 := fun _ => 0

/-- The all-ones bit string `|111111⟩`. -/
def allOnes : Fin 6 → Fin 2 := fun _ => 1

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`. -/
noncomputable def ghz6 : Qubits6 :=
  WithLp.toLp 2 (fun b => if b = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
           else if b = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

lemma norm_amp_sq : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]

/-- The 6-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∀ b : Fin 6 → Fin 2,
      ‖ghz6.ofLp b‖ ^ 2 = (if b = allZeros then (1:ℝ)/2 else 0)
        + (if b = allOnes then (1:ℝ)/2 else 0) := by
    intro b
    by_cases h0 : b = allZeros
    · subst h0
      simp only [ghz6, WithLp.ofLp_toLp, if_neg allZeros_ne_allOnes]
      norm_num [norm_amp_sq]
    · by_cases h1 : b = allOnes
      · subst h1
        simp only [ghz6, WithLp.ofLp_toLp, if_neg h0]
        norm_num [norm_amp_sq]
      · simp [ghz6, h0, h1]
  simp only [hsum, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]
  norm_num

end QC

