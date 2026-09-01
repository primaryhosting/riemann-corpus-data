/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- A two-qubit state: an amplitude for each computational basis vector `|x y⟩`. -/
abbrev State := Bool × Bool → ℂ

/-- Matrix entries of the Hadamard gate: `H a b = (-1)^(a*b) / √2`. -/
noncomputable def had (a b : Bool) : ℂ :=
  if a && b then -((Real.sqrt 2)⁻¹ : ℝ) else ((Real.sqrt 2)⁻¹ : ℝ)

/-- Apply a Hadamard gate to both qubits. -/
noncomputable def hadBoth (psi : State) : State :=
  fun p => ∑ u : Bool, ∑ v : Bool, had p.1 u * had p.2 v * psi (u, v)

/-- Apply a Hadamard gate to the first qubit only. -/
noncomputable def hadFirst (psi : State) : State :=
  fun p => ∑ u : Bool, had p.1 u * psi (u, p.2)

/-- The oracle `U_f |x, y⟩ = |x, y ⊕ f x⟩` (acting on amplitudes). -/
def oracle (f : Bool → Bool) (psi : State) : State :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The initial state `|0⟩|1⟩`. -/
def init : State := fun p => if p = (false, true) then 1 else 0

/-- The state produced by Deutsch's algorithm: `(H ⊗ I) U_f (H ⊗ H)` applied to `|0,1⟩`. -/
noncomputable def deutschState (f : Bool → Bool) : State :=
  hadFirst (oracle f (hadBoth init))

/-- Probability that measuring the first qubit of the final state yields `b`. -/
noncomputable def prob (f : Bool → Bool) (b : Bool) : ℝ :=
  ∑ y : Bool, ‖deutschState f (b, y)‖ ^ 2

private lemma sqrt_two_pow_six : (Real.sqrt 2) ^ 6 = 8 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
    _ = 8 := by rw [h2]; norm_num

/-- **Deutsch's algorithm is correct.**  With a single query to the oracle `U_f`, the
circuit `(H ⊗ I) U_f (H ⊗ H)` applied to `|0,1⟩` yields a first qubit which measures
to `0` with certainty exactly when `f` is constant, and to `1` with certainty exactly
when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    (f false = f true → prob f false = 1 ∧ prob f true = 0) ∧
    (f false ≠ f true → prob f false = 0 ∧ prob f true = 1) := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h6 := sqrt_two_pow_six
  constructor <;> intro hf <;> constructor <;>
    · simp only [prob, deutschState, hadFirst, oracle, hadBoth, init, had, Fintype.sum_bool]
      cases h0 : f false <;> cases h1 : f true <;>
        simp_all [-Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_add,
          ← Complex.ofReal_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs] <;>
        field_simp <;> linarith [h6]

end QC
#print axioms QC.deutsch_correct

