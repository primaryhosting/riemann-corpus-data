/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- **Berry phase quantization (base case).**

A one-parameter family of normalized states `t ↦ exp (I * θ t)` is transported around a
closed loop, parametrized by `t ∈ [0,1]`.  The *Berry connection* is the real function `A`
with `A t = θ' t`, and the *Berry phase* accumulated around the loop is the integral of the
connection, `∫ t in 0..1, A t`.

If the state is single-valued around the loop (`exp (I * θ 1) = exp (I * θ 0)`), then the
Berry phase is quantized: it is an integer multiple of `2π`. -/
theorem berry_phase_quantized
    (θ A : ℝ → ℝ)
    (hθ : ∀ t, HasDerivAt θ (A t) t)
    (hA : IntervalIntegrable A MeasureTheory.volume 0 1)
    (hloop : Complex.exp (Complex.I * θ 1) = Complex.exp (Complex.I * θ 0)) :
    ∃ n : ℤ, (∫ t in (0:ℝ)..1, A t) = 2 * Real.pi * n := by
  have hint : (∫ t in (0:ℝ)..1, A t) = θ 1 - θ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hθ t) hA
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hloop
  refine ⟨n, ?_⟩
  rw [hint]
  have hI : Complex.I * ((θ 1 : ℂ) - (θ 0 : ℂ) - 2 * Real.pi * n) = 0 := by
    linear_combination hn
  have : (θ 1 : ℂ) - (θ 0 : ℂ) - 2 * Real.pi * n = 0 := by
    rcases mul_eq_zero.mp hI with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  have hreal : ((θ 1 - θ 0 : ℝ) : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
    push_cast
    linear_combination this
  exact_mod_cast hreal

end Frontier

import Mathlib

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

