import Mathlib
-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the requested header comment follows the import.)

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped ComplexConjugate InnerProductSpace

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- The quantum-mechanical expectation value `⟨Op⟩ = ⟪ψ, Op ψ⟫` of an operator `Op`
in the (normalized) state `ψ`. -/
noncomputable def expectation (ψ : 𝓗) (Op : 𝓗 →ₗ[ℂ] 𝓗) : ℂ := ⟪ψ, Op ψ⟫_ℂ

/-- For a stationary state `ψ` (an eigenvector of the symmetric Hamiltonian `H` with real
energy `E`), the expectation value of any commutator `[H, A]` vanishes. -/
theorem inner_commutator_eq_zero_of_eigenvector
    {H A : 𝓗 →ₗ[ℂ] 𝓗} {ψ : 𝓗} {E : ℝ}
    (hsym : ∀ x y : 𝓗, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (heig : H ψ = (E : ℂ) • ψ) :
    ⟪ψ, H (A ψ) - A (H ψ)⟫_ℂ = 0 := by
  rw [inner_sub_right, ← hsym ψ (A ψ), heig, map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.conj_ofReal]

/-- **Quantum virial theorem.**

Let `H = T + V` be a symmetric Hamiltonian on a complex inner product space, let `A` be the
generator of dilations (`A = r · p`), and let `W` be the operator `r · ∇V`.  The canonical
commutation relations give the operator identity `[H, A] = i (2T - r·∇V)` (hypothesis `hcomm`,
needed only at the state `ψ`).  Then for a bound stationary state `ψ`, i.e. a normalized
eigenvector of `H` with real energy `E`, one has

`2 ⟨T⟩ = ⟨r · ∇V⟩`.

The normalization hypothesis `hnorm` records that `ψ` is a bound (normalizable) state, as in the
physical statement; the algebraic identity itself does not need it. -/
theorem virial_theorem
    {H A T W : 𝓗 →ₗ[ℂ] 𝓗} {ψ : 𝓗} {E : ℝ}
    (hnorm : ‖ψ‖ = 1)
    (hsym : ∀ x y : 𝓗, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (heig : H ψ = (E : ℂ) • ψ)
    (hcomm : H (A ψ) - A (H ψ) = Complex.I • (2 • T ψ - W ψ)) :
    2 * expectation ψ T = expectation ψ W := by
  have h0 : ⟪ψ, H (A ψ) - A (H ψ)⟫_ℂ = 0 :=
    inner_commutator_eq_zero_of_eigenvector hsym heig
  rw [hcomm, inner_smul_right, inner_sub_right] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h Complex.I_ne_zero
  · have h2 : (2 : ℂ) * ⟪ψ, T ψ⟫_ℂ - ⟪ψ, W ψ⟫_ℂ = 0 := by
      simpa [two_smul, inner_add_right, two_mul] using h
    simpa only [expectation] using sub_eq_zero.mp h2

end Phys

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

