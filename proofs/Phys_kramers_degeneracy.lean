/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Key lemma (Kramers orthogonality).**  If `T` is antiunitary, i.e.
`⟪T x, T y⟫ = ⟪y, x⟫` for all `x y`, and squares to `-1` (the half-integer-spin case),
then every vector is orthogonal to its image under `T`. -/
theorem inner_timeReversal_self_eq_zero (T : V → V)
    (hanti : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT2 : ∀ x : V, T (T x) = -x) (x : V) :
    ⟪x, T x⟫_ℂ = 0 := by
  have h1 : ⟪T x, T (T x)⟫_ℂ = ⟪T x, x⟫_ℂ := hanti x (T x)
  rw [hT2 x, inner_neg_right] at h1
  have h2 : ⟪T x, x⟫_ℂ = 0 := by linear_combination (-1 / 2 : ℂ) * h1
  have h3 : ⟪x, T x⟫_ℂ = (starRingEnd ℂ) (⟪T x, x⟫_ℂ) := (inner_conj_symm _ _).symm
  rw [h3, h2, map_zero]

/-- **Kramers degeneracy.**  Let `H` be the Hamiltonian (a linear operator) of a
finite-dimensional quantum system, and let `T` be an antiunitary time-reversal operator
(conjugate-linear, `⟪T x, T y⟫ = ⟪y, x⟫`) with `T ∘ T = -1`, which is the case of
half-integer total spin.  If `H` is time-reversal invariant (`H ∘ T = T ∘ H`), then every
energy level `E` of `H` is (at least) doubly degenerate: its eigenspace has dimension `≥ 2`. -/
theorem kramers_degeneracy [FiniteDimensional ℂ V]
    (T : V → V)
    (hsmul : ∀ (c : ℂ) (x : V), T (c • x) = (starRingEnd ℂ) c • T x)
    (hanti : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT2 : ∀ x : V, T (T x) = -x)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ x : V, H (T x) = T (H x))
    (E : ℝ) (ψ : V) (hψ : ψ ≠ 0) (heig : H ψ = (E : ℂ) • ψ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H (E : ℂ)) := by
  set W := Module.End.eigenspace H (E : ℂ) with hW
  -- `ψ` lies in the eigenspace
  have hψW : ψ ∈ W := by
    simp [hW, heig]
  -- `T ψ` lies in the eigenspace as well
  have hTψW : T ψ ∈ W := by
    have : H (T ψ) = (E : ℂ) • T ψ := by
      rw [hcomm ψ, heig, hsmul]
      simp
    simp [hW, this]
  -- `T ψ` is nonzero
  have hTψ : T ψ ≠ 0 := by
    intro h
    apply hψ
    have := hT2 ψ
    rw [h] at this
    have h0 : T (0 : V) = 0 := by
      have := hsmul 0 0
      simpa using this
    rw [h0] at this
    exact by simpa using this.symm
  -- orthogonality of `ψ` and `T ψ`
  have horth : ⟪ψ, T ψ⟫_ℂ = 0 := inner_timeReversal_self_eq_zero T hanti hT2 ψ
  have horth' : ⟪T ψ, ψ⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (T ψ) ψ, horth, map_zero]
  -- linear independence of the pair in `V`
  have hli : LinearIndependent ℂ ![ψ, T ψ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    constructor
    · have h1 : ⟪ψ, s • ψ + t • T ψ⟫_ℂ = 0 := by rw [hst, inner_zero_right]
      rw [inner_add_right, inner_smul_right, inner_smul_right, horth] at h1
      have hn : ⟪ψ, ψ⟫_ℂ ≠ 0 := by rw [ne_eq, inner_self_eq_zero]; exact hψ
      have h2 : s * ⟪ψ, ψ⟫_ℂ = 0 := by simpa using h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 hn
    · have h1 : ⟪T ψ, s • ψ + t • T ψ⟫_ℂ = 0 := by rw [hst, inner_zero_right]
      rw [inner_add_right, inner_smul_right, inner_smul_right, horth'] at h1
      have hn : ⟪T ψ, T ψ⟫_ℂ ≠ 0 := by rw [ne_eq, inner_self_eq_zero]; exact hTψ
      have h2 : t * ⟪T ψ, T ψ⟫_ℂ = 0 := by simpa using h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 hn
  -- transfer to the eigenspace
  have hli' : LinearIndependent ℂ (![(⟨ψ, hψW⟩ : W), ⟨T ψ, hTψW⟩]) := by
    apply LinearIndependent.of_comp W.subtype
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  have := hli'.fintype_card_le_finrank
  simpa using this

end Phys

