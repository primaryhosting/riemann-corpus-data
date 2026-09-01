/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Momentum selection rule.**  If `T` preserves the inner product (a translation
operator is unitary) and two states are `T`-eigenvectors with *different* eigenvalues,
the first one being a unit vector, then the two states are orthogonal.

This is the step of the Lieb–Schultz–Mattis argument which guarantees that the twisted
state, carrying a different lattice momentum, is orthogonal to the ground state. -/
theorem inner_eq_zero_of_translation_eigenvalue_ne
    {T : E →ₗ[ℂ] E} (hT : ∀ x y : E, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    {ψ φ : E} {t s : ℂ} (ht : ‖ψ‖ = 1)
    (hψ : T ψ = t • ψ) (hφ : T φ = s • φ) (hne : s ≠ t) :
    ⟪ψ, φ⟫_ℂ = 0 := by
  -- `|t| = 1`, i.e. `conj t * t = 1`
  have hnorm : (starRingEnd ℂ) t * t = 1 := by
    have h := hT ψ ψ
    rw [hψ, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ht] at h
    simpa using h
  have key : (starRingEnd ℂ) t * s * ⟪ψ, φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
    have h := hT ψ φ
    rw [hψ, hφ, inner_smul_left, inner_smul_right, ← mul_assoc] at h
    exact h
  have key' : ((starRingEnd ℂ) t * s - 1) * ⟪ψ, φ⟫_ℂ = 0 := by linear_combination key
  rcases mul_eq_zero.1 key' with h | h
  · -- `conj t * s = 1` together with `conj t * t = 1` forces `s = t`, a contradiction
    exact absurd (by linear_combination t * h - s * hnorm : s = t) hne
  · exact h

/-- **Lieb–Schultz–Mattis theorem (operator core).**

A translation-invariant spin chain whose sites carry *half-integer* spin
`S = twoS / 2` (with `twoS` odd) cannot have a unique ground state separated by a gap
larger than the twist energy `ε`: it is either degenerate or gapless.

Formal setting.  `E` is the complex Hilbert space of the chain, `H` its Hamiltonian,
`T` the translation operator (unitary, as encoded by `hT`), and `ψ₀` a normalized
ground state of energy `E₀` (minimality of the energy is `hmin`, and `hground` says
that `ψ₀` realizes it) which, by translation invariance, carries a definite momentum
eigenvalue `t` (`hTψ`).  The Lieb–Schultz–Mattis twist operator `U` produces the
variational state `U ψ₀`, which is normalized (`hUnorm`), has energy at most `E₀ + ε`
(`hEnergy`; on a chain of `L` sites the twist estimate gives `ε = O(1/L)`), and whose
momentum is shifted by the factor `(-1) ^ twoS` relative to the ground state (`hTU`).
For half-integer spin, `twoS` is odd and this factor is `-1`, i.e. a momentum shift
by `π`.

Conclusion: there is a normalized state orthogonal to the ground state whose energy
either equals the ground-state energy (ground-state **degeneracy**) or exceeds it by
at most `ε` (**gaplessness**: the spectral gap above `ψ₀` is bounded by the twist
energy, which tends to `0` in the thermodynamic limit). -/
theorem lieb_schultz_mattis
    {H T U : E →ₗ[ℂ] E} {ψ₀ : E} {E₀ ε : ℝ} {t : ℂ} {twoS : ℕ}
    -- half-integer spin per site: the spin is `twoS / 2` with `twoS` odd
    (hspin : Odd twoS)
    -- the translation operator is unitary
    (hT : ∀ x y : E, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    -- `ψ₀` is a normalized ground state of energy `E₀`
    (hψnorm : ‖ψ₀‖ = 1)
    (hmin : ∀ φ : E, ‖φ‖ = 1 → E₀ ≤ (⟪φ, H φ⟫_ℂ).re)
    (hground : (⟪ψ₀, H ψ₀⟫_ℂ).re = E₀)
    -- translation invariance: the ground state has a definite momentum
    (hTψ : T ψ₀ = t • ψ₀)
    -- the twisted state is normalized and its momentum is shifted by `(-1) ^ twoS`
    (hUnorm : ‖U ψ₀‖ = 1)
    (hTU : T (U ψ₀) = ((-1) ^ twoS * t) • (U ψ₀))
    -- the twist costs at most the energy `ε`
    (hEnergy : (⟪U ψ₀, H (U ψ₀)⟫_ℂ).re ≤ E₀ + ε) :
    (∃ φ : E, ‖φ‖ = 1 ∧ ⟪ψ₀, φ⟫_ℂ = 0 ∧
      (⟪φ, H φ⟫_ℂ).re = (⟪ψ₀, H ψ₀⟫_ℂ).re) ∨
    (∃ φ : E, ‖φ‖ = 1 ∧ ⟪ψ₀, φ⟫_ℂ = 0 ∧
      (⟪ψ₀, H ψ₀⟫_ℂ).re < (⟪φ, H φ⟫_ℂ).re ∧
      (⟪φ, H φ⟫_ℂ).re ≤ (⟪ψ₀, H ψ₀⟫_ℂ).re + ε) := by
  rw [hground]
  -- half-integer spin ⟹ the momentum shift is a genuine sign flip
  have hsign : ((-1 : ℂ)) ^ twoS = -1 := hspin.neg_one_pow
  have ht0 : t ≠ 0 := by
    intro h
    have h0 : ⟪ψ₀, ψ₀⟫_ℂ = 0 := by
      rw [← hT ψ₀ ψ₀, hTψ, h, zero_smul, inner_zero_left]
    rw [inner_self_eq_zero] at h0
    rw [h0, norm_zero] at hψnorm
    exact one_ne_zero hψnorm.symm
  have hne : (-1 : ℂ) ^ twoS * t ≠ t := by
    rw [hsign]
    intro h
    exact ht0 (by linear_combination -h / 2)
  -- momentum selection rule: the twisted state is orthogonal to the ground state
  have horth : ⟪ψ₀, U ψ₀⟫_ℂ = 0 :=
    inner_eq_zero_of_translation_eigenvalue_ne hT hψnorm hTψ hTU hne
  -- the twisted state is a variational state of energy at most `E₀ + ε`
  rcases eq_or_lt_of_le (hmin _ hUnorm) with h | h
  · exact Or.inl ⟨U ψ₀, hUnorm, horth, h.symm⟩
  · exact Or.inr ⟨U ψ₀, hUnorm, horth, h, hEnergy⟩

/-- **Lieb–Schultz–Mattis theorem, from the twist–translation commutation relation.**

Same conclusion as `Phys.lieb_schultz_mattis`, but the momentum shift of the twisted
state is now derived from the more primitive algebraic input `hcomm`, the
commutation relation `T U = (-1) ^ twoS • U T` between the translation operator and
the Lieb–Schultz–Mattis twist (evaluated on the ground state).  For half-integer spin
per site (`twoS` odd) the sign is `-1`, so the twist shifts the momentum by `π`. -/
theorem lieb_schultz_mattis_of_twist_commutation
    {H T U : E →ₗ[ℂ] E} {ψ₀ : E} {E₀ ε : ℝ} {t : ℂ} {twoS : ℕ}
    (hspin : Odd twoS)
    (hT : ∀ x y : E, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hψnorm : ‖ψ₀‖ = 1)
    (hmin : ∀ φ : E, ‖φ‖ = 1 → E₀ ≤ (⟪φ, H φ⟫_ℂ).re)
    (hground : (⟪ψ₀, H ψ₀⟫_ℂ).re = E₀)
    (hTψ : T ψ₀ = t • ψ₀)
    (hUnorm : ‖U ψ₀‖ = 1)
    (hcomm : T (U ψ₀) = ((-1 : ℂ)) ^ twoS • U (T ψ₀))
    (hEnergy : (⟪U ψ₀, H (U ψ₀)⟫_ℂ).re ≤ E₀ + ε) :
    (∃ φ : E, ‖φ‖ = 1 ∧ ⟪ψ₀, φ⟫_ℂ = 0 ∧
      (⟪φ, H φ⟫_ℂ).re = (⟪ψ₀, H ψ₀⟫_ℂ).re) ∨
    (∃ φ : E, ‖φ‖ = 1 ∧ ⟪ψ₀, φ⟫_ℂ = 0 ∧
      (⟪ψ₀, H ψ₀⟫_ℂ).re < (⟪φ, H φ⟫_ℂ).re ∧
      (⟪φ, H φ⟫_ℂ).re ≤ (⟪ψ₀, H ψ₀⟫_ℂ).re + ε) := by
  have hTU : T (U ψ₀) = ((-1 : ℂ) ^ twoS * t) • (U ψ₀) := by
    rw [hcomm, hTψ, map_smul, smul_smul]
  exact lieb_schultz_mattis hspin hT hψnorm hmin hground hTψ hUnorm hTU hEnergy

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

