import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped InnerProductSpace

/-- **Ehrenfest's theorem.**

Let `E` be a complex inner product space (the state space), `H : E →L[ℂ] E` a Hamiltonian
(assumed symmetric: `⟪H x, y⟫ = ⟪x, H y⟫`), and `psi : ℝ → E` a state trajectory satisfying the
Schrödinger equation `i ℏ ψ'(t) = H ψ(t)`.  Let `A : ℝ → (E →L[ℂ] E)` be a (possibly
time-dependent) observable, differentiable at `t` with derivative `A'`.

Then the expectation value `⟨A⟩(t) = ⟪ψ(t), A(t) ψ(t)⟫` is differentiable at `t` with

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`.

Here `[H, A] = H * A - A * H` is the commutator, the product on `E →L[ℂ] E` being composition. -/
theorem ehrenfest
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (hbar : ℝ) (hbar_ne : hbar ≠ 0)
    (H : E →L[ℂ] E) (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (psi : ℝ → E) (dpsi : E) (A : ℝ → (E →L[ℂ] E)) (A' : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi dpsi t) (hA : HasDerivAt A A' t)
    (hSch : (Complex.I * (hbar : ℂ)) • dpsi = H (psi t)) :
    HasDerivAt (fun s => ⟪psi s, (A s) (psi s)⟫_ℂ)
      ((Complex.I / (hbar : ℂ)) * ⟪psi t, (H * A t - A t * H) (psi t)⟫_ℂ
        + ⟪psi t, A' (psi t)⟫_ℂ) t := by
  have hbarC : (hbar : ℂ) ≠ 0 := by exact_mod_cast hbar_ne
  have hIhbar : Complex.I * (hbar : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hbarC
  -- Differentiate `s ↦ A s (ψ s)`; scalars are restricted to `ℝ` to differentiate the
  -- application map, which does not change the underlying function.
  have hAr : HasDerivAt (fun s => (A s).restrictScalars ℝ) (A'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  have hprod : HasDerivAt (fun s => (A s) (psi s)) (A' (psi t) + (A t) dpsi) t :=
    hAr.clm_apply hpsi
  have hinner : HasDerivAt (fun s => ⟪psi s, (A s) (psi s)⟫_ℂ)
      (⟪psi t, (A' (psi t) + (A t) dpsi)⟫_ℂ + ⟪dpsi, (A t) (psi t)⟫_ℂ) t := hpsi.inner ℂ hprod
  -- Solve the Schrödinger equation for `ψ'`.
  have hdpsi : dpsi = (Complex.I * (hbar : ℂ))⁻¹ • H (psi t) := by
    rw [← hSch, smul_smul, inv_mul_cancel₀ hIhbar, one_smul]
  have hinv : (Complex.I * (hbar : ℂ))⁻¹ = -(Complex.I / (hbar : ℂ)) := by
    rw [mul_inv, Complex.inv_I, div_eq_mul_inv]; ring
  have hsymm : ⟪H (psi t), (A t) (psi t)⟫_ℂ = ⟪psi t, H ((A t) (psi t))⟫_ℂ := hH _ _
  have hcomm : ⟪psi t, (H * A t - A t * H) (psi t)⟫_ℂ
      = ⟪psi t, H ((A t) (psi t))⟫_ℂ - ⟪psi t, (A t) (H (psi t))⟫_ℂ := by
    simp
  convert hinner using 1
  rw [hdpsi, hinv]
  simp only [map_smul, inner_smul_right, inner_smul_left, inner_add_right, map_neg, map_div₀,
    Complex.conj_I, Complex.conj_ofReal, hsymm, hcomm]
  ring

end QPhys

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

