/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib


open scoped InnerProductSpace

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a family of (bounded) Hamiltonians on a complex inner product
space `E`, depending on a parameter, and suppose that for every parameter value `t` the vector
`psi t` is a normalized eigenvector of `H t` with (real) eigenvalue `en t`:
`H t (psi t) = en t • psi t` and `⟪psi t, psi t⟫ = 1`.

If, at the parameter value `l`, the family `H`, the eigenvector `psi` and the eigenvalue `en`
are differentiable (with derivatives `dH`, `psi'`, `en'`) and `H l` is Hermitian, then

`dEₙ/dλ = ⟪ψₙ | ∂H/∂λ | ψₙ⟫`,

i.e. `en' = ⟪psi l, dH (psi l)⟫`. -/
theorem hellmann_feynman
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : ℝ → (E →L[ℂ] E)) (dH : E →L[ℂ] E) (psi : ℝ → E) (psi' : E)
    (en : ℝ → ℝ) (en' l : ℝ)
    (hH : HasDerivAt H dH l) (hpsi : HasDerivAt psi psi' l) (hen : HasDerivAt en en' l)
    (hsym : ∀ x y : E, ⟪H l x, y⟫_ℂ = ⟪x, H l y⟫_ℂ)
    (heig : ∀ t, H t (psi t) = (en t : ℂ) • psi t)
    (hnorm : ∀ t, ⟪psi t, psi t⟫_ℂ = 1) :
    (en' : ℂ) = ⟪psi l, dH (psi l)⟫_ℂ := by
  -- Differentiate the map `t ↦ H t (psi t)` (product rule for the application map).
  have h1 : HasDerivAt (fun t => (H t).restrictScalars ℝ) (dH.restrictScalars ℝ) l :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt l hH
  have hHpsi : HasDerivAt (fun t => H t (psi t)) (dH (psi l) + H l psi') l := h1.clm_apply hpsi
  -- Differentiate the expectation value `t ↦ ⟪psi t, H t (psi t)⟫`.
  have hE : HasDerivAt (fun t => ⟪psi t, H t (psi t)⟫_ℂ)
      (⟪psi l, dH (psi l) + H l psi'⟫_ℂ + ⟪psi', H l (psi l)⟫_ℂ) l := hpsi.inner ℂ hHpsi
  -- The expectation value is exactly the eigenvalue.
  have hfun : (fun t => ⟪psi t, H t (psi t)⟫_ℂ) = fun t => ((en t : ℂ)) := by
    funext t
    rw [heig t, inner_smul_right, hnorm t, mul_one]
  rw [hfun] at hE
  have hderiv := hE.unique hen.ofReal_comp
  -- Normalization kills the terms involving `psi'`.
  have hN : HasDerivAt (fun t => ⟪psi t, psi t⟫_ℂ) (⟪psi l, psi'⟫_ℂ + ⟪psi', psi l⟫_ℂ) l :=
    hpsi.inner ℂ hpsi
  have hN0 : (⟪psi l, psi'⟫_ℂ + ⟪psi', psi l⟫_ℂ) = 0 := by
    refine hN.unique ?_
    have hconst : (fun t => ⟪psi t, psi t⟫_ℂ) = fun _ : ℝ => (1 : ℂ) := funext hnorm
    rw [hconst]
    exact hasDerivAt_const _ _
  have e1 : ⟪psi l, H l psi'⟫_ℂ = (en l : ℂ) * ⟪psi l, psi'⟫_ℂ := by
    rw [← hsym, heig l, inner_smul_left]
    simp
  have e2 : ⟪psi', H l (psi l)⟫_ℂ = (en l : ℂ) * ⟪psi', psi l⟫_ℂ := by
    rw [heig l, inner_smul_right]
  rw [inner_add_right, e1, e2] at hderiv
  have hz : (en l : ℂ) * ⟪psi l, psi'⟫_ℂ + (en l : ℂ) * ⟪psi', psi l⟫_ℂ = 0 := by
    rw [← mul_add, hN0, mul_zero]
  linear_combination -hderiv + hz

end Phys

