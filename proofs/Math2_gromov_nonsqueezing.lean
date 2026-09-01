/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Math2

/-- The standard symplectic form on `ℂ ^ (n+1) ≅ ℝ ^ (2n+2)`, given by the imaginary part
of the hermitian inner product. -/
noncomputable def omegaForm {m : ℕ} (z w : EuclideanSpace ℂ (Fin m)) : ℝ :=
  (inner ℂ z w : ℂ).im

/-- Key intermediate lemma: if a map `f` sends the open ball of radius `r` into the open
disc of radius `R`, and the linear functional `omegaForm w ·` is dominated by `‖f ·‖`,
then `r * ‖w‖ ≤ R`. -/
lemma norm_le_of_omegaForm_bound {m : ℕ} {r R : ℝ} (hr : 0 < r)
    (w : EuclideanSpace ℂ (Fin m)) (f : EuclideanSpace ℂ (Fin m) → ℂ)
    (hf : ∀ z, ‖z‖ < r → ‖f z‖ < R)
    (hw : ∀ z, |omegaForm w z| ≤ ‖f z‖) :
    r * ‖w‖ ≤ R := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg (f 0)) (hf 0 (by simpa using hr))
  rcases eq_or_ne w 0 with hw0 | hw0
  · simp [hw0, hR.le]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  by_contra hcon
  push_neg at hcon
  set s : ℝ := R / ‖w‖ ^ 2 with hs
  have hspos : 0 < s := by positivity
  set z : EuclideanSpace ℂ (Fin m) := s • (Complex.I • w) with hz
  have hznorm : ‖z‖ = R / ‖w‖ := by
    rw [hz, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hs]
    simp
    field_simp
  have hom : omegaForm w z = R := by
    have h1 : (inner ℂ w (Complex.I • w) : ℂ).im = ‖w‖ ^ 2 := by
      simp [Complex.mul_im, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have h2 : (inner ℂ w z : ℂ) = (s : ℂ) * (inner ℂ w (Complex.I • w) : ℂ) := by
      rw [hz, show ((s : ℝ) • (Complex.I • w)) = ((s : ℂ) • (Complex.I • w)) by
        simp [Complex.coe_smul], inner_smul_right]
    simp only [omegaForm, h2, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h1]
    rw [hs]
    field_simp
    ring
  have h3 : R ≤ ‖f z‖ := by
    have := hw z
    rwa [hom, abs_of_pos hR] at this
  have h4 : ‖f z‖ < R := hf z (by rw [hznorm, div_lt_iff₀ hwpos]; linarith)
  linarith

/-- **Gromov's nonsqueezing theorem, linear case.**

If a linear symplectomorphism `Φ` of `ℂ^(n+1) ≅ ℝ^(2n+2)` (i.e. an `ℝ`-linear automorphism
preserving the standard symplectic form `omegaForm`) maps the open ball of radius `r > 0`
into the open symplectic cylinder `Z(R) = {z | ‖z 0‖ < R}`, then `r ≤ R`.

(The general, nonlinear statement of Gromov's theorem is not formalized here; this is the
classical linear version of the nonsqueezing phenomenon.) -/
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hr : 0 < r)
    (Φ : EuclideanSpace ℂ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin (n + 1)))
    (hsymp : ∀ z w, omegaForm (Φ z) (Φ w) = omegaForm z w)
    (hsq : ∀ z, ‖z‖ < r → ‖(Φ z) 0‖ < R) :
    r ≤ R := by
  set e0 : EuclideanSpace ℂ (Fin (n + 1)) := EuclideanSpace.single 0 (1 : ℂ) with he0
  set p : EuclideanSpace ℂ (Fin (n + 1)) := Φ.symm e0 with hp
  set q : EuclideanSpace ℂ (Fin (n + 1)) := Φ.symm (Complex.I • e0) with hq
  have hΦp : Φ p = e0 := by rw [hp]; exact Φ.apply_symm_apply e0
  have hΦq : Φ q = Complex.I • e0 := by rw [hq]; exact Φ.apply_symm_apply _
  -- the two coordinate functionals
  have hpz : ∀ z, omegaForm p z = ((Φ z) 0).im := by
    intro z
    rw [← hsymp p z, hΦp, he0]
    simp [omegaForm, EuclideanSpace.inner_single_left]
  have hqz : ∀ z, omegaForm q z = -((Φ z) 0).re := by
    intro z
    rw [← hsymp q z, hΦq, he0]
    simp [omegaForm, EuclideanSpace.inner_single_left, Complex.mul_im]
  -- the normalization coming from `ω(p, q) = 1`
  have hpq : omegaForm p q = 1 := by
    rw [← hsymp p q, hΦp, hΦq, he0]
    simp [omegaForm]
  have hCS : (1 : ℝ) ≤ ‖p‖ * ‖q‖ := by
    have h1 : omegaForm p q ≤ ‖(inner ℂ p q : ℂ)‖ := by
      simpa [omegaForm] using (Complex.abs_im_le_norm (inner ℂ p q : ℂ)).trans'
        (le_abs_self _)
    have h2 : ‖(inner ℂ p q : ℂ)‖ ≤ ‖p‖ * ‖q‖ := norm_inner_le_norm _ _
    linarith [hpq ▸ h1]
  -- apply the key lemma to both functionals
  have hbp : r * ‖p‖ ≤ R :=
    norm_le_of_omegaForm_bound hr p (fun z => (Φ z) 0) hsq (fun z => by
      rw [hpz z]; exact Complex.abs_im_le_norm _)
  have hbq : r * ‖q‖ ≤ R :=
    norm_le_of_omegaForm_bound hr q (fun z => (Φ z) 0) hsq (fun z => by
      rw [hqz z, abs_neg]; exact Complex.abs_re_le_norm _)
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) (hsq 0 (by simpa using hr))
  nlinarith [norm_nonneg p, norm_nonneg q, hr, hR, hbp, hbq, hCS]

/-- Sanity check: the hypotheses of `gromov_nonsqueezing` are satisfiable, and the conclusion
is sharp: the identity symplectomorphism maps the ball of radius `r` into the cylinder of
radius `r`. -/
example {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (∀ z w : EuclideanSpace ℂ (Fin (n + 1)),
        omegaForm (LinearEquiv.refl ℝ _ z) (LinearEquiv.refl ℝ _ w) = omegaForm z w) ∧
      ∀ z : EuclideanSpace ℂ (Fin (n + 1)), ‖z‖ < r → ‖(LinearEquiv.refl ℝ _ z) 0‖ < r :=
  ⟨fun _ _ => rfl, fun z hz => lt_of_le_of_lt (PiLp.norm_apply_le z 0) hz⟩

end Math2

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

