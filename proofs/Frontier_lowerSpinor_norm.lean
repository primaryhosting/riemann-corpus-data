import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

namespace Frontier

noncomputable section

open Complex Real intervalIntegral

/-! ## The two-level Bloch Hamiltonian and its lower band -/

/-- The two-level Bloch Hamiltonian `H(th, ph) = d̂(th,ph) · σ⃗`, where
`d̂ = (sin th cos ph, sin th sin ph, cos th)` is a unit vector and `σ⃗` are the Pauli matrices.
Explicitly `H = [[cos th, sin th e^{-iph}], [sin th e^{iph}, -cos th]]`. -/
def blochHamiltonian (th ph : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos th : ℂ), (Real.sin th : ℂ) * Complex.exp (-Complex.I * ph);
     (Real.sin th : ℂ) * Complex.exp (Complex.I * ph), -(Real.cos th : ℂ)]

/-- The (smooth, away from the poles) gauge choice for the normalized lower-band eigenvector
of `blochHamiltonian`. -/
def lowerSpinor (th ph : ℝ) : Fin 2 → ℂ :=
  ![(Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * ph), -(Real.cos (th / 2) : ℂ)]

/-- The lower spinor is normalized. -/
theorem lowerSpinor_norm (th ph : ℝ) :
    ∑ j : Fin 2, ‖lowerSpinor th ph j‖ ^ 2 = 1 := by
  have hexp : ‖Complex.exp (-Complex.I * (ph : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [lowerSpinor, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_mul, hexp, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_one]
  rw [sq_abs, sq_abs]
  exact Real.sin_sq_add_cos_sq _

/-- The lower spinor is an eigenvector of the Bloch Hamiltonian with eigenvalue `-1`. -/
theorem blochHamiltonian_mulVec_lowerSpinor (th ph : ℝ) :
    (blochHamiltonian th ph).mulVec (lowerSpinor th ph) = -lowerSpinor th ph := by
  have hs : Real.sin th = 2 * Real.sin (th / 2) * Real.cos (th / 2) := by
    have h := Real.sin_two_mul (th / 2)
    rw [show 2 * (th / 2) = th by ring] at h
    exact h
  have hc : Real.cos th = Real.cos (th / 2) ^ 2 - Real.sin (th / 2) ^ 2 := by
    have h := Real.cos_two_mul' (th / 2)
    rw [show 2 * (th / 2) = th by ring] at h
    exact h
  have hpyth : Real.sin (th / 2) ^ 2 + Real.cos (th / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have h1 : ((Real.sin (th / 2) : ℂ)) ^ 2 + ((Real.cos (th / 2) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hpyth
  have hsC : ((Real.sin th : ℝ) : ℂ)
      = 2 * ((Real.sin (th / 2) : ℝ) : ℂ) * ((Real.cos (th / 2) : ℝ) : ℂ) := by
    rw [hs]; simp
  have hcC : ((Real.cos th : ℝ) : ℂ)
      = ((Real.cos (th / 2) : ℝ) : ℂ) ^ 2 - ((Real.sin (th / 2) : ℝ) : ℂ) ^ 2 := by
    rw [hc]; simp
  have hee : Complex.exp (Complex.I * (ph : ℂ)) * Complex.exp (-Complex.I * (ph : ℂ)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  funext j
  fin_cases j <;>
    simp only [blochHamiltonian, lowerSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Pi.neg_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    rw [hsC, hcC]
  · linear_combination (-(Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ))) * h1
  · linear_combination (2 * (Real.sin (th / 2) : ℂ) ^ 2 * (Real.cos (th / 2) : ℂ)) * hee +
      (Real.cos (th / 2) : ℂ) * h1

/-! ## Berry connection and Berry curvature -/

/-- The `th`-component of the Berry connection `A_th = -i ⟨u | ∂_th u⟩` of the lower band. -/
def berryConnTheta (th ph : ℝ) : ℝ :=
  (-Complex.I * ∑ j : Fin 2,
      (starRingEnd ℂ) (lowerSpinor th ph j) * deriv (fun t : ℝ => lowerSpinor t ph j) th).re

/-- The `ph`-component of the Berry connection `A_ph = -i ⟨u | ∂_ph u⟩` of the lower band. -/
def berryConnPhi (th ph : ℝ) : ℝ :=
  (-Complex.I * ∑ j : Fin 2,
      (starRingEnd ℂ) (lowerSpinor th ph j) * deriv (fun s : ℝ => lowerSpinor th s j) ph).re

/-- The Berry curvature `F = ∂_th A_ph - ∂_ph A_th`. -/
def berryCurvature (th ph : ℝ) : ℝ :=
  deriv (fun t : ℝ => berryConnPhi t ph) th - deriv (fun s : ℝ => berryConnTheta th s) ph

/-- Conjugation of the phase factor. -/
theorem conj_exp_neg (ph : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-Complex.I * (ph : ℂ))) = Complex.exp (Complex.I * (ph : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The phase factor has unit modulus. -/
theorem exp_mul_exp_neg (ph : ℝ) :
    Complex.exp (Complex.I * (ph : ℂ)) * Complex.exp (-Complex.I * (ph : ℂ)) = 1 := by
  rw [← Complex.exp_add]; ring_nf; simp

theorem hasDerivAt_sin_half (th : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (Real.cos (th / 2) * (1 / 2)) th := by
  have hhalf : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) th := by
    simpa using (hasDerivAt_id th).div_const 2
  exact hhalf.sin

theorem hasDerivAt_cos_half (th : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (t / 2)) (-Real.sin (th / 2) * (1 / 2)) th := by
  have hhalf : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) th := by
    simpa using (hasDerivAt_id th).div_const 2
  exact hhalf.cos

/-- The `th`-component of the Berry connection vanishes in this gauge. -/
theorem berryConnTheta_eq (th ph : ℝ) : berryConnTheta th ph = 0 := by
  have hsin := hasDerivAt_sin_half th
  have hcos := hasDerivAt_cos_half th
  have hd0 : deriv (fun t : ℝ => lowerSpinor t ph 0) th
      = ((Real.cos (th / 2) * (1 / 2) : ℝ) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ)) := by
    simpa [lowerSpinor] using
      (hsin.ofReal_comp.mul_const (Complex.exp (-Complex.I * (ph : ℂ)))).deriv
  have hd1 : deriv (fun t : ℝ => lowerSpinor t ph 1) th
      = -((-Real.sin (th / 2) * (1 / 2) : ℝ) : ℂ) := by
    simpa [lowerSpinor] using hcos.ofReal_comp.neg.deriv
  have v0 : lowerSpinor th ph 0 = (Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ)) :=
    rfl
  have v1 : lowerSpinor th ph 1 = -(Real.cos (th / 2) : ℂ) := rfl
  have key : (-Complex.I * ∑ j : Fin 2,
      (starRingEnd ℂ) (lowerSpinor th ph j) * deriv (fun t : ℝ => lowerSpinor t ph j) th)
      = ((0 : ℝ) : ℂ) := by
    rw [Fin.sum_univ_two, hd0, hd1, v0, v1]
    simp only [map_mul, map_neg, Complex.conj_ofReal, conj_exp_neg, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_zero]
    linear_combination
      (-Complex.I * (Real.sin (th / 2) : ℂ) * (Real.cos (th / 2) : ℂ) / 2) * exp_mul_exp_neg ph
  rw [berryConnTheta, key, Complex.ofReal_re]

/-- The `ph`-component of the Berry connection equals `-sin²(th/2)`. -/
theorem berryConnPhi_eq (th ph : ℝ) : berryConnPhi th ph = -(Real.sin (th / 2)) ^ 2 := by
  have hlin : HasDerivAt (fun s : ℝ => -Complex.I * (s : ℂ)) (-Complex.I) ph := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := ph)).const_mul (-Complex.I)
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (s : ℂ)))
      (Complex.exp (-Complex.I * (ph : ℂ)) * -Complex.I) ph := hlin.cexp
  have hd0 : deriv (fun s : ℝ => lowerSpinor th s 0) ph
      = (Real.sin (th / 2) : ℂ) * (Complex.exp (-Complex.I * (ph : ℂ)) * -Complex.I) := by
    simpa [lowerSpinor] using (hexp.const_mul ((Real.sin (th / 2) : ℝ) : ℂ)).deriv
  have hd1 : deriv (fun s : ℝ => lowerSpinor th s 1) ph = 0 := by simp [lowerSpinor]
  have v0 : lowerSpinor th ph 0 = (Real.sin (th / 2) : ℂ) * Complex.exp (-Complex.I * (ph : ℂ)) :=
    rfl
  have v1 : lowerSpinor th ph 1 = -(Real.cos (th / 2) : ℂ) := rfl
  have key : (-Complex.I * ∑ j : Fin 2,
      (starRingEnd ℂ) (lowerSpinor th ph j) * deriv (fun s : ℝ => lowerSpinor th s j) ph)
      = ((-(Real.sin (th / 2)) ^ 2 : ℝ) : ℂ) := by
    rw [Fin.sum_univ_two, hd0, hd1, v0, v1, map_mul, Complex.conj_ofReal, conj_exp_neg,
      Complex.ofReal_neg, Complex.ofReal_pow]
    linear_combination (Complex.I ^ 2 * (Real.sin (th / 2) : ℂ) ^ 2) * exp_mul_exp_neg ph +
      ((Real.sin (th / 2) : ℂ) ^ 2) * Complex.I_sq
  rw [berryConnPhi, key, Complex.ofReal_re]

/-- The Berry curvature of the lower band is `-(1/2) sin th`: a magnetic monopole of unit
charge sitting at the degeneracy point. -/
theorem berryCurvature_eq (th ph : ℝ) :
    berryCurvature th ph = -(1 / 2) * Real.sin th := by
  have hfun : (fun t : ℝ => berryConnPhi t ph) = fun t : ℝ => -(Real.sin (t / 2)) ^ 2 :=
    funext fun t => berryConnPhi_eq t ph
  have hfun2 : (fun s : ℝ => berryConnTheta th s) = fun _ : ℝ => (0 : ℝ) :=
    funext fun s => berryConnTheta_eq th s
  have hd : HasDerivAt (fun t : ℝ => -(Real.sin (t / 2)) ^ 2)
      (-(2 * Real.sin (th / 2) ^ 1 * (Real.cos (th / 2) * (1 / 2)))) th :=
    ((hasDerivAt_sin_half th).pow 2).neg
  have hs : Real.sin th = 2 * Real.sin (th / 2) * Real.cos (th / 2) := by
    have h := Real.sin_two_mul (th / 2)
    rw [show 2 * (th / 2) = th by ring] at h
    exact h
  rw [berryCurvature, hfun, hfun2, hd.deriv, deriv_const, hs]
  ring

/-! ## Chern number and Hall conductance -/

/-- The (first) Chern number of a Berry curvature `F` over the parameter sphere,
`C = (1 / 2π) ∫₀^{2π} ∫₀^{π} F dth dph`. -/
def chernNumber (F : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ ph in (0:ℝ)..(2 * π), ∫ th in (0:ℝ)..π, F th ph

/-- The TKNN (Kubo-formula) Hall conductance associated with a Berry curvature `F`,
in units set by the electron charge `e` and Planck's constant `hP`:
`σ_xy = (e² / hP) · (1 / 2π) ∫∫ F`. -/
def hallConductance (F : ℝ → ℝ → ℝ) (e hP : ℝ) : ℝ :=
  (e ^ 2 / hP) * ((1 / (2 * π)) * ∫ ph in (0:ℝ)..(2 * π), ∫ th in (0:ℝ)..π, F th ph)

/-- The TKNN formula: the Hall conductance is the Chern number times `e²/hP`. -/
theorem hallConductance_eq_chernNumber_mul (F : ℝ → ℝ → ℝ) (e hP : ℝ) :
    hallConductance F e hP = chernNumber F * (e ^ 2 / hP) := by
  simp [hallConductance, chernNumber, mul_comm]

/-- The Chern number of the two-level model is `-1`. -/
theorem chernNumber_berryCurvature : chernNumber berryCurvature = -1 := by
  have hinner : (∫ th in (0:ℝ)..π, (-(1 / 2) * Real.sin th)) = -1 := by
    rw [intervalIntegral.integral_const_mul, integral_sin]
    norm_num
  rw [chernNumber]
  simp_rw [berryCurvature_eq]
  rw [hinner, intervalIntegral.integral_const, smul_eq_mul]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **TKNN theorem (base case).**  For the two-level Bloch Hamiltonian
`H(th,ph) = d̂ · σ⃗` with its normalized lower band `lowerSpinor`, the Berry curvature
`F = ∂_th A_ph - ∂_ph A_th` equals `-(1/2) sin th`, its Chern number is the integer `-1`,
and the integer quantum Hall conductance obtained from the TKNN/Kubo integral is exactly
that integer times `e²/h`. -/
theorem tknn_chern_hall (e hP : ℝ) :
    ∃ C : ℤ,
      (∀ th ph : ℝ, berryCurvature th ph = -(1 / 2) * Real.sin th) ∧
      chernNumber berryCurvature = (C : ℝ) ∧
      hallConductance berryCurvature e hP = (C : ℝ) * (e ^ 2 / hP) := by
  refine ⟨-1, berryCurvature_eq, ?_, ?_⟩
  · simpa using chernNumber_berryCurvature
  · rw [hallConductance_eq_chernNumber_mul, chernNumber_berryCurvature]
    norm_num

end

end Frontier

