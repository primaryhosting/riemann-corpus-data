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

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/
def Qubit : Type := {v : ℂ × ℂ // normSq v.1 + normSq v.2 = 1}

namespace Qubit

/-- The first amplitude of a qubit state. -/
def fst (v : Qubit) : ℂ := v.1.1

/-- The second amplitude of a qubit state. -/
def snd (v : Qubit) : ℂ := v.1.2

theorem norm_eq (v : Qubit) : normSq v.fst + normSq v.snd = 1 := v.2

@[ext] theorem ext {v w : Qubit} (h1 : v.fst = w.fst) (h2 : v.snd = w.snd) : v = w := by
  cases v; cases w
  simp only [Subtype.mk.injEq, Prod.ext_iff]
  exact ⟨h1, h2⟩

/-- Two qubit states are equivalent when they differ by a global phase. -/
instance setoid : Setoid Qubit where
  r v w := ∃ c : ℂ, ‖c‖ = 1 ∧ w.fst = c * v.fst ∧ w.snd = c * v.snd
  iseqv := by
    refine ⟨fun v => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨c, hc, h1, h2⟩
      have hc0 : c ≠ 0 := by
        intro h; rw [h] at hc; simp at hc
      exact ⟨c⁻¹, by simp [hc], by rw [h1]; field_simp, by rw [h2]; field_simp⟩
    · rintro u v w ⟨c, hc, h1, h2⟩ ⟨d, hd, h3, h4⟩
      exact ⟨d * c, by simp [hd, hc], by rw [h3, h1]; ring, by rw [h4, h2]; ring⟩

end Qubit

/-- Pure qubit states modulo global phase. -/
def PureState : Type := Quotient Qubit.setoid

/-- The two-sphere `S² ⊆ ℝ³`. -/
def Sphere2 : Type := {p : ℝ × ℝ × ℝ // p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

/-- The Bloch vector of a qubit state:
`(2 Re(conj a * b), 2 Im(conj a * b), |a|² - |b|²)`. -/
def bloch (v : Qubit) : Sphere2 :=
  ⟨(2 * ((starRingEnd ℂ) v.fst * v.snd).re,
    2 * ((starRingEnd ℂ) v.fst * v.snd).im,
    normSq v.fst - normSq v.snd), by
    have h := v.norm_eq
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply] at *
    nlinarith [h, sq_nonneg (v.fst.re * v.snd.re), sq_nonneg (v.fst.im * v.snd.im)]⟩

theorem bloch_phase_invariant {v w : Qubit} (h : v ≈ w) : bloch v = bloch w := by
  obtain ⟨c, hc, h1, h2⟩ := h
  have hcn : normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  have hcn' : c.re ^ 2 + c.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, sq] using hcn
  simp only [bloch, Subtype.mk.injEq, Prod.mk.injEq, h1, h2]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply] <;> nlinarith [hcn']

/-- The Bloch map descended to states modulo global phase. -/
def blochQuot : PureState → Sphere2 :=
  Quotient.lift bloch fun _ _ h => bloch_phase_invariant h

theorem blochQuot_injective : Function.Injective blochQuot := by
  refine fun x y => Quotient.inductionOn₂ x y ?_
  rintro v w h
  simp only [blochQuot, Quotient.lift_mk] at h
  -- extract the three coordinate equations
  have h1 : ((starRingEnd ℂ) v.fst * v.snd) = ((starRingEnd ℂ) w.fst * w.snd) := by
    have hre := congrArg (fun p => p.1.1) h
    have him := congrArg (fun p => p.1.2.1) h
    simp only [bloch] at hre him
    apply Complex.ext <;> linarith
  have h2 : normSq v.fst - normSq v.snd = normSq w.fst - normSq w.snd := by
    have := congrArg (fun p => p.1.2.2) h
    simpa [bloch] using this
  have hv := v.norm_eq
  have hw := w.norm_eq
  have ha : normSq v.fst = normSq w.fst := by linarith
  have hb : normSq v.snd = normSq w.snd := by linarith
  apply Quotient.sound
  by_cases hvz : v.fst = 0
  · have hwz : w.fst = 0 := by
      have : normSq w.fst = 0 := by rw [← ha, hvz]; simp
      simpa [Complex.normSq_eq_zero] using this
    have hvs : normSq v.snd = 1 := by
      rw [hvz] at hv; simpa using hv
    have hvs0 : v.snd ≠ 0 := by
      intro hz; rw [hz] at hvs; simp at hvs
    refine ⟨w.snd / v.snd, ?_, ?_, ?_⟩
    · have hws : normSq w.snd = 1 := by rw [← hb, hvs]
      have h1 : ‖w.snd‖ = 1 := by
        have := Complex.normSq_eq_norm_sq w.snd
        rw [hws] at this
        nlinarith [norm_nonneg w.snd]
      have h2 : ‖v.snd‖ = 1 := by
        have := Complex.normSq_eq_norm_sq v.snd
        rw [hvs] at this
        nlinarith [norm_nonneg v.snd]
      rw [norm_div, h1, h2]; norm_num
    · rw [hvz, hwz]; ring
    · field_simp
  · have hwz : w.fst ≠ 0 := by
      intro hz
      apply hvz
      have : normSq v.fst = 0 := by rw [ha, hz]; simp
      simpa [Complex.normSq_eq_zero] using this
    refine ⟨w.fst / v.fst, ?_, ?_, ?_⟩
    · have hvn : ‖v.fst‖ ^ 2 = ‖w.fst‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ha]
      have : ‖v.fst‖ = ‖w.fst‖ := by
        nlinarith [norm_nonneg v.fst, norm_nonneg w.fst]
      rw [norm_div, ← this]
      field_simp
      simpa [Complex.norm_eq_zero] using hvz
    · field_simp
    · -- w.snd = (w.fst / v.fst) * v.snd, i.e. v.fst * w.snd = w.fst * v.snd
      have key : v.fst * w.snd = w.fst * v.snd := by
        have hc : (starRingEnd ℂ) w.fst * (v.fst * w.snd)
            = (starRingEnd ℂ) w.fst * (w.fst * v.snd) := by
          calc (starRingEnd ℂ) w.fst * (v.fst * w.snd)
              = v.fst * ((starRingEnd ℂ) w.fst * w.snd) := by ring
            _ = v.fst * ((starRingEnd ℂ) v.fst * v.snd) := by rw [h1]
            _ = ((normSq v.fst : ℂ)) * v.snd := by
                  rw [← Complex.normSq_eq_conj_mul_self]; ring
            _ = ((normSq w.fst : ℂ)) * v.snd := by rw [ha]
            _ = (starRingEnd ℂ) w.fst * (w.fst * v.snd) := by
                  rw [← Complex.normSq_eq_conj_mul_self]; ring
        have hne : (starRingEnd ℂ) w.fst ≠ 0 := by
          simpa using hwz
        exact mul_left_cancel₀ hne hc
      field_simp
      linear_combination -key

theorem blochQuot_surjective : Function.Surjective blochQuot := by
  rintro ⟨⟨x, y, z⟩, hp⟩
  simp only at hp
  by_cases hz : z = -1
  · refine ⟨Quotient.mk _ ⟨(0, 1), by simp⟩, ?_⟩
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    simp only [blochQuot, Quotient.lift_mk, bloch, Qubit.fst, Qubit.snd, Subtype.mk.injEq,
      Prod.mk.injEq]
    refine ⟨by simp [hx], by simp [hy], by simp [hz]⟩
  · have hz1 : (1 : ℝ) + z > 0 := by
      rcases lt_trichotomy z (-1) with h | h | h
      · nlinarith [sq_nonneg x, sq_nonneg y]
      · exact absurd h hz
      · linarith
    set a : ℝ := Real.sqrt ((1 + z) / 2) with ha
    have ha2 : a ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
    refine ⟨Quotient.mk _ ⟨((a : ℂ), (x / (2 * a) : ℝ) + (y / (2 * a) : ℝ) * Complex.I), ?_⟩, ?_⟩
    · simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hane : a ≠ 0 := ne_of_gt hapos
      field_simp
      nlinarith [ha2, hp]
    · simp only [blochQuot, Quotient.lift_mk, bloch, Qubit.fst, Qubit.snd, Subtype.mk.injEq,
        Prod.mk.injEq, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.normSq_apply]
      have hane : a ≠ 0 := ne_of_gt hapos
      refine ⟨by field_simp; ring, by field_simp; ring, ?_⟩
      field_simp
      nlinarith [ha2, hp]

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection with
the points of the two-sphere `S²`. -/
theorem bloch_sphere_bijection : Function.Bijective blochQuot :=
  ⟨blochQuot_injective, blochQuot_surjective⟩

/-- The Bloch sphere bijection packaged as an equivalence. -/
noncomputable def blochEquiv : PureState ≃ Sphere2 :=
  Equiv.ofBijective blochQuot bloch_sphere_bijection

end QC

