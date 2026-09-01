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

import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede any module documentation, so the
header comment above is placed immediately after the single `import Mathlib`.)

Pure qubit states (unit vectors in `ℂ²`) modulo global phase are in bijection with
the points of the unit 2-sphere `S² ⊆ ℝ³`, via the Bloch vector
`(2 Re(conj a * b), 2 Im(conj a * b), |a|² - |b|²)`.
-/

namespace QC

open Complex

/-- A (normalized) pure qubit state: a unit vector in `ℂ²`. -/
def Qubit : Type := {v : ℂ × ℂ // normSq v.1 + normSq v.2 = 1}

/-- Two qubit states are equivalent when they differ by a global phase. -/
def phaseRel (v w : Qubit) : Prop :=
  ∃ z : ℂ, normSq z = 1 ∧ w.val.1 = z * v.val.1 ∧ w.val.2 = z * v.val.2

theorem phaseRel_refl (v : Qubit) : phaseRel v v :=
  ⟨1, by simp, by ring, by ring⟩

theorem phaseRel_symm {v w : Qubit} (h : phaseRel v w) : phaseRel w v := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hz; simp at hz
  refine ⟨z⁻¹, ?_, ?_, ?_⟩
  · rw [normSq_inv, hz]; norm_num
  · rw [h1]; field_simp
  · rw [h2]; field_simp

theorem phaseRel_trans {u v w : Qubit} (h1 : phaseRel u v) (h2 : phaseRel v w) :
    phaseRel u w := by
  obtain ⟨z, hz, hz1, hz2⟩ := h1
  obtain ⟨y, hy, hy1, hy2⟩ := h2
  exact ⟨y * z, by rw [map_mul, hy, hz]; ring, by rw [hy1, hz1]; ring, by rw [hy2, hz2]; ring⟩

/-- The setoid identifying qubit states that differ by a global phase. -/
def phaseSetoid : Setoid Qubit where
  r := phaseRel
  iseqv := ⟨phaseRel_refl, phaseRel_symm, phaseRel_trans⟩

/-- Pure qubit states modulo global phase. -/
def PureState : Type := Quotient phaseSetoid

/-- The unit 2-sphere in `ℝ³`. -/
def Sphere2 : Type := {p : ℝ × ℝ × ℝ // p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

/-- The Bloch vector of a pair of complex amplitudes. -/
def blochVec (v : ℂ × ℂ) : ℝ × ℝ × ℝ :=
  (2 * ((starRingEnd ℂ) v.1 * v.2).re, 2 * ((starRingEnd ℂ) v.1 * v.2).im,
    normSq v.1 - normSq v.2)

theorem blochVec_mem (v : Qubit) :
    (blochVec v.val).1 ^ 2 + (blochVec v.val).2.1 ^ 2 + (blochVec v.val).2.2 ^ 2 = 1 := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  simp only [normSq_apply] at h
  simp only [blochVec, normSq_apply, Complex.mul_re, Complex.mul_im, conj_re, conj_im]
  linear_combination (a.re * a.re + a.im * a.im + b.re * b.re + b.im * b.im + 1) * h

/-- The Bloch map on normalized states. -/
def bloch (v : Qubit) : Sphere2 := ⟨blochVec v.val, blochVec_mem v⟩

theorem bloch_phase_invariant {v w : Qubit} (h : phaseRel v w) : bloch v = bloch w := by
  obtain ⟨z, hz, h1, h2⟩ := h
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨c, d⟩, hw⟩ := w
  simp only at h1 h2
  subst h1
  subst h2
  apply Subtype.ext
  simp only [normSq_apply] at hz
  simp only [bloch, blochVec, normSq_apply, Complex.mul_re, Complex.mul_im, conj_re, conj_im,
    Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(2 * (a.re * b.re + a.im * b.im))) * hz
  · linear_combination (-(2 * (a.re * b.im - a.im * b.re))) * hz
  · linear_combination (-(a.re * a.re + a.im * a.im - b.re * b.re - b.im * b.im)) * hz

/-- The induced map from pure states modulo phase to the sphere. -/
def blochQuot : PureState → Sphere2 :=
  Quotient.lift bloch (fun _ _ h => bloch_phase_invariant h)

/-- Injectivity at the level of representatives: equal Bloch vectors force a global phase. -/
theorem bloch_inj_aux {v w : Qubit} (h : bloch v = bloch w) : phaseRel v w := by
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨c, d⟩, hw⟩ := w
  have h' := congrArg Subtype.val h
  simp only [bloch, blochVec, Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  simp only [normSq_apply] at hv hw
  have hna : normSq a = normSq c := by
    simp only [normSq_apply] at h3 ⊢; linarith
  have hnb : normSq b = normSq d := by
    simp only [normSq_apply] at h3 ⊢; linarith
  have hcd : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d := by
    apply Complex.ext <;> linarith
  by_cases ha : a = 0
  · subst ha
    have hc : c = 0 := by
      have h0 : normSq c = 0 := by simpa using hna.symm
      exact normSq_eq_zero.mp h0
    have hnb1 : normSq b = 1 := by simpa using hv
    have hb : b ≠ 0 := by
      intro h0
      rw [h0] at hnb1
      simp at hnb1
    refine ⟨d / b, ?_, by simp [hc], ?_⟩
    · rw [map_div₀, ← hnb, hnb1]; norm_num
    · field_simp
  · have hane : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
    have key : (starRingEnd ℂ) a * (c * b) = (starRingEnd ℂ) a * (a * d) := by
      have e1 : (starRingEnd ℂ) a * (c * b) = c * ((starRingEnd ℂ) c * d) := by
        rw [← hcd]; ring
      have e2 : c * ((starRingEnd ℂ) c * d) = (normSq c : ℂ) * d := by
        rw [← Complex.mul_conj]; ring
      have e3 : (starRingEnd ℂ) a * (a * d) = (normSq a : ℂ) * d := by
        rw [← Complex.mul_conj]; ring
      rw [e1, e2, e3, hna]
    have hcb : c * b = a * d := mul_left_cancel₀ hane key
    refine ⟨c / a, ?_, ?_, ?_⟩
    · rw [map_div₀, ← hna]
      have : normSq a ≠ 0 := by simpa using ha
      field_simp
    · field_simp
    · field_simp
      linear_combination -hcb

theorem blochQuot_injective : Function.Injective blochQuot := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ v =>
    induction y using Quotient.inductionOn with
    | _ w =>
      exact Quotient.sound (bloch_inj_aux h)

theorem blochQuot_surjective : Function.Surjective blochQuot := by
  rintro ⟨⟨x, y, zc⟩, hp⟩
  simp only at hp
  by_cases hz : zc = -1
  · subst hz
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨Quotient.mk phaseSetoid ⟨(0, 1), by simp⟩, ?_⟩
    apply Subtype.ext
    simp [blochQuot, bloch, blochVec, hx, hy]
  · have hle : -1 ≤ zc := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hzlt : -1 < zc := lt_of_le_of_ne hle (fun h => hz h.symm)
    have hpos : (0:ℝ) < (1 + zc) / 2 := by linarith
    set r : ℝ := Real.sqrt ((1 + zc) / 2) with hrdef
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = (1 + zc) / 2 := Real.sq_sqrt hpos.le
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hnorm : normSq ((r : ℂ)) + normSq (⟨x / (2 * r), y / (2 * r)⟩ : ℂ) = 1 := by
      simp only [normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      nlinarith [hr2, hp]
    refine ⟨Quotient.mk phaseSetoid ⟨((r : ℂ), (⟨x / (2 * r), y / (2 * r)⟩ : ℂ)), hnorm⟩, ?_⟩
    apply Subtype.ext
    simp only [blochQuot, Quotient.lift_mk, bloch, blochVec, normSq_apply, Complex.mul_re,
      Complex.mul_im, conj_re, conj_im, Complex.ofReal_re, Complex.ofReal_im, Prod.mk.injEq]
    refine ⟨by field_simp; ring, by field_simp; ring, ?_⟩
    field_simp
    nlinarith [hr2, hp]

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection
with the points of the 2-sphere `S²`. -/
theorem bloch_sphere_bijection : Function.Bijective blochQuot :=
  ⟨blochQuot_injective, blochQuot_surjective⟩

end QC

