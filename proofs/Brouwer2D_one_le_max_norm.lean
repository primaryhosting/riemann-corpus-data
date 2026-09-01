/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/
noncomputable def diskProj (z : ℂ) : ℂ := (max 1 ‖z‖ : ℝ)⁻¹ • z

lemma one_le_max_norm (z : ℂ) : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _

lemma continuous_diskProj : Continuous diskProj := by
  refine Continuous.smul ?_ continuous_id
  exact (continuous_const.max continuous_norm).inv₀ fun z =>
    ne_of_gt (lt_of_lt_of_le one_pos (one_le_max_norm z))

lemma norm_diskProj_le (z : ℂ) : ‖diskProj z‖ ≤ 1 := by
  have h1 : (0 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le one_pos (one_le_max_norm z)
  have : ‖diskProj z‖ = ‖z‖ / max 1 ‖z‖ := by
    rw [diskProj, norm_smul]
    simp [abs_of_pos h1, div_eq_inv_mul]
  rw [this, div_le_one h1]
  exact le_max_right _ _

lemma diskProj_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : diskProj z = z := by
  have : max 1 ‖z‖ = 1 := max_eq_left hz
  simp [diskProj, this]

/-! ### Continuous logarithms on the plane -/

/-- Any nonvanishing continuous function on `ℂ` has a continuous logarithm,
by the lifting property of the covering map `exp : ℂ → ℂ \ {0}`. -/
theorem exists_continuous_log (g : C(ℂ, ℂ)) (hg : ∀ z, g z ≠ 0) :
    ∃ G : C(ℂ, ℂ), ∀ z, Complex.exp (G z) = g z := by
  obtain ⟨G, ⟨-, hG⟩, -⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g
      (a₀ := (0 : ℂ)) (e₀ := Complex.log (g 0)) (Complex.exp_log (hg 0))
      (fun a => by simpa using hg a)
  exact ⟨G, fun z => congrFun hG z⟩

/-! ### The key positivity estimate on the boundary circle -/

/-- If `z` lies on the unit circle and `w` lies in the closed unit disk with `w ≠ z`, then
`z - w` points strictly into the half plane determined by `z`. -/
lemma re_sub_mul_conj_pos {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ z) :
    0 < ((z - w) * (starRingEnd ℂ) z).re := by
  set a : ℂ := w * (starRingEnd ℂ) z with ha
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hre : ((z - w) * (starRingEnd ℂ) z).re = 1 - a.re := by
    rw [sub_mul, hzz]; simp [ha]
  rw [hre, sub_pos]
  by_contra h
  push_neg at h
  have hna : ‖a‖ ≤ 1 := by
    rw [ha, norm_mul, RCLike.norm_conj, hz, mul_one]; exact hw
  have h1 : a.re ≤ ‖a‖ := Complex.re_le_norm a
  have hre1 : a.re = 1 := le_antisymm (le_trans h1 hna) h
  have hn1 : ‖a‖ = 1 := le_antisymm hna (by rw [← hre1]; exact h1)
  have him : a.im = 0 := by
    have h2 := Complex.normSq_eq_norm_sq a
    rw [hn1, Complex.normSq_apply, hre1] at h2
    nlinarith [sq_nonneg a.im]
  have haa : a = 1 := by
    apply Complex.ext <;> simp [hre1, him]
  refine hne ?_
  have := congrArg (· * z) haa
  simp only [one_mul] at this
  rw [ha, mul_assoc, mul_comm ((starRingEnd ℂ) z) z, hzz, mul_one] at this
  exact this

/-! ### Brouwer's fixed point theorem in the complex plane -/

theorem brouwer_complex (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  have hball : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∈ closedBall (0 : ℂ) 1 := fun z h => by simpa using h
  -- Extend `f` to the whole plane using the radial retraction; the extension has no fixed point.
  set F : ℂ → ℂ := fun z => f (diskProj z) with hF
  have hFc : Continuous F :=
    hf.comp_continuous continuous_diskProj fun z => hball _ (norm_diskProj_le z)
  have hFnorm : ∀ z, ‖F z‖ ≤ 1 := fun z => by
    simpa using hmaps (hball _ (norm_diskProj_le z))
  have hFne : ∀ z, F z ≠ z := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := hz ▸ hFnorm z
    have hp : diskProj z = z := diskProj_eq_self hzn
    exact hcon z (hball _ hzn) (by rw [hF] at hz; simpa [hp] using hz)
  -- A continuous logarithm of the nonvanishing map `z ↦ z - F z`.
  obtain ⟨G, hG⟩ := exists_continuous_log ⟨fun z => z - F z, continuous_id.sub hFc⟩
    fun z => sub_ne_zero.2 fun h => hFne z h.symm
  simp only [ContinuousMap.coe_mk] at hG
  set c : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * t) with hc
  have hcnorm : ∀ t, ‖c t‖ = 1 := fun t => by simp [hc, Complex.norm_exp]
  set u : ℝ → ℝ := fun t => (G (c t) - 2 * Real.pi * Complex.I * t).im with hu
  have hucont : Continuous u :=
    Complex.continuous_im.comp ((G.continuous.comp (by fun_prop)).sub (by fun_prop))
  -- The imaginary part of the lift stays in the region where the cosine is positive.
  have hcos : ∀ t, 0 < Real.cos (u t) := by
    intro t
    have h1 : Complex.exp (G (c t) - 2 * Real.pi * Complex.I * t)
        = (c t - F (c t)) * (starRingEnd ℂ) (c t) := by
      rw [Complex.exp_sub, hG]
      rw [show Complex.exp (2 * Real.pi * Complex.I * t) = c t from rfl,
        div_eq_mul_inv, Complex.inv_eq_conj (hcnorm t)]
    have h2 : 0 < ((c t - F (c t)) * (starRingEnd ℂ) (c t)).re :=
      re_sub_mul_conj_pos (hcnorm t) (hFnorm _) (hFne _)
    rw [← h1, Complex.exp_re] at h2
    nlinarith [Real.exp_pos (G (c t) - 2 * Real.pi * Complex.I * t).re]
  -- But going once around the circle decreases that imaginary part by `2π`.
  have hc0 : c 0 = 1 := by simp [hc]
  have hc1 : c 1 = 1 := by simp [hc]
  have hu0 : u 0 = (G 1).im := by simp [hu, hc0]
  have hu1 : u 1 = (G 1).im - 2 * Real.pi := by simp [hu, hc1]
  have hmem : u 0 - Real.pi ∈ Icc (u 1) (u 0) := by
    constructor <;> [linarith [Real.pi_pos, hu0, hu1]; linarith [Real.pi_pos]]
  obtain ⟨t, -, hut⟩ := intermediate_value_Icc' zero_le_one hucont.continuousOn hmem
  have hneg := hcos t
  rw [hut, Real.cos_sub_pi] at hneg
  linarith [hcos 0]

end Brouwer2D

namespace Math

/-- **Brouwer's fixed point theorem in dimension two**: every continuous self-map of the
closed unit disk in the Euclidean plane has a fixed point. -/
theorem brouwer_2d
    (f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  classical
  -- Identify the Euclidean plane with `ℂ` by a linear isometry.
  set e := Complex.orthonormalBasisOneI.repr
  have hmemD : ∀ z : ℂ, ‖z‖ ≤ 1 → e z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    simpa [mem_closedBall_zero_iff] using hz
  set P : ℂ → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun z => ⟨e (Brouwer2D.diskProj z), hmemD _ (Brouwer2D.norm_diskProj_le z)⟩ with hP
  have hPc : Continuous P :=
    ((e.continuous.comp Brouwer2D.continuous_diskProj)).subtype_mk _
  set g : ℂ → ℂ := fun z => e.symm ((f (P z) : EuclideanSpace ℝ (Fin 2))) with hg
  have hgc : Continuous g :=
    e.symm.continuous.comp ((continuous_subtype_val.comp hf).comp hPc)
  have hgmaps : Set.MapsTo g (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro z _
    have h2 := (f (P z)).2
    rw [mem_closedBall_zero_iff] at h2 ⊢
    simpa [hg] using h2
  obtain ⟨z, hz, hfz⟩ := Brouwer2D.brouwer_complex g hgc.continuousOn hgmaps
  rw [mem_closedBall_zero_iff] at hz
  have hpz : P z = ⟨e z, hmemD z hz⟩ := by
    simp [hP, Brouwer2D.diskProj_eq_self hz]
  refine ⟨P z, Subtype.ext ?_⟩
  have : (f (P z) : EuclideanSpace ℝ (Fin 2)) = e z := by
    have := congrArg e hfz
    simpa [hg] using this
  rw [this, hpz]

/-- Brouwer's fixed point theorem in dimension two, stated for a continuous map of the plane
mapping the closed unit disk into itself. -/
theorem brouwer_2d_mapsTo (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f)
    (hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  obtain ⟨x, hx⟩ := brouwer_2d (fun x => ⟨f x, hmaps x.2⟩)
    ((hf.comp continuous_subtype_val).subtype_mk _)
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

end Math

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

