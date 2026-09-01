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

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- If `u` lies in the closed unit disk of `ℂ` and `u ≠ 1`, then `u.re < 1`. -/
lemma re_lt_one_of_norm_le_one {u : ℂ} (hu : ‖u‖ ≤ 1) (h1 : u ≠ 1) : u.re < 1 := by
  rcases lt_or_eq_of_le (le_trans (Complex.re_le_norm u) hu) with h | h
  · exact h
  · exfalso
    apply h1
    have hn : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
      have h2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
      have := Complex.normSq_eq_norm_sq u
      rw [Complex.normSq_apply] at this
      nlinarith [this]
    have him : u.im = 0 := by nlinarith
    apply Complex.ext <;> simp [h, him]

/-- There is no continuous `φ : ℝ → ℝ` whose cosine is everywhere positive and which
decreases by exactly `2π` between `0` and `2π`. -/
lemma no_continuous_arg_drop {ph : ℝ → ℝ} (hcont : Continuous ph)
    (hcos : ∀ t, 0 < Real.cos (ph t)) (hper : ph (2 * Real.pi) = ph 0 - 2 * Real.pi) : False := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set c := ph 0 with hc
  set n : ℤ := ⌊(c - Real.pi) / (2 * Real.pi)⌋ with hn
  set y : ℝ := Real.pi + (n : ℝ) * (2 * Real.pi) with hy
  have h2pi : (0:ℝ) < 2 * Real.pi := by linarith
  have hfl : (n : ℝ) ≤ (c - Real.pi) / (2 * Real.pi) := Int.floor_le _
  have hfl2 : (c - Real.pi) / (2 * Real.pi) < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hy_le : y ≤ c := by
    have := (le_div_iff₀ h2pi).mp hfl
    simp only [hy]
    linarith
  have hy_ge : c - 2 * Real.pi ≤ y := by
    have := (div_lt_iff₀ h2pi).mp hfl2
    simp only [hy]
    linarith
  have hsub := intermediate_value_Icc' (le_of_lt h2pi) hcont.continuousOn (f := ph)
  obtain ⟨t, -, ht⟩ := hsub (show y ∈ Set.Icc (ph (2 * Real.pi)) (ph 0) from
    Set.mem_Icc.mpr ⟨by rw [hper]; linarith, hy_le⟩)
  have hpos := hcos t
  rw [ht, hy, Real.cos_add_int_mul_two_pi, Real.cos_pi] at hpos
  linarith

/-- **Brouwer's fixed point theorem in dimension 2**, complex form: every continuous self-map
of the closed unit disk of `ℂ` has a fixed point. -/
theorem brouwer_2d_complex {f : ℂ → ℂ} (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : Set.MapsTo f (closedBall (0:ℂ) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0:ℂ) 1, f x = x := by
  by_contra hcon
  push_neg at hcon
  haveI : LocPathConnectedSpace (closedBall (0:ℂ) 1) :=
    Convex.locPathConnectedSpace ℂ (convex_closedBall (0:ℂ) 1)
  haveI : ContractibleSpace (closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).contractibleSpace ⟨0, by simp⟩
  -- `x ↦ x - f x` never vanishes on the disk
  have hne : ∀ x : closedBall (0:ℂ) 1, (x : ℂ) - f x ≠ 0 := fun x =>
    sub_ne_zero.mpr (Ne.symm (hcon x x.2))
  have hcs : Continuous (fun x : closedBall (0:ℂ) 1 => (x : ℂ) - f x) :=
    continuous_subtype_val.sub hf.restrict
  -- the normalized direction map from the disk to the circle
  set F : C(closedBall (0:ℂ) 1, Circle) :=
    ⟨fun x => ⟨((x : ℂ) - f x) / ‖(x : ℂ) - f x‖, by
        simp [Submonoid.unitSphere, hne x]⟩, by
      apply Continuous.subtype_mk
      exact hcs.div (Complex.continuous_ofReal.comp hcs.norm)
        (fun x => by simpa using hne x)⟩ with hF
  -- the disk is simply connected, so `F` lifts along the covering map `Circle.exp`
  obtain ⟨h, ⟨-, hlift⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F
    ⟨0, by simp⟩ ((F ⟨0, by simp⟩ : Circle) : ℂ).arg (Circle.exp_arg _)
  set zeta : C(ℝ, closedBall (0:ℂ) 1) :=
    ⟨fun t => ⟨Complex.exp (t * I), by
        simp [Complex.norm_exp_ofReal_mul_I]⟩, by
      apply Continuous.subtype_mk
      fun_prop⟩ with hzeta
  -- the lifted argument along the boundary circle, corrected by the angle
  set ph : ℝ → ℝ := fun t => h (zeta t) - t with hph
  have hphc : Continuous ph := (h.continuous.comp zeta.continuous).sub continuous_id
  have hcos : ∀ t, 0 < Real.cos (ph t) := by
    intro t
    set z : ℂ := Complex.exp ((t:ℝ) * I) with hzdef
    have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    have hzc : ((zeta t : closedBall (0:ℂ) 1) : ℂ) = z := rfl
    set w : ℂ := f (zeta t) with hwdef
    have hw : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp (hmaps (zeta t).2)
    have hrne : z - w ≠ 0 := by simpa [hzc] using hne (zeta t)
    have hr : 0 < ‖z - w‖ := norm_pos_iff.mpr hrne
    have hFz : (F (zeta t) : ℂ) = (z - w) / (‖z - w‖ : ℂ) := rfl
    have hlift' : Circle.exp (h (zeta t)) = F (zeta t) := congrFun hlift (zeta t)
    have hzz : z * (starRingEnd ℂ) z = 1 := by rw [Complex.mul_conj', hz1]; norm_num
    have hexp : Complex.exp ((ph t : ℝ) * I) = (1 - w * (starRingEnd ℂ) z) / (‖z - w‖ : ℂ) := by
      have h1 : ((ph t : ℝ) : ℂ) * I = ((h (zeta t) : ℝ) : ℂ) * I - ((t:ℝ):ℂ) * I := by
        simp only [hph]; push_cast; ring
      rw [h1, Complex.exp_sub, ← Circle.coe_exp, hlift', hFz, ← hzdef]
      have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz1; simp at hz1
      have hrc : ((‖z - w‖:ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
      field_simp
      linear_combination w * hzz
    have hcosv : Real.cos (ph t) = (1 - (w * (starRingEnd ℂ) z).re) / ‖z - w‖ := by
      rw [← Complex.exp_ofReal_mul_I_re (ph t), hexp, Complex.div_ofReal_re]
      simp
    rw [hcosv]
    apply div_pos _ hr
    have hu : ‖w * (starRingEnd ℂ) z‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj, hz1, mul_one]; exact hw
    have hune : w * (starRingEnd ℂ) z ≠ 1 := by
      intro hEq
      apply hrne
      have hwz : w = z := by linear_combination z * hEq - w * hzz
      simp [hwz]
    linarith [re_lt_one_of_norm_le_one hu hune]
  refine no_continuous_arg_drop hphc hcos ?_
  have hzper : zeta (2 * Real.pi) = zeta 0 := by
    apply Subtype.ext
    simp [hzeta]
  simp only [hph, hzper]
  ring

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
2-disk `{x ∈ ℝ² : ‖x‖ ≤ 1}` has a fixed point. -/
theorem brouwer_2d {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : Set.MapsTo f (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with he
  have hmem : ∀ z : ℂ,
      z ∈ closedBall (0:ℂ) 1 ↔ e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z
    simp [e.norm_map]
  have hmem' : ∀ y : EuclideanSpace ℝ (Fin 2),
      y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔ e.symm y ∈ closedBall (0:ℂ) 1 := by
    intro y
    rw [hmem (e.symm y)]
    simp
  set g : ℂ → ℂ := fun z => e.symm (f (e z)) with hg
  have hgc : ContinuousOn g (closedBall (0:ℂ) 1) := by
    apply e.symm.continuous.comp_continuousOn
    exact hf.comp e.continuous.continuousOn (fun z hz => (hmem z).mp hz)
  have hgm : Set.MapsTo g (closedBall (0:ℂ) 1) (closedBall 0 1) := fun z hz =>
    (hmem' _).mp (hmaps ((hmem z).mp hz))
  obtain ⟨x, hx, hfx⟩ := brouwer_2d_complex hgc hgm
  exact ⟨e x, (hmem x).mp hx, by simpa [hg] using congrArg e hfx⟩

/-- **Brouwer's fixed point theorem in dimension 2**, bundled form: every continuous self-map
of the closed 2-disk, viewed as a map of the subtype, has a fixed point. -/
theorem brouwer_2d_bundled
    (f : C(closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
          closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    ∃ x, f x = x := by
  classical
  set F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => if hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then (f ⟨y, hy⟩ : _) else 0
    with hF
  have hFc : ContinuousOn F (closedBall 0 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hr : (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).restrict F
        = fun y => (f y : EuclideanSpace ℝ (Fin 2)) := by
      funext y
      simp only [hF, Set.restrict_apply, dif_pos y.2, Subtype.coe_eta]
    rw [hr]
    exact continuous_subtype_val.comp f.continuous
  have hFm : Set.MapsTo F (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1) := by
    intro y hy
    simp only [hF, dif_pos hy]
    exact (f ⟨y, hy⟩).2
  obtain ⟨x, hx, hfx⟩ := brouwer_2d hFc hFm
  simp only [hF, dif_pos hx] at hfx
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

end Math

