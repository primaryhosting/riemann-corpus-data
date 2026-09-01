import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/
def scos : Spin → ℝ := Real.cos_periodic.lift

/-- The sine function on the circle. -/
def ssin : Spin → ℝ := Real.sin_periodic.lift

@[simp] lemma scos_coe (x : ℝ) : scos (x : Spin) = Real.cos x := Function.Periodic.lift_coe _ _

@[simp] lemma ssin_coe (x : ℝ) : ssin (x : Spin) = Real.sin x := Function.Periodic.lift_coe _ _

lemma continuous_scos : Continuous scos := by
  unfold scos Function.Periodic.lift
  exact continuous_coinduced_dom.mpr Real.continuous_cos

lemma continuous_ssin : Continuous ssin := by
  unfold ssin Function.Periodic.lift
  exact continuous_coinduced_dom.mpr Real.continuous_sin

lemma abs_scos_le_one (x : Spin) : |scos x| ≤ 1 := by
  induction x using QuotientAddGroup.induction_on with
  | H x => simpa using Real.abs_cos_le_one x

lemma abs_ssin_le_one (x : Spin) : |ssin x| ≤ 1 := by
  induction x using QuotientAddGroup.induction_on with
  | H x => simpa using Real.abs_sin_le_one x

lemma scos_le_one (x : Spin) : scos x ≤ 1 := (abs_le.1 (abs_scos_le_one x)).2

lemma scos_add_pi (a : Spin) : scos (a + ((Real.pi : ℝ) : Spin)) = -scos a := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
    rw [← AddCircle.coe_add, scos_coe, Real.cos_add_pi, scos_coe]

lemma ssin_add_pi (a : Spin) : ssin (a + ((Real.pi : ℝ) : Spin)) = -ssin a := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
    rw [← AddCircle.coe_add, ssin_coe, Real.sin_add_pi, ssin_coe]

/-- The key second-difference identity: shifting an angle by `±t` changes the cosine
by a second-order amount proportional to `1 - cos t`. -/
lemma scos_second_difference (a : Spin) (t : ℝ) :
    2 * scos a - scos (a + (t : Spin)) - scos (a - (t : Spin)) = 2 * scos a * (1 - Real.cos t) := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
    rw [← AddCircle.coe_add, ← AddCircle.coe_sub]
    simp only [scos_coe, Real.cos_add, Real.cos_sub]
    ring

/-- `1 - cos t ≤ t ^ 2 / 2`. -/
lemma one_sub_cos_le (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := t)
  linarith

end

end Phys

import RequestProject.Spin

/-!
# Gibbs measures on a finite product of circles, and the spin-wave estimate

For a finite index set `ι` we consider the configuration space `ι → Spin` of a classical
spin system, equipped with the (translation invariant) Haar measure, and the Gibbs
expectation associated with a continuous Hamiltonian `H` at inverse temperature `β`.

The main result `Phys.gibbs_shift_bound` is the quantitative version of the spin-wave
(Bogoliubov / relative entropy) argument: if the *second difference*
`H (θ + g) + H (θ - g) - 2 H θ` of the Hamiltonian along a deformation `g` is bounded
by `K`, then the Gibbs expectation of a bounded observable changes by at most
`‖F‖_∞ √(2βK)` when the configuration is shifted by `g`.
-/

namespace Phys

noncomputable section

open MeasureTheory

variable {ι : Type} [Fintype ι]

/-- The Boltzmann weight `exp (-β H θ)`. -/
def gWeight (β : ℝ) (H : (ι → Spin) → ℝ) (θ : ι → Spin) : ℝ := Real.exp (-β * H θ)

/-- The partition function `∫ exp (-β H)`. -/
def gPart (β : ℝ) (H : (ι → Spin) → ℝ) : ℝ := ∫ θ, gWeight β H θ

/-- The Gibbs expectation of an observable `F`. -/
def gAvg (β : ℝ) (H : (ι → Spin) → ℝ) (F : (ι → Spin) → ℝ) : ℝ :=
  (∫ θ, F θ * gWeight β H θ) / gPart β H

lemma torus_integrable {f : (ι → Spin) → ℝ} (hf : Continuous f) :
    Integrable f (volume : Measure (ι → Spin)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma volume_univ_pos : (0:ℝ) < ((volume : Measure (ι → Spin)) Set.univ).toReal := by
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  simpa using (Ne.symm (NeZero.ne' (volume : Measure (ι → Spin))))

omit [Fintype ι] in
lemma gWeight_pos (β : ℝ) (H : (ι → Spin) → ℝ) (θ : ι → Spin) : 0 < gWeight β H θ :=
  Real.exp_pos _

omit [Fintype ι] in
@[fun_prop]
lemma continuous_gWeight (β : ℝ) {H : (ι → Spin) → ℝ} (hH : Continuous H) :
    Continuous (gWeight β H) :=
  Real.continuous_exp.comp (continuous_const.mul hH)

lemma gPart_pos (β : ℝ) {H : (ι → Spin) → ℝ} (hH : Continuous H) : 0 < gPart β H := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := (ι → Spin))).exists_bound_of_continuousOn
    (hH.norm.continuousOn)
  have hbdd : ∀ θ : ι → Spin, Real.exp (-(|β| * M)) ≤ gWeight β H θ := by
    intro θ
    have h1 : |β * H θ| ≤ |β| * M := by
      rw [abs_mul]
      have := hM θ (Set.mem_univ θ)
      have hβ : (0:ℝ) ≤ |β| := abs_nonneg _
      exact mul_le_mul_of_nonneg_left (by simpa using this) hβ
    have h2 : -(|β| * M) ≤ -β * H θ := by
      have := abs_le.1 h1
      simp only [neg_mul]
      linarith [this.1]
    exact Real.exp_le_exp.2 h2
  have hint : Integrable (gWeight β H) (volume : Measure (ι → Spin)) :=
    torus_integrable (continuous_gWeight β hH)
  have hconst : Integrable (fun _ : ι → Spin => Real.exp (-(|β| * M)))
      (volume : Measure (ι → Spin)) := integrable_const _
  have := integral_mono hconst hint hbdd
  have hlow : (0:ℝ) < ∫ _ : ι → Spin, Real.exp (-(|β| * M)) := by
    rw [integral_const, smul_eq_mul]
    exact mul_pos volume_univ_pos (Real.exp_pos _)
  exact lt_of_lt_of_le hlow this

lemma gAvg_neg (β : ℝ) (H : (ι → Spin) → ℝ) (F : (ι → Spin) → ℝ) :
    gAvg β H (fun θ => -F θ) = -gAvg β H F := by
  unfold gAvg
  rw [← neg_div]
  congr 1
  rw [← integral_neg]
  congr 1 with θ
  ring

lemma integral_lin2 {f₁ f₂ : (ι → Spin) → ℝ}
    (h₁ : Integrable f₁ (volume : Measure (ι → Spin)))
    (h₂ : Integrable f₂ (volume : Measure (ι → Spin))) (a b : ℝ) :
    ∫ θ, (a * f₁ θ + b * f₂ θ) = a * (∫ θ, f₁ θ) + b * (∫ θ, f₂ θ) := by
  rw [integral_add (h₁.const_mul a) (h₂.const_mul b), integral_const_mul, integral_const_mul]

lemma integral_lin3 {f₁ f₂ f₃ : (ι → Spin) → ℝ}
    (h₁ : Integrable f₁ (volume : Measure (ι → Spin)))
    (h₂ : Integrable f₂ (volume : Measure (ι → Spin)))
    (h₃ : Integrable f₃ (volume : Measure (ι → Spin))) (a b c : ℝ) :
    ∫ θ, (a * f₁ θ + b * f₂ θ + c * f₃ θ)
      = a * (∫ θ, f₁ θ) + b * (∫ θ, f₂ θ) + c * (∫ θ, f₃ θ) := by
  have h : ∫ θ, ((1:ℝ) * (a * f₁ θ + b * f₂ θ) + c * f₃ θ)
      = 1 * (∫ θ, (a * f₁ θ + b * f₂ θ)) + c * (∫ θ, f₃ θ) :=
    integral_lin2 ((h₁.const_mul a).add (h₂.const_mul b)) h₃ 1 c
  simp only [one_mul] at h
  rw [h, integral_lin2 h₁ h₂ a b]

/-- **Spin-wave estimate.**  If the second difference of the Hamiltonian along the
deformation `g` is bounded by `K`, then shifting a bounded observable by `g` changes its
Gibbs expectation by at most `C √(2βK)`. -/
theorem gibbs_shift_bound (β : ℝ) (hβ : 0 ≤ β) (H : (ι → Spin) → ℝ) (hH : Continuous H)
    (F : (ι → Spin) → ℝ) (hF : Continuous F) (C : ℝ) (hC : ∀ θ, |F θ| ≤ C)
    (g : ι → Spin) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ θ, H (θ + g) + H (θ - g) - 2 * H θ ≤ K) :
    |gAvg β H (fun θ => F (θ + g)) - gAvg β H F| ≤ C * Real.sqrt (2 * β * K) := by
  classical
  -- notation
  have hZpos : 0 < gPart β H := gPart_pos β hH
  set Z : ℝ := gPart β H with hZdef
  set u : (ι → Spin) → ℝ := fun θ => Real.exp (-β * H (θ - g) / 2) with hudef
  set v : (ι → Spin) → ℝ := fun θ => Real.exp (-β * H θ / 2) with hvdef
  set p : (ι → Spin) → ℝ := fun θ => Real.exp (-β * (H (θ + g) + H θ) / 2) with hpdef
  -- continuity
  have hHm : Continuous fun θ : ι → Spin => H (θ - g) :=
    hH.comp (continuous_id.sub continuous_const)
  have hHp : Continuous fun θ : ι → Spin => H (θ + g) :=
    hH.comp (continuous_id.add continuous_const)
  have hcu : Continuous u := Real.continuous_exp.comp (by fun_prop)
  have hcv : Continuous v := Real.continuous_exp.comp (by fun_prop)
  have hcp : Continuous p := Real.continuous_exp.comp (by fun_prop)
  -- squares
  have hv2 : ∀ θ, v θ ^ 2 = gWeight β H θ := by
    intro θ; simp only [hvdef, gWeight, sq, ← Real.exp_add]; ring_nf
  have hu2 : ∀ θ, u θ ^ 2 = gWeight β H (θ - g) := by
    intro θ; simp only [hudef, gWeight, sq, ← Real.exp_add]; ring_nf
  have hupos : ∀ θ, 0 < u θ := fun θ => Real.exp_pos _
  have hvpos : ∀ θ, 0 < v θ := fun θ => Real.exp_pos _
  -- basic integrals
  have hIv2 : ∫ θ, v θ ^ 2 = Z := by
    rw [hZdef, gPart]; exact integral_congr_ae (Filter.Eventually.of_forall hv2)
  have hIu2 : ∫ θ, u θ ^ 2 = Z := by
    have h1 : ∫ θ, u θ ^ 2 = ∫ θ, gWeight β H (θ - g) :=
      integral_congr_ae (Filter.Eventually.of_forall hu2)
    have h2 : ∫ θ, gWeight β H (θ + (-g)) = ∫ θ, gWeight β H θ :=
      integral_add_right_eq_self (gWeight β H) (-g)
    rw [h1, hZdef, gPart, ← h2]
    congr 1 with θ
    rw [← sub_eq_add_neg]
  -- the symmetrized overlap
  set S : ℝ := ∫ θ, u θ * v θ with hSdef
  have hSp : S = ∫ θ, p θ := by
    have h2 : ∫ θ, (u (θ + g) * v (θ + g)) = ∫ θ, u θ * v θ :=
      integral_add_right_eq_self (fun θ => u θ * v θ) g
    have h3 : ∀ θ : ι → Spin, u (θ + g) * v (θ + g) = p θ := by
      intro θ
      simp only [hudef, hvdef, hpdef, add_sub_cancel_right, ← Real.exp_add]
      ring_nf
    rw [hSdef, ← h2, integral_congr_ae (Filter.Eventually.of_forall h3)]
  -- integrability
  have iu2 : Integrable (fun θ => u θ ^ 2) (volume : Measure (ι → Spin)) :=
    torus_integrable (by fun_prop)
  have iv2 : Integrable (fun θ => v θ ^ 2) (volume : Measure (ι → Spin)) :=
    torus_integrable (by fun_prop)
  have iuv : Integrable (fun θ => u θ * v θ) (volume : Measure (ι → Spin)) :=
    torus_integrable (by fun_prop)
  have ip : Integrable p (volume : Measure (ι → Spin)) := torus_integrable hcp
  -- lower bound on the overlap
  have hSlow : (2 - β * K / 2) * Z ≤ 2 * S := by
    have key : ∀ θ : ι → Spin, v θ ^ 2 * (2 - β * K / 2) ≤ u θ * v θ + p θ := by
      intro θ
      have e1 : u θ * v θ = v θ ^ 2 * Real.exp (-β * (H (θ - g) - H θ) / 2) := by
        simp only [hudef, hvdef, sq, ← Real.exp_add]; ring_nf
      have e2 : p θ = v θ ^ 2 * Real.exp (-β * (H (θ + g) - H θ) / 2) := by
        simp only [hpdef, hvdef, sq, ← Real.exp_add]; ring_nf
      have b1 : 1 + (-β * (H (θ - g) - H θ) / 2) ≤ Real.exp (-β * (H (θ - g) - H θ) / 2) := by
        have := Real.add_one_le_exp (-β * (H (θ - g) - H θ) / 2); linarith
      have b2 : 1 + (-β * (H (θ + g) - H θ) / 2) ≤ Real.exp (-β * (H (θ + g) - H θ) / 2) := by
        have := Real.add_one_le_exp (-β * (H (θ + g) - H θ) / 2); linarith
      have hvsq : 0 < v θ ^ 2 := pow_pos (hvpos θ) 2
      have hKθ := hK θ
      have hstep : (2 - β * K / 2) ≤
          (1 + (-β * (H (θ - g) - H θ) / 2)) + (1 + (-β * (H (θ + g) - H θ) / 2)) := by
        nlinarith [hβ, hKθ]
      calc v θ ^ 2 * (2 - β * K / 2)
          ≤ v θ ^ 2 * ((1 + (-β * (H (θ - g) - H θ) / 2)) +
              (1 + (-β * (H (θ + g) - H θ) / 2))) := by
            exact mul_le_mul_of_nonneg_left hstep (le_of_lt hvsq)
        _ ≤ v θ ^ 2 * (Real.exp (-β * (H (θ - g) - H θ) / 2) +
              Real.exp (-β * (H (θ + g) - H θ) / 2)) := by
            have := add_le_add b1 b2
            exact mul_le_mul_of_nonneg_left this (le_of_lt hvsq)
        _ = u θ * v θ + p θ := by rw [e1, e2]; ring
    have iL : Integrable (fun θ => v θ ^ 2 * (2 - β * K / 2))
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have iR : Integrable (fun θ => u θ * v θ + p θ)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have hmono := integral_mono iL iR key
    have hL : ∫ θ, v θ ^ 2 * (2 - β * K / 2) = (2 - β * K / 2) * Z := by
      rw [integral_mul_const, hIv2]; ring
    have hR : ∫ θ, (u θ * v θ + p θ) = 2 * S := by
      have := integral_lin2 iuv ip 1 1
      simp only [one_mul] at this
      rw [this, ← hSp, ← hSdef]; ring
    rw [hL, hR] at hmono
    exact hmono
  -- the overlap is at most Z
  have hSle : S ≤ Z := by
    have key : ∀ θ : ι → Spin, u θ * v θ ≤ (u θ ^ 2 + v θ ^ 2) / 2 := by
      intro θ; nlinarith [sq_nonneg (u θ - v θ)]
    have iR : Integrable (fun θ => (u θ ^ 2 + v θ ^ 2) / 2)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have hmono := integral_mono iuv iR key
    have hR : ∫ θ, (u θ ^ 2 + v θ ^ 2) / 2 = Z := by
      have h := integral_lin2 iu2 iv2 (1/2) (1/2)
      have h2 : ∀ θ : ι → Spin, (u θ ^ 2 + v θ ^ 2) / 2
          = (1/2 : ℝ) * u θ ^ 2 + (1/2 : ℝ) * v θ ^ 2 := by intro θ; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall h2), h, hIu2, hIv2]; ring
    rw [hR] at hmono
    exact hmono
  -- the L¹ distance of the two Boltzmann weights
  set D : ℝ := ∫ θ, |u θ ^ 2 - v θ ^ 2| with hDdef
  have hDnonneg : 0 ≤ D := integral_nonneg (fun θ => abs_nonneg _)
  have hDlam : ∀ lam : ℝ, 0 < lam →
      D ≤ (1 / (2 * lam)) * (2 * Z - 2 * S) + (lam / 2) * (2 * Z + 2 * S) := by
    intro lam hlam
    have key : ∀ θ : ι → Spin, |u θ ^ 2 - v θ ^ 2| ≤
        (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2 := by
      intro θ
      have hpos : 0 < u θ + v θ := add_pos (hupos θ) (hvpos θ)
      have habs : |u θ ^ 2 - v θ ^ 2| = |u θ - v θ| * (u θ + v θ) := by
        rw [← abs_of_pos hpos, ← abs_mul]
        congr 1
        ring
      rw [habs, ← sub_nonneg]
      have hA2 : |u θ - v θ| ^ 2 = (u θ - v θ) ^ 2 := sq_abs _
      have expand : (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2
          - |u θ - v θ| * (u θ + v θ)
          = (1 / (2 * lam)) * (|u θ - v θ| - lam * (u θ + v θ)) ^ 2 := by
        rw [← hA2]
        field_simp
        ring
      rw [expand]
      positivity
    have iabs : Integrable (fun θ => |u θ ^ 2 - v θ ^ 2|) (volume : Measure (ι → Spin)) :=
      torus_integrable (by fun_prop)
    have irhs : Integrable
        (fun θ => (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have hmono := integral_mono iabs irhs key
    have hexp : ∀ θ : ι → Spin,
        (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2
        = (1 / (2 * lam) + lam / 2) * u θ ^ 2 + (1 / (2 * lam) + lam / 2) * v θ ^ 2
          + (lam - 1 / lam) * (u θ * v θ) := by
      intro θ
      field_simp
      ring
    have hRint : ∫ θ, ((1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2)
        = (1 / (2 * lam) + lam / 2) * Z + (1 / (2 * lam) + lam / 2) * Z
          + (lam - 1 / lam) * S := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
        integral_lin3 iu2 iv2 iuv _ _ _, hIu2, hIv2, ← hSdef]
    rw [hRint] at hmono
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have : (1 / (2 * lam) + lam / 2) * Z + (1 / (2 * lam) + lam / 2) * Z + (lam - 1 / lam) * S
        = (1 / (2 * lam)) * (2 * Z - 2 * S) + (lam / 2) * (2 * Z + 2 * S) := by
      field_simp
      ring
    rw [this] at hmono
    exact hmono
  -- the small-difference bound
  have hsmall : 2 * Z - 2 * S ≤ β * K / 2 * Z := by nlinarith [hSlow, hZpos]
  set c : ℝ := Real.sqrt (2 * β * K) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 2 * β * K := Real.sq_sqrt (by positivity)
  have hDc : D ≤ c * Z := by
    rcases eq_or_lt_of_le hc0 with hc | hc
    · -- c = 0, hence β K = 0 and the two weights agree
      have hbk : β * K = 0 := by nlinarith [hc2, hc.symm]
      have hzero : 2 * Z - 2 * S ≤ 0 := by rw [hbk] at hsmall; linarith
      have hD0 : D ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have hlam := hDlam (D / (4 * Z)) (by positivity)
        have hnn : (0:ℝ) ≤ 1 / (2 * (D / (4 * Z))) := by positivity
        have h1 : (1 / (2 * (D / (4 * Z)))) * (2 * Z - 2 * S) ≤ 0 := by nlinarith
        have hSZ : 2 * Z + 2 * S ≤ 4 * Z := by linarith
        have h3 : (D / (4 * Z)) / 2 * (2 * Z + 2 * S) ≤ (D / (4 * Z)) / 2 * (4 * Z) :=
          mul_le_mul_of_nonneg_left hSZ (by positivity)
        have h4 : (D / (4 * Z)) / 2 * (4 * Z) = D / 2 := by field_simp
        linarith
      have : c * Z = 0 := by rw [← hc]; ring
      linarith
    · have hcne : c ≠ 0 := ne_of_gt hc
      have hlam := hDlam (c / 4) (by positivity)
      have hSZ : 2 * Z + 2 * S ≤ 4 * Z := by linarith
      have e1 : (1 / (2 * (c / 4))) * (2 * Z - 2 * S) ≤ (2 / c) * (β * K / 2 * Z) := by
        have : (1 : ℝ) / (2 * (c / 4)) = 2 / c := by field_simp; norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      have e2 : (c / 4) / 2 * (2 * Z + 2 * S) ≤ (c / 4) / 2 * (4 * Z) :=
        mul_le_mul_of_nonneg_left hSZ (by positivity)
      have e3 : (2 / c) * (β * K / 2 * Z) = c * Z / 2 := by
        have hbk : β * K = c ^ 2 / 2 := by rw [hc2]; ring
        rw [hbk]
        field_simp
      have e4 : (c / 4) / 2 * (4 * Z) = c * Z / 2 := by ring
      linarith
  -- transfer to the observable
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 0))
  have hshift : ∫ θ, F (θ + g) * gWeight β H θ = ∫ θ, F θ * gWeight β H (θ - g) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (ι → Spin)))
      (fun θ => F θ * gWeight β H (θ - g)) g
    rw [← h]
    congr 1 with θ
    simp [add_sub_cancel_right]
  have hnum : |(∫ θ, F (θ + g) * gWeight β H θ) - ∫ θ, F θ * gWeight β H θ| ≤ C * D := by
    rw [hshift]
    have iL : Integrable (fun θ => F θ * gWeight β H (θ - g)) (volume : Measure (ι → Spin)) :=
      torus_integrable (hF.mul (Real.continuous_exp.comp (by fun_prop)))
    have iR : Integrable (fun θ => F θ * gWeight β H θ) (volume : Measure (ι → Spin)) :=
      torus_integrable (hF.mul (continuous_gWeight β hH))
    have hdiff : (∫ θ, F θ * gWeight β H (θ - g)) - ∫ θ, F θ * gWeight β H θ
        = ∫ θ, F θ * (gWeight β H (θ - g) - gWeight β H θ) := by
      rw [← integral_sub iL iR]
      congr 1 with θ
      ring
    rw [hdiff]
    have hbnd : ∀ θ : ι → Spin, |F θ * (gWeight β H (θ - g) - gWeight β H θ)|
        ≤ C * |u θ ^ 2 - v θ ^ 2| := by
      intro θ
      rw [abs_mul, hu2 θ, hv2 θ]
      exact mul_le_mul_of_nonneg_right (hC θ) (abs_nonneg _)
    have iabs2 : Integrable (fun θ => C * |u θ ^ 2 - v θ ^ 2|)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    calc |∫ θ, F θ * (gWeight β H (θ - g) - gWeight β H θ)|
        ≤ ∫ θ, |F θ * (gWeight β H (θ - g) - gWeight β H θ)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ θ, C * |u θ ^ 2 - v θ ^ 2| := by
          refine integral_mono ?_ iabs2 hbnd
          exact torus_integrable (by fun_prop)
      _ = C * D := by rw [integral_const_mul, hDdef]
  -- conclude
  have hgoal : |gAvg β H (fun θ => F (θ + g)) - gAvg β H F| = |(∫ θ, F (θ + g) * gWeight β H θ) -
      ∫ θ, F θ * gWeight β H θ| / Z := by
    unfold gAvg
    rw [← hZdef, div_sub_div_same, abs_div, abs_of_pos hZpos]
  rw [hgoal]
  rw [div_le_iff₀ hZpos]
  calc |(∫ θ, F (θ + g) * gWeight β H θ) - ∫ θ, F θ * gWeight β H θ| ≤ C * D := hnum
    _ ≤ C * (c * Z) := by exact mul_le_mul_of_nonneg_left hDc hCnn
    _ = C * c * Z := by ring

end

end Phys

/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Spin
import RequestProject.Gibbs
import RequestProject.Lattice

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
## The Mermin–Wagner theorem

We consider the classical XY model on the lattice `ℤ^d`: spins take values in the circle
`Spin = ℝ / 2πℤ`, the spins inside the box `box d N` fluctuate, the spins outside are
frozen to an arbitrary boundary condition `τ`, and the (nearest neighbour, ferromagnetic)
Hamiltonian is

`xyHam N τ θ = ∑_{x, i} (1 - cos (θ x - θ (x + e i)))`,

the sum ranging over the bonds `{x, x + e i}` with `x` in the box of radius `N + 1`.  This
includes every bond meeting the box of radius `N` (the fluctuating spins), together with
finitely many bonds joining two frozen spins, which contribute an additive constant and
hence do not affect the Gibbs measure.  The Gibbs expectation at inverse
temperature `β > 0` (i.e. at temperature `T = 1/β > 0`) is `gAvg β (xyHam N τ)`, and the
two components of the magnetisation at the origin are `magCos` and `magSin`.

The theorem `Phys.mermin_wagner` states that in dimension `d ≤ 2` and at any positive
temperature the magnetisation at the origin is arbitrarily small in absolute value, for
all sufficiently large boxes and *uniformly in the boundary condition*: the continuous
`O(2)` symmetry of the model is not spontaneously broken.

The proof is the spin-wave (Bogoliubov) argument: a slowly varying rotation of the spins,
equal to `π` at the origin and vanishing outside a large box, costs an energy of order
`1 / log R`, which vanishes in dimension `d ≤ 2`; by `Phys.gibbs_shift_bound` this forces
the magnetisation to be equal to its own opposite, up to an arbitrarily small error.
-/

namespace Phys

noncomputable section

open MeasureTheory Finset

variable {d : ℕ}

/-- Configurations of the spins in the box of radius `N`. -/
abbrev BoxCfg (d N : ℕ) := {x : Site d // x ∈ box d N} → Spin

/-- Extend a configuration in the box by the boundary condition `τ` outside the box. -/
def extend (N : ℕ) (τ : Site d → Spin) (θ : BoxCfg d N) : Site d → Spin :=
  fun x => if h : x ∈ box d N then θ ⟨x, h⟩ else τ x

/-- The XY Hamiltonian: the sum of `1 - cos (θ x - θ y)` over all nearest-neighbour bonds
meeting the box of radius `N`. -/
def xyHam (N : ℕ) (τ : Site d → Spin) (θ : BoxCfg d N) : ℝ :=
  ∑ x ∈ box d (N + 1), ∑ i : Fin d, (1 - scos (extend N τ θ x - extend N τ θ (x + unitVec i)))

/-- First component of the magnetisation at the origin. -/
def magCos (β : ℝ) (N : ℕ) (τ : Site d → Spin) : ℝ :=
  gAvg β (xyHam N τ) (fun θ => scos (extend N τ θ (0 : Site d)))

/-- Second component of the magnetisation at the origin. -/
def magSin (β : ℝ) (N : ℕ) (τ : Site d → Spin) : ℝ :=
  gAvg β (xyHam N τ) (fun θ => ssin (extend N τ θ (0 : Site d)))

/-- The spin-wave shift associated with a profile `f`. -/
def shiftOf (N : ℕ) (f : Site d → ℝ) : BoxCfg d N := fun y => ((f y : ℝ) : Spin)

lemma continuous_extend_apply (N : ℕ) (τ : Site d → Spin) (x : Site d) :
    Continuous fun θ : BoxCfg d N => extend N τ θ x := by
  unfold extend
  by_cases h : x ∈ box d N
  · simp only [h, dif_pos]
    exact continuous_apply _
  · simp only [h, dif_neg, not_false_iff]
    exact continuous_const

lemma continuous_xyHam (N : ℕ) (τ : Site d → Spin) : Continuous (xyHam N τ) := by
  unfold xyHam
  refine continuous_finset_sum _ (fun x _ => continuous_finset_sum _ (fun i _ => ?_))
  exact continuous_const.sub
    (continuous_scos.comp ((continuous_extend_apply N τ x).sub (continuous_extend_apply N τ _)))

lemma extend_add_shift (N : ℕ) (τ : Site d → Spin) (f : Site d → ℝ)
    (hsupp : ∀ x, x ∉ box d N → f x = 0) (θ : BoxCfg d N) (x : Site d) :
    extend N τ (θ + shiftOf N f) x = extend N τ θ x + ((f x : ℝ) : Spin) := by
  unfold extend shiftOf
  by_cases h : x ∈ box d N
  · simp [h]
  · simp [h, hsupp x h]

lemma extend_sub_shift (N : ℕ) (τ : Site d → Spin) (f : Site d → ℝ)
    (hsupp : ∀ x, x ∉ box d N → f x = 0) (θ : BoxCfg d N) (x : Site d) :
    extend N τ (θ - shiftOf N f) x = extend N τ θ x - ((f x : ℝ) : Spin) := by
  unfold extend shiftOf
  by_cases h : x ∈ box d N
  · simp [h]
  · simp [h, hsupp x h]

lemma sum_comb_le {α : Type} {s : Finset α} (F₁ F₂ F₃ G : α → ℝ)
    (h : ∀ a ∈ s, F₁ a + F₂ a - 2 * F₃ a ≤ G a) :
    (∑ a ∈ s, F₁ a) + (∑ a ∈ s, F₂ a) - 2 * (∑ a ∈ s, F₃ a) ≤ ∑ a ∈ s, G a := by
  have hEq : (∑ a ∈ s, F₁ a) + (∑ a ∈ s, F₂ a) - 2 * (∑ a ∈ s, F₃ a)
      = ∑ a ∈ s, (F₁ a + F₂ a - 2 * F₃ a) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hEq]
  exact Finset.sum_le_sum h

/-- The energy cost of a spin wave is at most its Dirichlet energy. -/
lemma xyHam_second_diff (N : ℕ) (τ : Site d → Spin) (f : Site d → ℝ)
    (hsupp : ∀ x, x ∉ box d N → f x = 0) (θ : BoxCfg d N) :
    xyHam N τ (θ + shiftOf N f) + xyHam N τ (θ - shiftOf N f) - 2 * xyHam N τ θ
      ≤ ∑ x ∈ box d (N + 1), ∑ i : Fin d, (f x - f (x + unitVec i)) ^ 2 := by
  unfold xyHam
  refine sum_comb_le _ _ _ _ (fun x _ => ?_)
  refine sum_comb_le _ _ _ _ (fun i _ => ?_)
  set A : Spin := extend N τ θ x - extend N τ θ (x + unitVec i) with hA
  set t : ℝ := f x - f (x + unitVec i) with ht
  have hplus : extend N τ (θ + shiftOf N f) x - extend N τ (θ + shiftOf N f) (x + unitVec i)
      = A + (t : Spin) := by
    rw [extend_add_shift N τ f hsupp θ x, extend_add_shift N τ f hsupp θ (x + unitVec i), hA, ht,
      AddCircle.coe_sub]
    abel
  have hminus : extend N τ (θ - shiftOf N f) x - extend N τ (θ - shiftOf N f) (x + unitVec i)
      = A - (t : Spin) := by
    rw [extend_sub_shift N τ f hsupp θ x, extend_sub_shift N τ f hsupp θ (x + unitVec i), hA, ht,
      AddCircle.coe_sub]
    abel
  rw [hplus, hminus]
  have hid := scos_second_difference A t
  have hcos : 0 ≤ 1 - Real.cos t := by
    have := Real.cos_le_one t; linarith
  have hle : 2 * scos A * (1 - Real.cos t) ≤ 2 * (1 - Real.cos t) := by
    have h1 : scos A ≤ 1 := scos_le_one A
    nlinarith
  have hquad : 2 * (1 - Real.cos t) ≤ t ^ 2 := by
    have := one_sub_cos_le t; linarith
  have : (1 - scos (A + (t : Spin))) + (1 - scos (A - (t : Spin))) - 2 * (1 - scos A)
      = 2 * scos A - scos (A + (t : Spin)) - scos (A - (t : Spin)) := by ring
  rw [this, hid]
  linarith

/-- **Mermin–Wagner theorem.**  In dimension `d ≤ 2` and at any positive temperature
`T = 1/β > 0` the continuous rotation symmetry of the XY model is not spontaneously
broken: for every `ε > 0` there is a radius `R` such that for every box of radius
`N ≥ R` and every boundary condition `τ` outside that box, both components of the Gibbs
magnetisation at the origin are smaller than `ε` in absolute value. -/
theorem mermin_wagner {d : ℕ} (hd : d ≤ 2) {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ N, R ≤ N → ∀ τ : Site d → Spin,
      |magCos β N τ| < ε ∧ |magSin β N τ| < ε := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨R, hR1, hR⟩ := dirichletEnergy_small (d := d) hd
    (ε := 2 * ε ^ 2 / (β * Real.pi ^ 2)) (by positivity)
  refine ⟨R, fun N hN τ => ?_⟩
  -- the spin-wave profile
  set f : Site d → ℝ := fun x => Real.pi * spinWave R x with hf
  have hsupp : ∀ x, x ∉ box d N → f x = 0 := by
    intro x hx
    have hxn : N < snorm x := by
      by_contra hcon
      exact hx (mem_box_iff.2 (by omega))
    have : spinWave R x = 0 := spinWave_eq_zero_of_le hR1 (by omega)
    simp [hf, this]
  set g : BoxCfg d N := shiftOf N f with hg
  -- the energy cost of the spin wave
  set K : ℝ := ∑ x ∈ box d (N + 1), ∑ i : Fin d, (f x - f (x + unitVec i)) ^ 2 with hK
  have hKeq : K = Real.pi ^ 2 * dirichletEnergy (d := d) R N := by
    rw [hK, dirichletEnergy, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf]
    ring
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hEsmall : dirichletEnergy (d := d) R N < 2 * ε ^ 2 / (β * Real.pi ^ 2) := hR N hN
  have hKsmall : 2 * β * K < 4 * ε ^ 2 := by
    rw [hKeq]
    have h1 : Real.pi ^ 2 * dirichletEnergy (d := d) R N
        < Real.pi ^ 2 * (2 * ε ^ 2 / (β * Real.pi ^ 2)) := by
      exact mul_lt_mul_of_pos_left hEsmall (by positivity)
    have h2 : Real.pi ^ 2 * (2 * ε ^ 2 / (β * Real.pi ^ 2)) = 2 * ε ^ 2 / β := by
      field_simp
    rw [h2] at h1
    have h3 : 2 * β * (Real.pi ^ 2 * dirichletEnergy (d := d) R N) < 2 * β * (2 * ε ^ 2 / β) := by
      exact mul_lt_mul_of_pos_left h1 (by positivity)
    have h4 : 2 * β * (2 * ε ^ 2 / β) = 4 * ε ^ 2 := by field_simp; ring
    linarith
  have hsqrt : Real.sqrt (2 * β * K) < 2 * ε := by
    have : Real.sqrt (2 * β * K) < Real.sqrt (4 * ε ^ 2) := by
      apply Real.sqrt_lt_sqrt (by positivity) hKsmall
    have h4 : Real.sqrt (4 * ε ^ 2) = 2 * ε := by
      rw [show (4:ℝ) * ε ^ 2 = (2 * ε) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith [this, h4.le, h4.ge]
  have hcost : ∀ θ : BoxCfg d N,
      xyHam N τ (θ + g) + xyHam N τ (θ - g) - 2 * xyHam N τ θ ≤ K :=
    fun θ => xyHam_second_diff N τ f hsupp θ
  have hf0 : f (0 : Site d) = Real.pi := by simp [hf, spinWave_origin]
  -- the key identity: the spin wave rotates the spin at the origin by π
  have hrot : ∀ θ : BoxCfg d N, extend N τ (θ + g) (0 : Site d)
      = extend N τ θ (0 : Site d) + ((Real.pi : ℝ) : Spin) := by
    intro θ
    rw [hg, extend_add_shift N τ f hsupp θ 0, hf0]
  constructor
  · -- cosine component
    have hbound := gibbs_shift_bound β hβ.le (xyHam N τ) (continuous_xyHam N τ)
      (fun θ => scos (extend N τ θ (0 : Site d)))
      (continuous_scos.comp (continuous_extend_apply N τ 0)) 1
      (fun θ => abs_scos_le_one _) g K hK0 hcost
    have hneg : (fun θ : BoxCfg d N => scos (extend N τ (θ + g) (0 : Site d)))
        = fun θ : BoxCfg d N => -scos (extend N τ θ (0 : Site d)) := by
      funext θ
      rw [hrot θ, scos_add_pi]
    rw [hneg, gAvg_neg] at hbound
    have : |(-magCos β N τ) - magCos β N τ| ≤ 1 * Real.sqrt (2 * β * K) := hbound
    have h2 : 2 * |magCos β N τ| ≤ Real.sqrt (2 * β * K) := by
      have habs : |(-magCos β N τ) - magCos β N τ| = 2 * |magCos β N τ| := by
        rw [show (-magCos β N τ) - magCos β N τ = -(2 * magCos β N τ) by ring, abs_neg, abs_mul]
        norm_num
      linarith [habs.symm ▸ this]
    linarith
  · -- sine component
    have hbound := gibbs_shift_bound β hβ.le (xyHam N τ) (continuous_xyHam N τ)
      (fun θ => ssin (extend N τ θ (0 : Site d)))
      (continuous_ssin.comp (continuous_extend_apply N τ 0)) 1
      (fun θ => abs_ssin_le_one _) g K hK0 hcost
    have hneg : (fun θ : BoxCfg d N => ssin (extend N τ (θ + g) (0 : Site d)))
        = fun θ : BoxCfg d N => -ssin (extend N τ θ (0 : Site d)) := by
      funext θ
      rw [hrot θ, ssin_add_pi]
    rw [hneg, gAvg_neg] at hbound
    have : |(-magSin β N τ) - magSin β N τ| ≤ 1 * Real.sqrt (2 * β * K) := hbound
    have h2 : 2 * |magSin β N τ| ≤ Real.sqrt (2 * β * K) := by
      have habs : |(-magSin β N τ) - magSin β N τ| = 2 * |magSin β N τ| := by
        rw [show (-magSin β N τ) - magSin β N τ = -(2 * magSin β N τ) by ring, abs_neg, abs_mul]
        norm_num
      linarith [habs.symm ▸ this]
    linarith

end

end Phys

import Mathlib

/-!
# The lattice `ℤ^d`, spin waves, and the Dirichlet energy in dimension `d ≤ 2`

This file contains the geometric heart of the Mermin–Wagner theorem: in dimension
`d ≤ 2` there are "spin waves", i.e. functions equal to `1` at the origin and vanishing
outside a finite box, whose Dirichlet energy is arbitrarily small.  (This is the lattice
counterpart of the recurrence of the simple random walk in dimensions `≤ 2`.)

The spin wave used is the logarithmic profile
`f R x = max 0 (1 - log (1 + ‖x‖) / log (1 + R))`, whose Dirichlet energy is `O(1 / log R)`.
-/

namespace Phys

noncomputable section

open Finset

variable {d : ℕ}

/-- The sites of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- The sup-norm of a lattice site. -/
def snorm (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The box of radius `N` around the origin. -/
def box (d N : ℕ) : Finset (Site d) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- The `i`-th lattice unit vector. -/
def unitVec (i : Fin d) : Site d := Pi.single i 1

/-- The logarithmic spin wave of range `R`. -/
def spinWave (R : ℕ) (x : Site d) : ℝ :=
  max 0 (1 - Real.log (1 + (snorm x : ℝ)) / Real.log (1 + (R : ℝ)))

/-- The Dirichlet energy of the spin wave, computed over all bonds of the box of
radius `N + 1`. -/
def dirichletEnergy (R N : ℕ) : ℝ :=
  ∑ x ∈ box d (N + 1), ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2

/-! ### Basic facts about the box and the sup-norm -/

lemma mem_box_iff {N : ℕ} {x : Site d} : x ∈ box d N ↔ snorm x ≤ N := by
  classical
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, snorm, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]
  constructor
  · intro h i
    have := h i
    omega
  · intro h i
    have := h i
    omega

lemma box_subset {N M : ℕ} (h : N ≤ M) : box d N ⊆ box d M := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  omega

lemma zero_mem_box (N : ℕ) : (0 : Site d) ∈ box d N := by
  rw [mem_box_iff]
  simp [snorm]

lemma card_box (N : ℕ) : (box d N).card = (2 * N + 1) ^ d := by
  classical
  simp only [box, Fintype.card_piFinset, Int.card_Icc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

lemma snorm_le_snorm_add_unit (x : Site d) (i : Fin d) :
    snorm x ≤ snorm (x + unitVec i) + 1 := by
  classical
  refine Finset.sup_le ?_
  intro j _
  have h1 : (x + unitVec i) j = x j + (if j = i then 1 else 0) := by
    simp [unitVec, Pi.single_apply, eq_comm]
  have h2 : ((x + unitVec i) j).natAbs ≤ snorm (x + unitVec i) :=
    Finset.le_sup (f := fun j => ((x + unitVec i) j).natAbs) (Finset.mem_univ j)
  by_cases hj : j = i
  · have h1' : (x + unitVec i) j = x j + 1 := by rw [h1]; simp [hj]
    rw [h1'] at h2
    omega
  · have h1' : (x + unitVec i) j = x j := by rw [h1]; simp [hj]
    rw [h1'] at h2
    omega

lemma snorm_add_unit_le (x : Site d) (i : Fin d) :
    snorm (x + unitVec i) ≤ snorm x + 1 := by
  classical
  refine Finset.sup_le ?_
  intro j _
  have h1 : (x + unitVec i) j = x j + (if j = i then 1 else 0) := by
    simp [unitVec, Pi.single_apply, eq_comm]
  have h2 : (x j).natAbs ≤ snorm x :=
    Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ j)
  by_cases hj : j = i
  · have h1' : (x + unitVec i) j = x j + 1 := by rw [h1]; simp [hj]
    rw [h1']
    omega
  · have h1' : (x + unitVec i) j = x j := by rw [h1]; simp [hj]
    rw [h1']
    omega

/-! ### Basic facts about the spin wave -/

lemma spinWave_nonneg (R : ℕ) (x : Site d) : 0 ≤ spinWave R x := le_max_left _ _

lemma spinWave_le_one (R : ℕ) (x : Site d) : spinWave R x ≤ 1 := by
  unfold spinWave
  refine max_le (by norm_num) ?_
  have h1 : (0:ℝ) ≤ Real.log (1 + (snorm x : ℝ)) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (snorm x : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : (0:ℝ) ≤ Real.log (1 + (R : ℝ)) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    linarith
  have : 0 ≤ Real.log (1 + (snorm x : ℝ)) / Real.log (1 + (R : ℝ)) := div_nonneg h1 h2
  linarith

lemma spinWave_origin (R : ℕ) : spinWave R (0 : Site d) = 1 := by
  have h : snorm (0 : Site d) = 0 := by simp [snorm]
  simp [spinWave, h]

lemma spinWave_eq_zero_of_le {R : ℕ} (hR : 1 ≤ R) {x : Site d} (hx : R ≤ snorm x) :
    spinWave R x = 0 := by
  have hlogpos : 0 < Real.log (1 + (R : ℝ)) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hmono : Real.log (1 + (R : ℝ)) ≤ Real.log (1 + (snorm x : ℝ)) := by
    apply Real.log_le_log (by positivity)
    have : (R:ℝ) ≤ (snorm x : ℝ) := by exact_mod_cast hx
    linarith
  have h1 : 1 ≤ Real.log (1 + (snorm x : ℝ)) / Real.log (1 + (R : ℝ)) :=
    (one_le_div hlogpos).2 hmono
  simp only [spinWave, max_eq_left_iff]
  linarith

/-! ### The energy estimate in dimension `d ≤ 2` -/

/-- An elementary logarithm step estimate: `log (1+b) - log (1+a) ≤ 1/(1+a)` for `b ≤ a+1`. -/
lemma log_step_bound (a b : ℕ) (hb : b ≤ a + 1) :
    Real.log (1 + (b:ℝ)) - Real.log (1 + (a:ℝ)) ≤ 1 / (1 + (a:ℝ)) := by
  have hpos : (0:ℝ) < 1 + (a:ℝ) := by positivity
  have hbpos : (0:ℝ) < 1 + (b:ℝ) := by positivity
  have hlog : Real.log (1 + (b:ℝ)) - Real.log (1 + (a:ℝ))
      = Real.log ((1 + (b:ℝ)) / (1 + (a:ℝ))) := (Real.log_div (ne_of_gt hbpos) (ne_of_gt hpos)).symm
  rw [hlog]
  have h2 := Real.log_le_sub_one_of_pos (x := (1 + (b:ℝ)) / (1 + (a:ℝ))) (by positivity)
  have hb' : (b:ℝ) ≤ (a:ℝ) + 1 := by exact_mod_cast hb
  have h3 : (1 + (b:ℝ)) / (1 + (a:ℝ)) - 1 ≤ 1 / (1 + (a:ℝ)) := by
    rw [← sub_nonpos]
    have heq : (1 + (b:ℝ)) / (1 + (a:ℝ)) - 1 - 1 / (1 + (a:ℝ))
        = ((b:ℝ) - (a:ℝ) - 1) / (1 + (a:ℝ)) := by field_simp; ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
  linarith

/-- Gradient bound for the logarithmic profile. -/
lemma spinWave_grad_bound {R : ℕ} (hR : 1 ≤ R) (x : Site d) (i : Fin d) :
    |spinWave R x - spinWave R (x + unitVec i)|
      ≤ 1 / ((max (snorm x : ℝ) 1) * Real.log (1 + (R : ℝ))) := by
  have hL : 0 < Real.log (1 + (R : ℝ)) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  set r : ℕ := snorm x with hr
  set r' : ℕ := snorm (x + unitVec i) with hr'
  have h1 : r ≤ r' + 1 := snorm_le_snorm_add_unit x i
  have h2 : r' ≤ r + 1 := snorm_add_unit_le x i
  have hmax : |spinWave R x - spinWave R (x + unitVec i)|
      ≤ |Real.log (1 + (r':ℝ)) - Real.log (1 + (r:ℝ))| / Real.log (1 + (R:ℝ)) := by
    unfold spinWave
    rw [← hr, ← hr', max_comm 0 _, max_comm 0 _]
    refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
    apply le_of_eq
    rw [show (1 - Real.log (1 + (r:ℝ)) / Real.log (1 + (R:ℝ)))
        - (1 - Real.log (1 + (r':ℝ)) / Real.log (1 + (R:ℝ)))
        = (Real.log (1 + (r':ℝ)) - Real.log (1 + (r:ℝ))) / Real.log (1 + (R:ℝ)) from by ring,
      abs_div, abs_of_pos hL]
  refine le_trans hmax ?_
  have hkey : |Real.log (1 + (r':ℝ)) - Real.log (1 + (r:ℝ))| ≤ 1 / (max (r:ℝ) 1) := by
    rcases le_total r r' with hle | hle
    · have hmono : Real.log (1 + (r:ℝ)) ≤ Real.log (1 + (r':ℝ)) := by
        apply Real.log_le_log (by positivity)
        have : (r:ℝ) ≤ (r':ℝ) := by exact_mod_cast hle
        linarith
      rw [abs_of_nonneg (by linarith)]
      refine le_trans (log_step_bound r r' h2) ?_
      refine one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ?_
      rcases le_total (r:ℝ) 1 with h | h
      · rw [max_eq_right h]
        have : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _
        linarith
      · rw [max_eq_left h]; linarith
    · have hmono : Real.log (1 + (r':ℝ)) ≤ Real.log (1 + (r:ℝ)) := by
        apply Real.log_le_log (by positivity)
        have : (r':ℝ) ≤ (r:ℝ) := by exact_mod_cast hle
        linarith
      rw [abs_of_nonpos (by linarith), neg_sub]
      refine le_trans (log_step_bound r' r h1) ?_
      refine one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ?_
      have hrr : (r:ℝ) ≤ (r':ℝ) + 1 := by exact_mod_cast h1
      have hr'0 : (0:ℝ) ≤ (r':ℝ) := Nat.cast_nonneg _
      rcases le_total (r:ℝ) 1 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
  have hmaxpos : (0:ℝ) < max (r:ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  rw [show 1 / ((max (r:ℝ) 1) * Real.log (1 + (R:ℝ))) = (1 / max (r:ℝ) 1) / Real.log (1 + (R:ℝ)) by
    field_simp]
  gcongr

/-- The number of sites at sup-distance exactly `r` from the origin is at most `8r`
(for `r ≥ 1`), in dimension `d ≤ 2`. -/
lemma card_shell_le (hd : d ≤ 2) (M r : ℕ) (hr : 1 ≤ r) :
    ((box d M).filter fun x => snorm x = r).card ≤ 8 * r := by
  classical
  have hsub : ((box d M).filter fun x => snorm x = r) ⊆ box d r \ box d (r - 1) := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [Finset.mem_sdiff, mem_box_iff, mem_box_iff]
    exact ⟨le_of_eq hx.2, by omega⟩
  have hcard := Finset.card_le_card hsub
  have hinter : box d (r - 1) ∩ box d r = box d (r - 1) :=
    Finset.inter_eq_left.2 (box_subset (by omega))
  have hsd : (box d r \ box d (r - 1)).card = (2 * r + 1) ^ d - (2 * (r - 1) + 1) ^ d := by
    rw [Finset.card_sdiff, hinter, card_box, card_box]
  rw [hsd] at hcard
  have hkey : (2 * r + 1) ^ d - (2 * (r - 1) + 1) ^ d ≤ 8 * r := by
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    interval_cases d
    · simp
    · simp only [pow_one]
      omega
    · have e1 : (2 * (n + 1) + 1) ^ 2 = 4 * (n * n) + 12 * n + 9 := by ring
      have e2 : (2 * n + 1) ^ 2 = 4 * (n * n) + 4 * n + 1 := by ring
      rw [e1, e2]
      generalize n * n = k
      omega
  omega

/-- The harmonic-type sum over the box, obtained by summing over the spheres. -/
lemma shell_sum_bound (hd : d ≤ 2) (R : ℕ) :
    ∑ x ∈ box d (R + 1), 1 / (max (snorm x : ℝ) 1) ^ 2 ≤ 9 + 8 * Real.log (1 + (R:ℝ)) := by
  classical
  set W : Site d → ℝ := fun x => 1 / (max (snorm x : ℝ) 1) ^ 2 with hW
  have hmaps : ∀ x ∈ box d (R + 1), snorm x ∈ Finset.range (R + 2) := by
    intro x hx
    rw [mem_box_iff] at hx
    simp only [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps W
  rw [← hfib]
  have hfiber : ∀ r ∈ Finset.range (R + 2),
      ∑ x ∈ (box d (R + 1)).filter (fun x => snorm x = r), W x
        = ((box d (R + 1)).filter (fun x => snorm x = r)).card * (1 / (max (r:ℝ) 1) ^ 2) := by
    intro r _
    rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mem_filter] at hx
    rw [hW]
    simp [hx.2]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_range_succ']
  have h0 : (((box d (R + 1)).filter (fun x => snorm x = 0)).card : ℝ) * (1 / (max (0:ℝ) 1) ^ 2)
      ≤ 1 := by
    have hsub : ((box d (R + 1)).filter (fun x => snorm x = 0)) ⊆ box d 0 := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [mem_box_iff, hx.2]
    have hc : (((box d (R + 1)).filter (fun x => snorm x = 0)).card : ℝ) ≤ 1 := by
      have hcc := Finset.card_le_card hsub
      rw [card_box] at hcc
      simp at hcc
      exact_mod_cast hcc
    have hone : (1:ℝ) / (max (0:ℝ) 1) ^ 2 = 1 := by norm_num
    rw [hone, mul_one]
    exact hc
  have hstep : ∀ i ∈ Finset.range (R + 1),
      (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
        * (1 / (max ((i:ℝ) + 1) 1) ^ 2) ≤ 8 / ((i:ℝ) + 1) := by
    intro i _
    have hcard : (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
        ≤ 8 * ((i:ℝ) + 1) := by
      have hc := card_shell_le (d := d) hd (R + 1) (i + 1) (by omega)
      have h2 : (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
          ≤ ((8 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast at h2
      linarith
    have hmax : max ((i:ℝ) + 1) 1 = (i:ℝ) + 1 := by
      apply max_eq_left
      have : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg _
      linarith
    rw [hmax]
    have hpos : (0:ℝ) < (i:ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
    nlinarith [hcard, hpos]
  have hsum : ∑ i ∈ Finset.range (R + 1),
      (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
        * (1 / (max ((i:ℝ) + 1) 1) ^ 2)
      ≤ ∑ i ∈ Finset.range (R + 1), 8 / ((i:ℝ) + 1) := Finset.sum_le_sum hstep
  have hharm : ∑ i ∈ Finset.range (R + 1), 8 / ((i:ℝ) + 1) ≤ 8 * (1 + Real.log (1 + (R:ℝ))) := by
    have h := harmonic_le_one_add_log (R + 1)
    have hcast : ((harmonic (R + 1) : ℚ) : ℝ) = ∑ i ∈ Finset.range (R + 1), (1:ℝ) / (i + 1) := by
      rw [harmonic]
      push_cast
      simp [one_div]
    rw [hcast] at h
    have hlog : Real.log ((R + 1 : ℕ) : ℝ) = Real.log (1 + (R:ℝ)) := by
      congr 1
      push_cast
      ring
    rw [hlog] at h
    have heq : ∑ i ∈ Finset.range (R + 1), 8 / ((i:ℝ) + 1)
        = 8 * ∑ i ∈ Finset.range (R + 1), (1:ℝ) / (i + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [heq]
    linarith
  have heq2 : ∀ i : ℕ, (max (((i + 1 : ℕ)):ℝ) 1) = max ((i:ℝ) + 1) 1 := by
    intro i; push_cast; ring_nf
  simp only [heq2, Nat.cast_zero]
  linarith [hsum.trans hharm, h0]

/-- The Dirichlet energy of the logarithmic spin wave is `O(1 / log R)`. -/
lemma dirichletEnergy_le (hd : d ≤ 2) {R N : ℕ} (hR : 1 ≤ R) (hN : R ≤ N) :
    dirichletEnergy (d := d) R N
      ≤ (18 + 16 * Real.log (1 + (R : ℝ))) / (Real.log (1 + (R : ℝ))) ^ 2 := by
  classical
  have hL : 0 < Real.log (1 + (R:ℝ)) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hA : dirichletEnergy (d := d) R N
      = ∑ x ∈ box d (R + 1), ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2 := by
    unfold dirichletEnergy
    refine (Finset.sum_subset (box_subset (by omega)) ?_).symm
    intro x hx hnx
    rw [mem_box_iff] at hnx
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have e1 : spinWave R x = 0 := spinWave_eq_zero_of_le hR (by omega)
    have e2 : spinWave R (x + unitVec i) = 0 := by
      refine spinWave_eq_zero_of_le hR ?_
      have := snorm_le_snorm_add_unit x i
      omega
    rw [e1, e2]; ring
  rw [hA]
  have hB : ∀ x ∈ box d (R + 1),
      ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
        ≤ (2 / Real.log (1 + (R:ℝ)) ^ 2) * (1 / (max (snorm x : ℝ) 1) ^ 2) := by
    intro x _
    have hm : (0:ℝ) < max (snorm x : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hterm : ∀ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
        ≤ 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) := by
      intro i
      have h1 := spinWave_grad_bound (d := d) hR x i
      have h2 : (spinWave R x - spinWave R (x + unitVec i)) ^ 2
          = |spinWave R x - spinWave R (x + unitVec i)| ^ 2 := (sq_abs _).symm
      rw [h2]
      calc |spinWave R x - spinWave R (x + unitVec i)| ^ 2
          ≤ (1 / ((max (snorm x : ℝ) 1) * Real.log (1 + (R:ℝ)))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) := by
            rw [div_pow, one_pow, mul_pow]
    calc ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
        ≤ ∑ _i : Fin d, 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (d : ℝ) * (1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 2 * (1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2)) := by
          have hd' : (d:ℝ) ≤ 2 := by exact_mod_cast hd
          have hnn : (0:ℝ) ≤ 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) := by
            positivity
          nlinarith
      _ = (2 / Real.log (1 + (R:ℝ)) ^ 2) * (1 / (max (snorm x : ℝ) 1) ^ 2) := by
          field_simp
  calc ∑ x ∈ box d (R + 1), ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
      ≤ ∑ x ∈ box d (R + 1),
          (2 / Real.log (1 + (R:ℝ)) ^ 2) * (1 / (max (snorm x : ℝ) 1) ^ 2) :=
        Finset.sum_le_sum hB
    _ = (2 / Real.log (1 + (R:ℝ)) ^ 2) * ∑ x ∈ box d (R + 1), 1 / (max (snorm x : ℝ) 1) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (2 / Real.log (1 + (R:ℝ)) ^ 2) * (9 + 8 * Real.log (1 + (R:ℝ))) :=
        mul_le_mul_of_nonneg_left (shell_sum_bound hd R) (by positivity)
    _ = (18 + 16 * Real.log (1 + (R : ℝ))) / (Real.log (1 + (R : ℝ))) ^ 2 := by
        field_simp
        ring

/-- **Vanishing Dirichlet energy in dimension `d ≤ 2`.**  For every `ε > 0` there is a
spin wave, equal to `1` at the origin and supported in a finite box, whose Dirichlet
energy is smaller than `ε`. -/
theorem dirichletEnergy_small (hd : d ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ N, R ≤ N → dirichletEnergy (d := d) R N < ε := by
  set M : ℝ := max 1 (35 / ε) with hM
  set R : ℕ := max 1 ⌈Real.exp M⌉₊ with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hexp : Real.exp M ≤ (R:ℝ) := by
    have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp M⌉₊ : ℕ) : ℝ) ≤ (R:ℝ) := by
      exact_mod_cast Nat.le_max_right 1 ⌈Real.exp M⌉₊
    linarith
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMe : 35 / ε ≤ M := le_max_right _ _
  have hLge : M ≤ Real.log (1 + (R:ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos M) (show Real.exp M ≤ 1 + (R:ℝ) by linarith)
    rwa [Real.log_exp] at h
  refine ⟨R, hR1, fun N hN => ?_⟩
  have hle := dirichletEnergy_le (d := d) hd hR1 hN
  set L := Real.log (1 + (R:ℝ)) with hLdef
  have hL1 : 1 ≤ L := le_trans hM1 hLge
  have hLpos : 0 < L := by linarith
  have hbound : (18 + 16 * L) / L ^ 2 ≤ 34 / L := by
    rw [div_le_div_iff₀ (by positivity) hLpos]
    nlinarith
  have h35 : 35 / ε ≤ L := le_trans hMe hLge
  have hfin : 34 / L < ε := by
    rw [div_lt_iff₀ hLpos]
    have h1 : ε * (35 / ε) ≤ ε * L := mul_le_mul_of_nonneg_left h35 hε.le
    have h2 : ε * (35 / ε) = 35 := by field_simp
    rw [h2] at h1
    linarith
  linarith

end

end Phys

