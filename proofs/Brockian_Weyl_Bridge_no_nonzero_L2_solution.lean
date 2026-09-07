/-
  Brockian/WeylBridge.lean — deficiency triviality for −y″ + V y = λ y
  at non-real λ (continuous real V; y, y' ∈ L²(ℝ)).

  Classical Wronskian identity: with
      W(x) = conj(y x) · y' x − conj(y' x) · y x,
  the ODE and reality of V give
      W' = −2i (Im λ) |y|².
  Since y, y' ∈ L², W' ∈ L¹ so W has limits at ±∞; the bound
      |W| ≤ |y|² + |y'|²
  forces those limits to vanish. Taking a → −∞, b → +∞ in the finite
  identity yields (Im λ) · ∫|y|² = 0, hence y ≡ 0 by continuity.
-/
import Mathlib

open MeasureTheory Filter Topology intervalIntegral Set Complex ComplexConjugate

namespace Brockian.Weyl.Bridge

/-- `y` solves `−y″ + V y = λ y` on ℝ, with `y, y'` square-integrable. -/
structure IsL2Solution (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  deriv1 : ∀ x, HasDerivAt y (y' x) x
  deriv2 : ∀ x, HasDerivAt y' (y'' x) x
  eqn    : ∀ x, y'' x = ((V x : ℂ) - lam) * y x
  memL2  : MemLp y 2 volume
  memL2' : MemLp y' 2 volume

variable {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ}

/-! ### Regularity and integrability -/

theorem continuous_y (hy : IsL2Solution V lam y y' y'') : Continuous y :=
  continuous_iff_continuousAt.mpr fun x => (hy.deriv1 x).continuousAt

theorem continuous_y' (hy : IsL2Solution V lam y y' y'') : Continuous y' :=
  continuous_iff_continuousAt.mpr fun x => (hy.deriv2 x).continuousAt

theorem integrable_normSq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun x => ‖f x‖ ^ 2) := by
  simpa using hf.integrable_norm_rpow (by norm_num) (by norm_num)

theorem integrable_y_normSq (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => ‖y x‖ ^ 2) :=
  integrable_normSq hy.memL2

theorem integrable_y'_normSq (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => ‖y' x‖ ^ 2) :=
  integrable_normSq hy.memL2'

theorem integrable_normSq_add (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => ‖y x‖ ^ 2 + ‖y' x‖ ^ 2) :=
  (integrable_y_normSq hy).add (integrable_y'_normSq hy)

/-! ### Boundary Wronskian -/

/-- Boundary Wronskian of `(conj y, y)`. -/
noncomputable def wronskianConj (y y' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => conj (y x) * y' x - conj (y' x) * y x

theorem wronskianConj_eq_two_I_im (x : ℝ) :
    wronskianConj y y' x = (↑(2 * (conj (y x) * y' x).im) : ℂ) * I := by
  unfold wronskianConj
  have hz : conj (conj (y x) * y' x) = conj (y' x) * y x := by
    simp [map_mul, mul_comm]
  rw [← hz, Complex.sub_conj]

theorem norm_wronskianConj_le (x : ℝ) :
    ‖wronskianConj y y' x‖ ≤ ‖y x‖ ^ 2 + ‖y' x‖ ^ 2 := by
  have h1 : ‖wronskianConj y y' x‖ = 2 * |(conj (y x) * y' x).im| := by
    rw [wronskianConj_eq_two_I_im, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  have h2 : |(conj (y x) * y' x).im| ≤ ‖y x‖ * ‖y' x‖ :=
    (Complex.abs_im_le_norm _).trans (by simp [norm_mul])
  have h3 : 2 * (‖y x‖ * ‖y' x‖) ≤ ‖y x‖ ^ 2 + ‖y' x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y x‖ - ‖y' x‖)]
  calc
    ‖wronskianConj y y' x‖ = 2 * |(conj (y x) * y' x).im| := h1
    _ ≤ 2 * (‖y x‖ * ‖y' x‖) := by gcongr
    _ ≤ ‖y x‖ ^ 2 + ‖y' x‖ ^ 2 := h3

/-! ### W' = −2i (Im λ) |y|² -/

theorem hasDerivAt_wronskianConj (hy : IsL2Solution V lam y y' y'') (x : ℝ) :
    HasDerivAt (wronskianConj y y')
      (-(2 * I * ↑lam.im) * ↑(‖y x‖ ^ 2)) x := by
  have h1 : HasDerivAt (fun t => conj (y t) * y' t)
      (conj (y' x) * y' x + conj (y x) * y'' x) x :=
    (hy.deriv1 x).star.mul (hy.deriv2 x)
  have h2 : HasDerivAt (fun t => conj (y' t) * y t)
      (conj (y'' x) * y x + conj (y' x) * y' x) x :=
    (hy.deriv2 x).star.mul (hy.deriv1 x)
  have hW0 : HasDerivAt (fun t => conj (y t) * y' t - conj (y' t) * y t)
      ((conj (y' x) * y' x + conj (y x) * y'' x)
        - (conj (y'' x) * y x + conj (y' x) * y' x)) x :=
    h1.sub h2
  have hsimp :
      (conj (y' x) * y' x + conj (y x) * y'' x)
        - (conj (y'' x) * y x + conj (y' x) * y' x)
      = conj (y x) * y'' x - conj (y'' x) * y x := by
    ring
  have hW : HasDerivAt (wronskianConj y y')
      (conj (y x) * y'' x - conj (y'' x) * y x) x := by
    change HasDerivAt (fun t => conj (y t) * y' t - conj (y' t) * y t) _ x
    rwa [hsimp] at hW0
  have hny : conj (y x) * y x = ↑(‖y x‖ ^ 2) := by
    rw [mul_comm, Complex.mul_conj, ofReal_inj, Complex.normSq_eq_norm_sq]
  have hcalc :
      conj (y x) * y'' x - conj (y'' x) * y x
        = (-(2 * I * ↑lam.im)) * ↑(‖y x‖ ^ 2) := by
    rw [hy.eqn x]
    simp only [map_mul, map_sub, Complex.conj_ofReal]
    -- goal: conj(y)*((V-λ)y) − (V−conj λ)·conj(y)·y = −(2i Im λ)·|y|²
    have hassoc :
        conj (y x) * (((V x : ℂ) - lam) * y x)
            - (↑(V x) - conj lam) * conj (y x) * y x
          = ((↑(V x) - lam) - (↑(V x) - conj lam)) * (conj (y x) * y x) := by
      ring
    rw [hassoc, hny]
    have hVdiff : (↑(V x) - lam) - (↑(V x) - conj lam) = -(2 * I * ↑lam.im) := by
      have : (↑(V x) - lam) - (↑(V x) - conj lam) = conj lam - lam := by ring
      rw [this, ← neg_sub, Complex.sub_conj]
      -- −↑(2 * lam.im) * I = −(2 * I * ↑lam.im)
      push_cast
      ring
    rw [hVdiff]
  exact hW.congr_deriv hcalc

theorem integrable_wronskianConj_deriv (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) := by
  simpa using (integrable_y_normSq hy).ofReal.const_mul (-(2 * I * ↑lam.im) : ℂ)

/-! ### Limits of W at ±∞ exist and vanish -/

theorem tendsto_wronskianConj_atTop
    (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atTop (nhds (limUnder atTop (wronskianConj y y'))) := by
  refine tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (a := 0) (f' := fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) ?_ ?_
  · intro x _hx; exact hasDerivAt_wronskianConj hy x
  · exact (integrable_wronskianConj_deriv hy).integrableOn

theorem tendsto_wronskianConj_atBot
    (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atBot (nhds (limUnder atBot (wronskianConj y y'))) := by
  refine tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic
    (a := 0) (f' := fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) ?_ ?_
  · intro x _hx; exact hasDerivAt_wronskianConj hy x
  · exact (integrable_wronskianConj_deriv hy).integrableOn

theorem not_integrableOn_const_pos_Ici {c A : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun _ : ℝ => c) (Ici A) := by
  intro h
  rw [IntegrableOn, integrable_const_iff] at h
  rcases h with rfl | hfin
  · exact lt_irrefl 0 hc
  · exact (isFiniteMeasure_restrict (μ := volume) (s := Ici A)).mp hfin Real.volume_Ici

theorem not_integrableOn_const_pos_Iic {c A : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun _ : ℝ => c) (Iic A) := by
  intro h
  rw [IntegrableOn, integrable_const_iff] at h
  rcases h with rfl | hfin
  · exact lt_irrefl 0 hc
  · exact (isFiniteMeasure_restrict (μ := volume) (s := Iic A)).mp hfin Real.volume_Iic

theorem limUnder_wronskianConj_atTop_eq_zero
    (hy : IsL2Solution V lam y y' y'') :
    limUnder atTop (wronskianConj y y') = 0 := by
  set L := limUnder atTop (wronskianConj y y')
  set g : ℝ → ℝ := fun x => ‖y x‖ ^ 2 + ‖y' x‖ ^ 2
  have hgI : Integrable g := integrable_normSq_add hy
  have htend := tendsto_wronskianConj_atTop hy
  by_contra hne
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hne
  have hEven : ∀ᶠ x in atTop, ‖L‖ / 2 ≤ ‖wronskianConj y y' x‖ := by
    have : Tendsto (fun x => ‖wronskianConj y y' x‖) atTop (nhds ‖L‖) := htend.norm
    filter_upwards [this.eventually_const_lt (half_lt_self hLpos)] with x hx
    exact hx.le
  have hmaj : ∀ᶠ x in atTop, ‖L‖ / 2 ≤ g x := by
    filter_upwards [hEven] with x hx
    exact hx.trans (norm_wronskianConj_le x)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hmaj
  have hOn : IntegrableOn g (Ici A) := hgI.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => ‖L‖ / 2) (Ici A) := by
    refine Integrable.mono' hOn continuous_const.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ici]
    refine Eventually.of_forall fun x hx => ?_
    simp only [Real.norm_eq_abs, abs_of_nonneg (half_pos hLpos).le]
    exact hA x hx
  exact not_integrableOn_const_pos_Ici (half_pos hLpos) hconst

theorem limUnder_wronskianConj_atBot_eq_zero
    (hy : IsL2Solution V lam y y' y'') :
    limUnder atBot (wronskianConj y y') = 0 := by
  set L := limUnder atBot (wronskianConj y y')
  set g : ℝ → ℝ := fun x => ‖y x‖ ^ 2 + ‖y' x‖ ^ 2
  have hgI : Integrable g := integrable_normSq_add hy
  have htend := tendsto_wronskianConj_atBot hy
  by_contra hne
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hne
  have hEven : ∀ᶠ x in atBot, ‖L‖ / 2 ≤ ‖wronskianConj y y' x‖ := by
    have : Tendsto (fun x => ‖wronskianConj y y' x‖) atBot (nhds ‖L‖) := htend.norm
    filter_upwards [this.eventually_const_lt (half_lt_self hLpos)] with x hx
    exact hx.le
  have hmaj : ∀ᶠ x in atBot, ‖L‖ / 2 ≤ g x := by
    filter_upwards [hEven] with x hx
    exact hx.trans (norm_wronskianConj_le x)
  obtain ⟨A, hA⟩ := eventually_atBot.mp hmaj
  have hOn : IntegrableOn g (Iic A) := hgI.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => ‖L‖ / 2) (Iic A) := by
    refine Integrable.mono' hOn continuous_const.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Iic]
    refine Eventually.of_forall fun x hx => ?_
    simp only [Real.norm_eq_abs, abs_of_nonneg (half_pos hLpos).le]
    exact hA x hx
  exact not_integrableOn_const_pos_Iic (half_pos hLpos) hconst

theorem tendsto_wronskianConj_atTop_zero (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atTop (nhds 0) := by
  simpa [limUnder_wronskianConj_atTop_eq_zero hy] using tendsto_wronskianConj_atTop hy

theorem tendsto_wronskianConj_atBot_zero (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atBot (nhds 0) := by
  simpa [limUnder_wronskianConj_atBot_eq_zero hy] using tendsto_wronskianConj_atBot hy

/-! ### Finite-interval identity -/

theorem integral_wronskianConj_eq (hy : IsL2Solution V lam y y' y'') (a b : ℝ) :
    wronskianConj y y' b - wronskianConj y y' a
      = ∫ x in a..b, (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2) := by
  have hder : ∀ x ∈ uIcc a b, HasDerivAt (wronskianConj y y')
      ((-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) x := fun x _ =>
    hasDerivAt_wronskianConj hy x
  have hcont : Continuous (fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) :=
    continuous_const.mul (continuous_ofReal.comp ((continuous_y hy).norm.pow 2))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hcont.intervalIntegrable a b)).symm

theorem integral_wronskianConj_eq_mul (hy : IsL2Solution V lam y y' y'') (a b : ℝ) :
    wronskianConj y y' b - wronskianConj y y' a
      = (-(2 * I * ↑lam.im) : ℂ) * ↑(∫ x in a..b, ‖y x‖ ^ 2) := by
  rw [integral_wronskianConj_eq hy a b]
  have h1 : ∫ x in a..b, (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)
      = (-(2 * I * ↑lam.im) : ℂ) * ∫ x in a..b, (↑(‖y x‖ ^ 2) : ℂ) :=
    intervalIntegral.integral_const_mul _ _
  have h2 : ∫ x in a..b, (↑(‖y x‖ ^ 2) : ℂ) = ↑(∫ x in a..b, ‖y x‖ ^ 2) :=
    intervalIntegral.integral_ofReal
  rw [h1, h2]

/-! ### Passage to the whole line -/

theorem coeff_ne_zero (hlam : lam.im ≠ 0) : (-(2 * I * ↑lam.im) : ℂ) ≠ 0 := by
  intro h
  have h' : (2 * I * ↑lam.im : ℂ) = 0 := by
    have := congrArg Neg.neg h
    simpa using this
  have h2I : (2 * I : ℂ) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h2 | hI
    · norm_num at h2
    · exact Complex.I_ne_zero hI
  have him : (↑lam.im : ℂ) = 0 := (mul_eq_zero.mp h').resolve_left h2I
  exact hlam (ofReal_eq_zero.mp him)

theorem global_boundary_identity (hy : IsL2Solution V lam y y' y'') :
    (-(2 * I * ↑lam.im) : ℂ) * ↑(∫ x, ‖y x‖ ^ 2) = 0 := by
  let c : ℂ := -(2 * I * ↑lam.im)
  have hfin (n : ℕ) :
      wronskianConj y y' (n : ℝ) - wronskianConj y y' (-(n : ℝ))
        = c * ↑(∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2) :=
    integral_wronskianConj_eq_mul hy _ _
  have hL : Tendsto (fun n : ℕ => wronskianConj y y' (n : ℝ)) atTop (nhds 0) :=
    (tendsto_wronskianConj_atTop_zero hy).comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n : ℕ => wronskianConj y y' (-(n : ℝ))) atTop (nhds 0) := by
    have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    exact (tendsto_wronskianConj_atBot_zero hy).comp hneg
  have hLHS : Tendsto (fun n : ℕ =>
      wronskianConj y y' (n : ℝ) - wronskianConj y y' (-(n : ℝ))) atTop (nhds 0) := by
    simpa using hL.sub hR
  have hint : Integrable (fun x => ‖y x‖ ^ 2) := integrable_y_normSq hy
  have hInt : Tendsto (fun n : ℕ => ∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2)
      atTop (nhds (∫ x, ‖y x‖ ^ 2)) :=
    intervalIntegral_tendsto_integral hint
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      tendsto_natCast_atTop_atTop
  have hRHS : Tendsto (fun n : ℕ =>
      c * ↑(∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2))
      atTop (nhds (c * ↑(∫ x, ‖y x‖ ^ 2))) :=
    ((continuous_const.mul continuous_ofReal).tendsto _).comp hInt
  have hLHS' : Tendsto (fun n : ℕ =>
      c * ↑(∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2)) atTop (nhds 0) :=
    (tendsto_congr hfin).1 hLHS
  exact (tendsto_nhds_unique hLHS' hRHS).symm

/-! ### Main theorem -/

/-- **Deficiency triviality.** For continuous (bounded) real potential and non-real
spectral parameter, any global L² solution of `−y″ + V y = λ y` is identically zero. -/
theorem no_nonzero_L2_solution (V : ℝ → ℝ) (_hVc : Continuous V)
    (M : ℝ) (_hV : ∀ x, |V x| ≤ M) (lam : ℂ) (hlam : lam.im ≠ 0)
    (y y' y'' : ℝ → ℂ) (hy : IsL2Solution V lam y y' y'') :
    ∀ x, y x = 0 := by
  have hglob := global_boundary_identity (V := V) (lam := lam) (y := y) (y' := y')
    (y'' := y'') hy
  have hcoeff := coeff_ne_zero (lam := lam) hlam
  have hmassℂ : ↑(∫ x, ‖y x‖ ^ 2) = (0 : ℂ) :=
    (mul_eq_zero.mp hglob).resolve_left hcoeff
  have hmass : (∫ x, ‖y x‖ ^ 2 : ℝ) = 0 := ofReal_eq_zero.mp hmassℂ
  have hnn : 0 ≤ fun x : ℝ => ‖y x‖ ^ 2 := fun x => sq_nonneg _
  have hint : Integrable (fun x => ‖y x‖ ^ 2) := integrable_y_normSq hy
  have hae : (fun x => ‖y x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hint).mp hmass
  have hcont : Continuous (fun x => ‖y x‖ ^ 2) := (continuous_y hy).norm.pow 2
  have heq : (fun x => ‖y x‖ ^ 2) = fun _ => 0 :=
    (hcont.ae_eq_iff_eq volume continuous_zero).mp hae
  intro x
  have : ‖y x‖ ^ 2 = 0 := congrFun heq x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)

end Brockian.Weyl.Bridge
