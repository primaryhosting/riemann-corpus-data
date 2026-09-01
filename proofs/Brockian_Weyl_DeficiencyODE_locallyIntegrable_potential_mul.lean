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

import Brockian.Weyl.Primitive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deficiency elements of a Sturm–Liouville operator are genuine ODE solutions

Let `q : ℝ → ℝ` be a continuous potential on an interval `(a, b)` and let `lam : ℂ`.  The
*minimal operator* associated with the formally symmetric differential expression
`τ u = -u'' + q u` is the restriction of `τ` to smooth compactly supported functions in
`(a, b)`.  A function `y ∈ L²(a, b)` lies in the deficiency space of the minimal operator
at `lam` exactly when it is orthogonal to the range of `τ - conj lam` on test functions,
that is when
`∫ conj (y x) * (-(g'' x) + q x * g x - conj lam * g x) = 0`
for every test function `g` supported in `(a, b)`; see `InDeficiencySpace`.

The main theorem `deficiencyRepresentsODE_of_weakRegularity` states that the deficiency
space is exactly the space of `L²` solutions of the ordinary differential equation
`-u'' + q u = lam * u`, i.e. every deficiency element is (a.e. equal to) a genuine, twice
differentiable, classical solution of the ODE.

The hard direction rests on the one-dimensional elliptic regularity statement
`weakRegularity` (Weyl's lemma): a locally integrable distributional solution of
`-y'' + q y = lam y` agrees a.e. with a classical solution.  It is proved here, so the
main theorem is unconditional.
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set Function Brockian.Weyl

/-- The smoothness exponent `∞`. -/
local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `IsODESolutionOn q lam s u` says that `u` is a classical solution of
`-u'' + q u = lam * u` on the set `s`: `u` is differentiable with a differentiable
derivative `u'` and `u'' = (q - lam) * u` on `s`. -/
def IsODESolutionOn (q : ℝ → ℝ) (lam : ℂ) (s : Set ℝ) (u : ℝ → ℂ) : Prop :=
  ∃ u' : ℝ → ℂ, (∀ x ∈ s, HasDerivAt u (u' x) x) ∧
    ∀ x ∈ s, HasDerivAt u' (((q x : ℂ) - lam) * u x) x

/-- `InDeficiencySpace q lam a b y` says that `y` is an `L²` function on `(a, b)` which is
orthogonal to the range of `τ - conj lam` applied to test functions, where
`τ u = -u'' + q u`; i.e. `y` belongs to the deficiency space of the minimal operator
at `lam`. -/
def InDeficiencySpace (q : ℝ → ℝ) (lam : ℂ) (a b : ℝ) (y : ℝ → ℂ) : Prop :=
  MemLp y 2 (volume.restrict (Set.Ioo a b)) ∧
    ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g → tsupport g ⊆ Set.Ioo a b →
      ∫ x, (starRingEnd ℂ) (y x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0

section Auxiliary

variable {a b : ℝ} {q : ℝ → ℝ} {lam : ℂ}

/-- Multiplying a locally integrable function by the continuous function `q - lam`
preserves local integrability. -/
theorem locallyIntegrable_potential_mul (hq : Continuous q) {y : ℝ → ℂ}
    (hy : LocallyIntegrable y volume) :
    LocallyIntegrable (fun t => ((q t : ℂ) - lam) * y t) volume := by
  refine locallyIntegrable_iff.2 fun K hK => ?_
  exact IntegrableOn.continuousOn_mul
    (((Complex.continuous_ofReal.comp hq).sub continuous_const).continuousOn)
    (hy.integrableOn_isCompact hK) hK

/-- The deficiency condition, tested against real test functions, is the weak formulation
of the differential equation `-y'' + q y = lam y`. -/
theorem weak_of_deficiency (hq : Continuous q) {y : ℝ → ℂ}
    (hy : LocallyIntegrable y volume)
    (hdef : ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g → tsupport g ⊆ Set.Ioo a b →
      ∫ x, (starRingEnd ℂ) (y x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0) :
    ∀ g : ℝ → ℝ, IsBumpOn a b g →
      ∫ x, deriv (deriv g) x • y x = ∫ x, g x • (((q x : ℂ) - lam) * y x) := by
  intro g hg
  set gc : ℝ → ℂ := fun x => (g x : ℂ) with hgc
  have hd1 : ∀ x, HasDerivAt gc (((deriv g x : ℝ) : ℂ)) x := fun x => (hg.hasDerivAt x).ofReal_comp
  have hderiv_gc : deriv gc = fun x => ((deriv g x : ℝ) : ℂ) := funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (fun x => ((deriv g x : ℝ) : ℂ)) (((deriv (deriv g) x : ℝ) : ℂ)) x :=
    fun x => (hg.deriv_isBumpOn.hasDerivAt x).ofReal_comp
  have hderiv2_gc : deriv (deriv gc) = fun x => ((deriv (deriv g) x : ℝ) : ℂ) := by
    rw [hderiv_gc]
    exact funext fun x => (hd2 x).deriv
  have hsmooth : ContDiff ℝ ∞' gc := Complex.ofRealCLM.contDiff.comp hg.smooth
  have hsupp : Function.support gc = Function.support g := by
    ext x
    simp [hgc]
  have htsupp : tsupport gc = tsupport g := by
    unfold tsupport
    rw [hsupp]
  have hcs : HasCompactSupport gc := by
    rw [HasCompactSupport, htsupp]
    exact hg.compactSupport
  have hts : tsupport gc ⊆ Set.Ioo a b := by
    rw [htsupp]
    exact hg.tsupport_subset
  have h0 := hdef gc hsmooth hcs hts
  rw [hderiv2_gc] at h0
  have hconj : (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (y x) *
      (-((deriv (deriv g) x : ℝ) : ℂ) + (q x : ℂ) * gc x
        - (starRingEnd ℂ) lam * gc x)) = 0 := by
    rw [h0]
    simp
  rw [← integral_conj] at hconj
  simp only [map_mul, map_sub, map_add, map_neg, Complex.conj_conj, Complex.conj_ofReal,
    hgc] at hconj
  -- `hconj : ∫ x, y x * (-(deriv (deriv g) x) + q x * g x - lam * g x) = 0`
  have hA : Integrable (fun x => deriv (deriv g) x • y x) volume :=
    hg.deriv_isBumpOn.deriv_isBumpOn.integrable_smul hy
  have hB : Integrable (fun x => g x • (((q x : ℂ) - lam) * y x)) volume :=
    hg.integrable_smul (locallyIntegrable_potential_mul hq hy)
  have hpt : ∀ x, y x * (-((deriv (deriv g) x : ℝ) : ℂ) + (q x : ℂ) * (g x : ℂ)
      - lam * (g x : ℂ)) = -(deriv (deriv g) x • y x) + g x • (((q x : ℂ) - lam) * y x) := by
    intro x
    simp only [Complex.real_smul]
    ring
  simp_rw [hpt] at hconj
  have hAneg : Integrable (fun x => -(deriv (deriv g) x • y x)) volume := hA.neg
  rw [integral_add hAneg hB] at hconj
  simp only [integral_neg] at hconj
  exact neg_add_eq_zero.mp hconj

end Auxiliary

/-- **Weyl's lemma in one dimension** (elliptic regularity for `-u'' + q u = lam u`).

If `y` is integrable and satisfies the differential equation `-y'' + q y = lam y` in the
distributional sense on `(a, b)`, then `y` agrees almost everywhere on `(a, b)` with a
classical (twice differentiable) solution of the equation.

This is the regularity statement that used to be assumed as a hypothesis in
`deficiencyRepresentsODE_of_weakRegularity`; it is proved here, which makes that theorem
unconditional. -/
theorem weakRegularity {a b : ℝ} (hab : a < b) {q : ℝ → ℝ} (hq : Continuous q) {lam : ℂ}
    {y : ℝ → ℂ} (hy : Integrable y volume)
    (hweak : ∀ g : ℝ → ℝ, IsBumpOn a b g →
      ∫ x, deriv (deriv g) x • y x = ∫ x, g x • (((q x : ℂ) - lam) * y x)) :
    ∃ u : ℝ → ℂ, IsODESolutionOn q lam (Set.Ioo a b) u ∧
      ∀ᵐ x, x ∈ Set.Ioo a b → y x = u x := by
  set I : Set ℝ := Set.Ioo a b with hI
  -- the right-hand side of the equation, truncated to the interval
  set h : ℝ → ℂ := I.indicator (fun t => ((q t : ℂ) - lam) * y t) with hhdef
  have hqy : LocallyIntegrable (fun t => ((q t : ℂ) - lam) * y t) volume :=
    locallyIntegrable_potential_mul hq hy.locallyIntegrable
  have hhint : Integrable h volume := by
    have h1 : IntegrableOn (fun t => ((q t : ℂ) - lam) * y t) I volume :=
      (hqy.integrableOn_isCompact (isCompact_Icc (a := a) (b := b))).mono_set
        Set.Ioo_subset_Icc_self
    exact h1.integrable_indicator measurableSet_Ioo
  -- the double primitive of `h`
  set c : ℝ := (a + b) / 2 with hc
  have hcI : c ∈ I := by
    constructor <;> · rw [hc]; linarith
  set H : ℝ → ℂ := fun x => ∫ t in c..x, h t with hHdef
  have hHcont : Continuous H := hhint.continuous_primitive c
  set G : ℝ → ℂ := fun x => ∫ t in c..x, H t with hGdef
  have hGderiv : ∀ x, HasDerivAt G (H x) x := fun x =>
    (hHcont.integral_hasStrictDerivAt c x).hasDerivAt
  have hGdiff : Differentiable ℝ G := fun x => (hGderiv x).differentiableAt
  have hGcont : Continuous G := hGdiff.continuous
  -- the double primitive solves the equation distributionally
  have key1 : ∀ g : ℝ → ℝ, IsBumpOn a b g →
      ∫ x, deriv (deriv g) x • G x = ∫ x, g x • h x := by
    intro g hg
    have e1 : ∫ x, deriv (deriv g) x • G x = -∫ x, deriv g x • H x := by
      simp only [hGdef]
      exact integral_deriv_smul_primitive hHcont.locallyIntegrable c hab hg.deriv_isBumpOn
    have e2 : ∫ x, deriv g x • H x = -∫ x, g x • h x := by
      simp only [hHdef]
      exact integral_deriv_smul_primitive hhint.locallyIntegrable c hab hg
    rw [e1, e2, neg_neg]
  -- hence `y - G` has vanishing second distributional derivative
  have key2 : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, deriv (deriv g) x • (y x - G x) = 0 := by
    intro g hg
    have hint1 : Integrable (fun x => deriv (deriv g) x • y x) volume :=
      hg.deriv_isBumpOn.deriv_isBumpOn.integrable_smul hy.locallyIntegrable
    have hint2 : Integrable (fun x => deriv (deriv g) x • G x) volume :=
      hg.deriv_isBumpOn.deriv_isBumpOn.integrable_smul hGcont.locallyIntegrable
    have hsplit : ∫ x, deriv (deriv g) x • (y x - G x)
        = (∫ x, deriv (deriv g) x • y x) - ∫ x, deriv (deriv g) x • G x := by
      simp_rw [smul_sub]
      exact integral_sub hint1 hint2
    have hgh : ∀ x, g x • h x = g x • (((q x : ℂ) - lam) * y x) := by
      intro x
      by_cases hx : x ∈ I
      · rw [hhdef, Set.indicator_of_mem hx]
      · rw [hg.zero_of_notMem hx]
        simp
    rw [hsplit, key1 g hg, hweak g hg]
    simp_rw [hgh]
    exact sub_self _
  have hfloc : LocallyIntegrable (fun x => y x - G x) volume :=
    hy.locallyIntegrable.sub hGcont.locallyIntegrable
  obtain ⟨A, B, hAB⟩ := ae_eq_affine_of_integral_deriv2_smul_eq_zero hab hfloc key2
  -- the candidate classical solution
  set u : ℝ → ℂ := fun x => G x + (x • A + B) with hudef
  have hucont : Continuous u :=
    hGcont.add ((continuous_id.smul continuous_const).add continuous_const)
  have hyu : ∀ᵐ x, x ∈ I → y x = u x := by
    filter_upwards [hAB] with x hx hmem
    have hx' := hx hmem
    rw [hudef]
    simp only
    rw [← hx']
    abel
  have hKcont : Continuous (fun t => ((q t : ℂ) - lam) * u t) :=
    ((Complex.continuous_ofReal.comp hq).sub continuous_const).mul hucont
  have hphi : ∀ z, HasDerivAt (fun x => ∫ t in c..x, ((q t : ℂ) - lam) * u t)
      (((q z : ℂ) - lam) * u z) z := fun z => (hKcont.integral_hasStrictDerivAt c z).hasDerivAt
  have hHphi : Set.EqOn H (fun x => ∫ t in c..x, ((q t : ℂ) - lam) * u t) I := by
    intro z hz
    simp only [hHdef]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hyu] with t ht htmem
    have htI : t ∈ I :=
      Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hcI hz (Set.uIoc_subset_uIcc htmem)
    rw [hhdef, Set.indicator_of_mem htI, ht htI]
  have hHderiv : ∀ x ∈ I, HasDerivAt H (((q x : ℂ) - lam) * u x) x := by
    intro x hx
    exact (hphi x).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2) hHphi)
  refine ⟨u, ⟨fun x => H x + A, ?_, ?_⟩, hyu⟩
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => x • A + B) A x := by
      simpa using ((hasDerivAt_id x).smul_const A).add_const B
    simpa [hudef] using (hGderiv x).add h1
  · intro x hx
    simpa using (hHderiv x hx).add_const A

set_option maxRecDepth 8000 in
/-- A classical solution of `-u'' + q u = lam u` on `(a, b)` satisfies the deficiency
identity: it is orthogonal to `(τ - conj lam) g` for every test function `g`. -/
theorem deficiency_of_isODESolution {a b : ℝ} (hab : a < b) {q : ℝ → ℝ} (hq : Continuous q)
    {lam : ℂ} {u : ℝ → ℂ} (hu : IsODESolutionOn q lam (Set.Ioo a b) u) :
    ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g → tsupport g ⊆ Set.Ioo a b →
      ∫ x, (starRingEnd ℂ) (u x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0 := by
  obtain ⟨u', hu1, hu2⟩ := hu
  intro g hgs hgc hgt
  set v : ℝ → ℂ := fun x => (starRingEnd ℂ) (u x) with hv
  set v' : ℝ → ℂ := fun x => (starRingEnd ℂ) (u' x) with hv'
  set w : ℝ → ℂ := fun x => ((q x : ℂ) - (starRingEnd ℂ) lam) * v x with hw
  have hv1 : ∀ x ∈ Set.Ioo a b, HasDerivAt v (v' x) x := fun x hx => (hu1 x hx).star
  have hv2 : ∀ x ∈ Set.Ioo a b, HasDerivAt v' (w x) x := by
    intro x hx
    have h := (hu2 x hx).star
    have hstar : star (((q x : ℂ) - lam) * u x) = w x := by
      show star (((q x : ℂ) - lam) * u x)
        = ((q x : ℂ) - (starRingEnd ℂ) lam) * (starRingEnd ℂ) (u x)
      rw [star_mul', star_sub]
      simp [mul_comm]
    rw [hstar] at h
    exact h
  -- derivatives of the test function
  have hgd1 : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hgs.differentiable (by simp) x).hasDerivAt
  have hgs1 : ContDiff ℝ ∞' (deriv g) := (contDiff_infty_iff_deriv.1 hgs).2
  have hgd2 : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x := fun x =>
    (hgs1.differentiable (by simp) x).hasDerivAt
  have hgc1 : Continuous (deriv g) := hgs1.continuous
  have hgc2 : Continuous (deriv (deriv g)) := (contDiff_infty_iff_deriv.1 hgs1).2.continuous
  -- localize
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := exists_Ioo_of_isCompact hab hgc hgt
  have hgz : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hsub hc)
  have hts1 : tsupport (deriv g) ⊆ Set.Ioo a₀ b₀ :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hsub
  have hd1z : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hts1 hc)
  have hts2 : tsupport (deriv (deriv g)) ⊆ Set.Ioo a₀ b₀ :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hts1
  have hd2z : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv (deriv g) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hts2 hc)
  have huIcc : Set.uIcc a₀ b₀ = Set.Icc a₀ b₀ := Set.uIcc_of_le hab₀.le
  have hIcc : Set.Icc a₀ b₀ ⊆ Set.Ioo a b := Set.Icc_subset_Ioo ha₀ hb₀
  have hmem : ∀ x ∈ Set.uIcc a₀ b₀, x ∈ Set.Ioo a b := by
    intro x hx
    exact hIcc (by rwa [huIcc] at hx)
  have hvcont : ContinuousOn v (Set.uIcc a₀ b₀) := fun x hx =>
    ((hv1 x (hmem x hx)).continuousAt).continuousWithinAt
  have hv'cont : ContinuousOn v' (Set.uIcc a₀ b₀) := fun x hx =>
    ((hv2 x (hmem x hx)).continuousAt).continuousWithinAt
  have hwcont : ContinuousOn w (Set.uIcc a₀ b₀) := by
    have h1 : ContinuousOn (fun x : ℝ => ((q x : ℂ) - (starRingEnd ℂ) lam))
        (Set.uIcc a₀ b₀) :=
      ((Complex.continuous_ofReal.comp hq).sub continuous_const).continuousOn
    exact h1.mul hvcont
  have hv'int : IntervalIntegrable v' volume a₀ b₀ := hv'cont.intervalIntegrable
  have hwint : IntervalIntegrable w volume a₀ b₀ := hwcont.intervalIntegrable
  -- two integrations by parts
  have hpartsA : ∫ x in a₀..b₀, v x * deriv (deriv g) x
      = v b₀ * deriv g b₀ - v a₀ * deriv g a₀ - ∫ x in a₀..b₀, v' x * deriv g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := v) (u' := v') (v := deriv g)
      (v' := deriv (deriv g)) (fun x hx => hv1 x (hmem x hx)) (fun x _ => hgd2 x)
      hv'int (hgc2.intervalIntegrable _ _)
  have hpartsB : ∫ x in a₀..b₀, v' x * deriv g x
      = v' b₀ * g b₀ - v' a₀ * g a₀ - ∫ x in a₀..b₀, w x * g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := v') (u' := w) (v := g)
      (v' := deriv g) (fun x hx => hv2 x (hmem x hx)) (fun x _ => hgd1 x)
      hwint (hgc1.intervalIntegrable _ _)
  rw [hgz a₀ (by simp), hgz b₀ (by simp)] at hpartsB
  rw [hd1z a₀ (by simp), hd1z b₀ (by simp)] at hpartsA
  simp only [mul_zero, sub_zero, zero_sub] at hpartsA hpartsB
  rw [hpartsB, neg_neg] at hpartsA
  -- assemble
  have hzero : ∀ x ∉ Set.Ioc a₀ b₀,
      v x * (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0 := by
    intro x hx
    have hx' : x ∉ Set.Ioo a₀ b₀ := fun hc => hx (Set.Ioo_subset_Ioc_self hc)
    rw [hgz x hx', hd2z x hx']
    ring
  rw [integral_eq_intervalIntegral hab₀.le hzero]
  have hptwise : ∀ x, v x * (-(deriv (deriv g) x) + (q x : ℂ) * g x
      - (starRingEnd ℂ) lam * g x) = -(v x * deriv (deriv g) x) + w x * g x := by
    intro x
    rw [hw]
    ring
  simp_rw [hptwise]
  have hi1 : IntervalIntegrable (fun x => -(v x * deriv (deriv g) x)) volume a₀ b₀ :=
    ((hvcont.mul hgc2.continuousOn).neg).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => w x * g x) volume a₀ b₀ :=
    (hwcont.mul (hgs.continuous.continuousOn)).intervalIntegrable
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_neg, hpartsA]
  ring

/-- **Deficiency elements are ODE solutions.**  A function `y` belongs to the deficiency
space of the minimal Sturm–Liouville operator `-u'' + q u` at `lam` on `(a, b)` if and
only if it agrees almost everywhere with an `L²` classical solution of the differential
equation `-u'' + q u = lam u`. -/
theorem deficiencyRepresentsODE_of_weakRegularity {a b : ℝ} (hab : a < b) {q : ℝ → ℝ}
    (hq : Continuous q) (lam : ℂ) (y : ℝ → ℂ) :
    InDeficiencySpace q lam a b y ↔
      ∃ u : ℝ → ℂ, IsODESolutionOn q lam (Set.Ioo a b) u ∧
        MemLp u 2 (volume.restrict (Set.Ioo a b)) ∧
        y =ᵐ[volume.restrict (Set.Ioo a b)] u := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp [Real.volume_Ioo]
  constructor
  · rintro ⟨hLp, hdef⟩
    have hyint : IntegrableOn y (Set.Ioo a b) volume := hLp.integrable one_le_two
    set Y : ℝ → ℂ := (Set.Ioo a b).indicator y with hYdef
    have hYint : Integrable Y volume := hyint.integrable_indicator measurableSet_Ioo
    have hYeq : ∀ x ∈ Set.Ioo a b, Y x = y x := fun x hx => Set.indicator_of_mem hx y
    have hdefY : ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g →
        tsupport g ⊆ Set.Ioo a b →
        ∫ x, (starRingEnd ℂ) (Y x) *
          (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0 := by
      intro g h1 h2 h3
      rw [← hdef g h1 h2 h3]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ Set.Ioo a b
      · rw [hYeq x hx]
      · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hx (h3 hc)
        have hts2 : tsupport (deriv (deriv g)) ⊆ Set.Ioo a b :=
          ((closure_minimal support_deriv_subset isClosed_closure).trans
            (closure_minimal support_deriv_subset isClosed_closure)).trans h3
        have hg2 : deriv (deriv g) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hc => hx (hts2 hc)
        rw [hg0, hg2]
        ring
    obtain ⟨u, hu, hYu⟩ := weakRegularity hab hq hYint
      (weak_of_deficiency hq hYint.locallyIntegrable hdefY)
    have hyu : y =ᵐ[volume.restrict (Set.Ioo a b)] u := by
      refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      filter_upwards [hYu] with x hx hmem
      rw [← hYeq x hmem]
      exact hx hmem
    exact ⟨u, hu, hLp.ae_eq hyu, hyu⟩
  · rintro ⟨u, hu, hLp, hyu⟩
    refine ⟨hLp.ae_eq hyu.symm, ?_⟩
    intro g h1 h2 h3
    have hyu' : ∀ᵐ x, x ∈ Set.Ioo a b → y x = u x :=
      (ae_restrict_iff' measurableSet_Ioo).1 hyu
    have hswap : ∫ x, (starRingEnd ℂ) (y x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x)
        = ∫ x, (starRingEnd ℂ) (u x) *
          (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) := by
      refine integral_congr_ae ?_
      filter_upwards [hyu'] with x hx
      by_cases hmem : x ∈ Set.Ioo a b
      · rw [hx hmem]
      · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hmem (h3 hc)
        have hts2 : tsupport (deriv (deriv g)) ⊆ Set.Ioo a b :=
          ((closure_minimal support_deriv_subset isClosed_closure).trans
            (closure_minimal support_deriv_subset isClosed_closure)).trans h3
        have hg2 : deriv (deriv g) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hc => hmem (hts2 hc)
        rw [hg0, hg2]
        ring
    rw [hswap]
    exact deficiency_of_isODESolution hab hq hu g h1 h2 h3

end Brockian.Weyl.DeficiencyODE

import Brockian.Weyl.TestFunctions

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Distributions with vanishing first or second derivative on an interval

Let `f : ℝ → E` be locally integrable.

* `Brockian.Weyl.ae_eq_const_of_integral_deriv_smul_eq_zero` (du Bois-Reymond): if
  `∫ g' • f = 0` for every test function `g` supported in `Ioo a b`, then `f` is a.e.
  constant on `Ioo a b`.
* `Brockian.Weyl.ae_eq_affine_of_integral_deriv2_smul_eq_zero`: if `∫ g'' • f = 0` for
  every test function `g` supported in `Ioo a b`, then `f` is a.e. affine on `Ioo a b`.
-/

namespace Brockian.Weyl

open MeasureTheory Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bump function is integrable. -/
theorem IsBumpOn.integrable {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) :
    Integrable g volume :=
  hg.continuous.integrable_of_hasCompactSupport hg.compactSupport

theorem IsBumpOn.hasDerivAt {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) (x : ℝ) :
    HasDerivAt g (deriv g x) x :=
  (hg.smooth.differentiable (by simp) x).hasDerivAt

/-- Integration by parts against the identity: `∫ g' x * x = -∫ g`. -/
theorem IsBumpOn.integral_deriv_mul_id {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : IsBumpOn a b g) : ∫ x, deriv g x * x = -∫ x, g x := by
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hgz : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hdz : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv g x = 0 := by
    intro x hx
    have hts : tsupport (deriv g) ⊆ Set.Ioo a₀ b₀ :=
      (closure_minimal support_deriv_subset isClosed_closure).trans hsub
    exact image_eq_zero_of_notMem_tsupport fun hx' => hx (hts hx')
  have hcont : Continuous (deriv g) := hg.deriv_isBumpOn.continuous
  have h1 : ∫ x, deriv g x * x = ∫ x in a₀..b₀, deriv g x * x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    have : deriv g x = 0 := hdz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
    simp [this]
  have h2 : ∫ x, g x = ∫ x in a₀..b₀, g x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    exact hgz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
  have hparts : ∫ x in a₀..b₀, (deriv g x * x + g x * 1) = g b₀ * b₀ - g a₀ * a₀ :=
    intervalIntegral.integral_deriv_mul_eq_sub (u := g) (u' := deriv g) (v := id)
      (v' := fun _ => 1) (fun x _ => hg.hasDerivAt x) (fun x _ => hasDerivAt_id x)
      (hcont.intervalIntegrable _ _) intervalIntegrable_const
  have hb : g b₀ = 0 := hgz b₀ (by simp)
  have ha : g a₀ = 0 := hgz a₀ (by simp)
  rw [hb, ha] at hparts
  simp only [mul_one, zero_mul, sub_self] at hparts
  have hsplit : (∫ x in a₀..b₀, (deriv g x * x + g x))
      = (∫ x in a₀..b₀, deriv g x * x) + ∫ x in a₀..b₀, g x :=
    intervalIntegral.integral_add ((hcont.mul continuous_id).intervalIntegrable _ _)
      (hg.continuous.intervalIntegrable _ _)
  rw [hsplit] at hparts
  rw [h1, h2]
  linarith [hparts]

/-- **du Bois-Reymond lemma**: a locally integrable function whose distributional derivative
vanishes on `Ioo a b` is a.e. constant there. -/
theorem ae_eq_const_of_integral_deriv_smul_eq_zero {a b : ℝ} (hab : a < b) {f : ℝ → E}
    (hf : LocallyIntegrable f volume)
    (h : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, deriv g x • f x = 0) :
    ∃ C : E, ∀ᵐ x, x ∈ Set.Ioo a b → f x = C := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_isBumpOn_integral_eq_one hab
  set C : E := ∫ x, χ x • f x with hC
  refine ⟨C, ?_⟩
  have key : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, g x • (f x - C) = 0 := by
    intro g hg
    set c : ℝ := ∫ x, g x with hc
    have hbump0 : IsBumpOn a b (fun x => g x - c * χ x) := hg.sub (hχ.smul c)
    have hint0 : ∫ x, (g x - c * χ x) = 0 := by
      rw [integral_sub hg.integrable ((hχ.smul c).integrable)]
      simp [integral_const_mul, hχ1, hc]
    obtain ⟨hbump, hderiv⟩ := hbump0.antideriv hab hint0
    have hd : deriv (fun x => ∫ t in a..x, (g t - c * χ t)) = fun x => g x - c * χ x :=
      funext fun x => (hderiv x).deriv
    have h0 := h _ hbump
    rw [hd] at h0
    have hgf : Integrable (fun x => g x • f x) volume := hg.integrable_smul hf
    have hχf : Integrable (fun x => χ x • f x) volume := hχ.integrable_smul hf
    have hexp : ∫ x, (g x - c * χ x) • f x
        = (∫ x, g x • f x) - c • ∫ x, χ x • f x := by
      have hpt : ∀ x, (g x - c * χ x) • f x = g x • f x - c • (χ x • f x) := by
        intro x; rw [sub_smul, mul_smul]
      simp_rw [hpt]
      have h2 : Integrable (fun x => c • (χ x • f x)) volume := hχf.smul c
      rw [integral_sub hgf h2, integral_smul]
    rw [hexp] at h0
    have hgC : Integrable (fun x => g x • C) volume := hg.integrable.smul_const C
    have hsplit : ∫ x, g x • (f x - C) = (∫ x, g x • f x) - (∫ x, g x) • C := by
      have hpt : ∀ x, g x • (f x - C) = g x • f x - g x • C := fun x => smul_sub _ _ _
      simp_rw [hpt]
      rw [integral_sub hgf hgC, integral_smul_const]
    rw [hsplit, ← hc, sub_eq_zero.mp h0, ← hC, sub_self]
  have hloc : LocallyIntegrableOn (fun x => f x - C) (Set.Ioo a b) volume :=
    ((hf.sub (locallyIntegrable_const C))).locallyIntegrableOn _
  have hae := (isOpen_Ioo (a := a) (b := b)).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg1 hg2 hg3 => key g ⟨hg1, hg2, hg3⟩)
  filter_upwards [hae] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

/-- If the second distributional derivative of a locally integrable function vanishes on
`Ioo a b`, then the function is a.e. affine there. -/
theorem ae_eq_affine_of_integral_deriv2_smul_eq_zero {a b : ℝ} (hab : a < b) {f : ℝ → E}
    (hf : LocallyIntegrable f volume)
    (h : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, deriv (deriv g) x • f x = 0) :
    ∃ A B : E, ∀ᵐ x, x ∈ Set.Ioo a b → f x = x • A + B := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_isBumpOn_integral_eq_one hab
  set K : E := ∫ x, deriv χ x • f x with hK
  -- Step 1 : test functions with vanishing integral are derivatives of test functions.
  have step1 : ∀ ψ : ℝ → ℝ, IsBumpOn a b ψ → (∫ x, ψ x) = 0 →
      ∫ x, deriv ψ x • f x = 0 := by
    intro ψ hψ h0
    obtain ⟨hbump, hderiv⟩ := hψ.antideriv hab h0
    have hd : deriv (fun x => ∫ t in a..x, ψ t) = ψ := funext fun x => (hderiv x).deriv
    have h1 := h _ hbump
    rw [hd] at h1
    exact h1
  -- Step 2 : for a general test function, the pairing is proportional to its integral.
  have step2 : ∀ ψ : ℝ → ℝ, IsBumpOn a b ψ → ∫ x, deriv ψ x • f x = (∫ x, ψ x) • K := by
    intro ψ hψ
    set c : ℝ := ∫ x, ψ x with hc
    have hbump0 : IsBumpOn a b (fun x => ψ x - c * χ x) := hψ.sub (hχ.smul c)
    have hint0 : ∫ x, (ψ x - c * χ x) = 0 := by
      rw [integral_sub hψ.integrable ((hχ.smul c).integrable)]
      simp [integral_const_mul, hχ1, hc]
    have h1 := step1 _ hbump0 hint0
    have hd : deriv (fun x => ψ x - c * χ x) = fun x => deriv ψ x - c * deriv χ x :=
      funext fun x => ((hψ.hasDerivAt x).sub ((hχ.hasDerivAt x).const_mul c)).deriv
    rw [hd] at h1
    have hψf : Integrable (fun x => deriv ψ x • f x) volume :=
      hψ.deriv_isBumpOn.integrable_smul hf
    have hχf : Integrable (fun x => deriv χ x • f x) volume :=
      hχ.deriv_isBumpOn.integrable_smul hf
    have hexp : ∫ x, (deriv ψ x - c * deriv χ x) • f x
        = (∫ x, deriv ψ x • f x) - c • ∫ x, deriv χ x • f x := by
      have hpt : ∀ x, (deriv ψ x - c * deriv χ x) • f x
          = deriv ψ x • f x - c • (deriv χ x • f x) := by
        intro x; rw [sub_smul, mul_smul]
      simp_rw [hpt]
      have h2 : Integrable (fun x => c • (deriv χ x • f x)) volume := hχf.smul c
      rw [integral_sub hψf h2, integral_smul]
    rw [hexp] at h1
    rw [sub_eq_zero.mp h1, hK]
  -- Step 3 : subtract the linear part.
  set A : E := -K with hA
  have step3 : ∀ ψ : ℝ → ℝ, IsBumpOn a b ψ → ∫ x, deriv ψ x • (f x - x • A) = 0 := by
    intro ψ hψ
    have hψf : Integrable (fun x => deriv ψ x • f x) volume :=
      hψ.deriv_isBumpOn.integrable_smul hf
    have hmulint : Integrable (fun x => deriv ψ x * x) volume := by
      refine Continuous.integrable_of_hasCompactSupport
        (hψ.deriv_isBumpOn.continuous.mul continuous_id) ?_
      exact hψ.deriv_isBumpOn.compactSupport.mul_right
    have hlin : Integrable (fun x => deriv ψ x • (x • A)) volume := by
      have : (fun x => deriv ψ x • (x • A)) = fun x => (deriv ψ x * x) • A := by
        funext x; rw [smul_smul]
      rw [this]
      exact hmulint.smul_const A
    have hsplit : ∫ x, deriv ψ x • (f x - x • A)
        = (∫ x, deriv ψ x • f x) - ∫ x, deriv ψ x • (x • A) := by
      have hpt : ∀ x, deriv ψ x • (f x - x • A) = deriv ψ x • f x - deriv ψ x • (x • A) :=
        fun x => smul_sub _ _ _
      simp_rw [hpt]
      rw [integral_sub hψf hlin]
    have hlin2 : ∫ x, deriv ψ x • (x • A) = (-∫ x, ψ x) • A := by
      have hpt : ∀ x, deriv ψ x • (x • A) = (deriv ψ x * x) • A := fun x => by rw [smul_smul]
      simp_rw [hpt]
      rw [integral_smul_const, hψ.integral_deriv_mul_id hab]
    rw [hsplit, step2 ψ hψ, hlin2, hA, neg_smul, smul_neg, sub_neg_eq_add, add_neg_cancel]
  have hf₁ : LocallyIntegrable (fun x => f x - x • A) volume :=
    hf.sub ((continuous_id.smul continuous_const).locallyIntegrable)
  obtain ⟨B, hB⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero hab hf₁ step3
  refine ⟨A, B, ?_⟩
  filter_upwards [hB] with x hx hmem
  rw [eq_add_of_sub_eq (hx hmem), add_comm]

end Brockian.Weyl

import Brockian.Weyl.WeakAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Integration by parts against a primitive

For a locally integrable `h : ℝ → ℂ` and a test function `g` supported in `Ioo a b`, we
prove
`∫ g' x • (∫ t in c..x, h t) = -∫ g x • h x`,
i.e. the distributional derivative of the primitive of `h` is `h`.

The real-valued case is `Brockian.Weyl.integral_deriv_mul_primitive_real`; it uses the
Lebesgue differentiation theorem and integration by parts for absolutely continuous
functions.  The complex-valued case
`Brockian.Weyl.integral_deriv_smul_primitive` follows by applying real-linear
functionals.
-/

namespace Brockian.Weyl

open MeasureTheory Set Function

/-- A locally integrable function is interval integrable on every interval. -/
theorem intervalIntegrable_of_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    {h : ℝ → E} (hh : LocallyIntegrable h volume) (p r : ℝ) :
    IntervalIntegrable h volume p r :=
  intervalIntegrable_iff.mpr ((hh.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

/-- The primitive of a locally integrable function is continuous. -/
theorem continuous_primitive_of_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {h : ℝ → E} (hh : LocallyIntegrable h volume) (c : ℝ) :
    Continuous fun x => ∫ t in c..x, h t :=
  intervalIntegral.continuous_primitive (fun p r => intervalIntegrable_of_locallyIntegrable hh p r) c

/-- A bump function is absolutely continuous on any interval. -/
theorem IsBumpOn.absolutelyContinuousOnInterval {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g)
    (p r : ℝ) : AbsolutelyContinuousOnInterval g p r := by
  have hderiv : ∀ x, HasDerivAt g (deriv g x) x := hg.hasDerivAt
  have hcont : Continuous (deriv g) := hg.deriv_isBumpOn.continuous
  have hrepr : g = fun x => g p + ∫ t in p..x, deriv g t := by
    funext x
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => (hderiv t).differentiableAt)
      (hcont.intervalIntegrable _ _)]
    ring
  rw [hrepr]
  have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => g p) p r :=
    (LipschitzWith.const (g p)).lipschitzOnWith.absolutelyContinuousOnInterval
  have h2 : AbsolutelyContinuousOnInterval (fun x => ∫ t in p..x, deriv g t) p r :=
    ((hcont.intervalIntegrable _ _).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc)
  exact h1.add h2

/-- The primitive of a locally integrable function is absolutely continuous on any
interval. -/
theorem absolutelyContinuousOnInterval_primitive {h : ℝ → ℝ} (hh : LocallyIntegrable h volume)
    (c p r : ℝ) : AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, h t) p r := by
  have hrepr : (fun x => ∫ t in c..x, h t)
      = fun x => (∫ t in c..p, h t) + ∫ t in p..x, h t := by
    funext x
    rw [intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_of_locallyIntegrable hh c p)
      (intervalIntegrable_of_locallyIntegrable hh p x)]
  rw [hrepr]
  have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => ∫ t in c..p, h t) p r :=
    (LipschitzWith.const (∫ t in c..p, h t)).lipschitzOnWith.absolutelyContinuousOnInterval
  have h2 : AbsolutelyContinuousOnInterval (fun x => ∫ t in p..x, h t) p r :=
    (intervalIntegrable_of_locallyIntegrable hh p r).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  exact h1.add h2

/-- The distributional derivative of the primitive of a locally integrable real function is
the function itself. -/
theorem integral_deriv_mul_primitive_real {h : ℝ → ℝ} (hh : LocallyIntegrable h volume) (c : ℝ)
    {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g) :
    ∫ x, deriv g x * (∫ t in c..x, h t) = -∫ x, g x * h x := by
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hgz : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hdz : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv g x = 0 := by
    intro x hx
    have hts : tsupport (deriv g) ⊆ Set.Ioo a₀ b₀ :=
      (closure_minimal support_deriv_subset isClosed_closure).trans hsub
    exact image_eq_zero_of_notMem_tsupport fun hx' => hx (hts hx')
  set H : ℝ → ℝ := fun x => ∫ t in c..x, h t with hH
  have hHac : AbsolutelyContinuousOnInterval H a₀ b₀ :=
    absolutelyContinuousOnInterval_primitive hh c a₀ b₀
  have hgac : AbsolutelyContinuousOnInterval g a₀ b₀ := hg.absolutelyContinuousOnInterval a₀ b₀
  have hparts := hHac.integral_mul_deriv_eq_deriv_mul hgac
  have hb : g b₀ = 0 := hgz b₀ (by simp)
  have ha : g a₀ = 0 := hgz a₀ (by simp)
  rw [hb, ha] at hparts
  have hderivH : ∀ᵐ x : ℝ, deriv H x = h x := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hh] with x hx
    exact (hx c).deriv
  have hcongr : ∫ x in a₀..b₀, deriv H x * g x = ∫ x in a₀..b₀, h x * g x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderivH] with x hx _
    rw [hx]
  rw [hcongr] at hparts
  simp only [mul_zero, sub_zero, zero_sub] at hparts
  have hL : ∫ x, deriv g x * H x = ∫ x in a₀..b₀, deriv g x * H x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    have : deriv g x = 0 := hdz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
    simp [this]
  have hR : ∫ x, g x * h x = ∫ x in a₀..b₀, g x * h x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    have : g x = 0 := hgz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
    simp [this]
  rw [hL, hR]
  have hcomm1 : ∫ x in a₀..b₀, deriv g x * H x = ∫ x in a₀..b₀, H x * deriv g x := by
    simp_rw [mul_comm]
  have hcomm2 : ∫ x in a₀..b₀, g x * h x = ∫ x in a₀..b₀, h x * g x := by
    simp_rw [mul_comm]
  rw [hcomm1, hcomm2, hparts]

/-- The distributional derivative of the primitive of a locally integrable complex function
is the function itself. -/
theorem integral_deriv_smul_primitive {h : ℝ → ℂ} (hh : LocallyIntegrable h volume) (c : ℝ)
    {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g) :
    ∫ x, deriv g x • (∫ t in c..x, h t) = -∫ x, g x • h x := by
  have hHcont : Continuous fun x => ∫ t in c..x, h t :=
    continuous_primitive_of_locallyIntegrable hh c
  have hint1 : Integrable (fun x => deriv g x • (∫ t in c..x, h t)) volume :=
    hg.deriv_isBumpOn.integrable_smul hHcont.locallyIntegrable
  have hint2 : Integrable (fun x => g x • h x) volume := hg.integrable_smul hh
  have key : ∀ L : ℂ →L[ℝ] ℝ,
      L (∫ x, deriv g x • (∫ t in c..x, h t)) = L (-∫ x, g x • h x) := by
    intro L
    have hLh : LocallyIntegrable (fun t => L (h t)) volume := by
      refine locallyIntegrable_iff.2 ?_
      intro K hK
      exact L.integrable_comp (hh.integrableOn_isCompact hK)
    have e1 : L (∫ x, deriv g x • (∫ t in c..x, h t))
        = ∫ x, deriv g x * (∫ t in c..x, L (h t)) := by
      rw [← L.integral_comp_comm hint1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
      congr 1
      exact (L.intervalIntegral_comp_comm (intervalIntegrable_of_locallyIntegrable hh c x)).symm
    have e2 : L (-∫ x, g x • h x) = -∫ x, g x * L (h x) := by
      rw [map_neg, ← L.integral_comp_comm hint2]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [e1, e2]
    exact integral_deriv_mul_primitive_real hLh c hab hg
  have hre := key Complex.reCLM
  have him := key Complex.imCLM
  exact Complex.ext hre him

end Brockian.Weyl

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Smooth compactly supported test functions on an interval

This file develops the small amount of test-function calculus needed for the
one–dimensional regularity theory (Weyl's lemma) used in
`Brockian.Weyl.DeficiencyODE`.

The main definitions and results are:

* `Brockian.Weyl.IsBumpOn a b g` : `g : ℝ → ℝ` is smooth, compactly supported and its
  support is contained in `Set.Ioo a b`;
* `Brockian.Weyl.IsBumpOn.exists_Ioo` : the support of a bump is contained in a
  slightly smaller open interval;
* `Brockian.Weyl.IsBumpOn.antideriv` : the primitive of a bump with vanishing integral
  is again a bump;
* `Brockian.Weyl.exists_isBumpOn_integral_eq_one` : existence of a bump of integral one.
-/

namespace Brockian.Weyl

open MeasureTheory Set Function
open scoped Topology

/-- `IsBumpOn a b g` says that `g : ℝ → ℝ` is a test function for the open interval
`Ioo a b`: it is smooth, compactly supported, and its (closed) support is contained
in `Ioo a b`. -/
structure IsBumpOn (a b : ℝ) (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
  compactSupport : HasCompactSupport g
  tsupport_subset : tsupport g ⊆ Set.Ioo a b

namespace IsBumpOn

variable {a b : ℝ} {g : ℝ → ℝ}

theorem continuous (hg : IsBumpOn a b g) : Continuous g := hg.smooth.continuous

theorem zero_of_notMem (hg : IsBumpOn a b g) {x : ℝ} (hx : x ∉ Set.Ioo a b) : g x = 0 := by
  by_contra h
  exact hx (hg.tsupport_subset (subset_tsupport g h))

/-- The derivative of a bump is a bump. -/
theorem deriv_isBumpOn (hg : IsBumpOn a b g) : IsBumpOn a b (deriv g) where
  smooth := (contDiff_infty_iff_deriv.1 hg.smooth).2
  compactSupport := hg.compactSupport.deriv
  tsupport_subset :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hg.tsupport_subset

theorem add (hg : IsBumpOn a b g) {h : ℝ → ℝ} (hh : IsBumpOn a b h) :
    IsBumpOn a b (fun x => g x + h x) where
  smooth := hg.smooth.add hh.smooth
  compactSupport := hg.compactSupport.add hh.compactSupport
  tsupport_subset :=
    (tsupport_add g h).trans (union_subset hg.tsupport_subset hh.tsupport_subset)

theorem smul (c : ℝ) (hg : IsBumpOn a b g) : IsBumpOn a b (fun x => c * g x) where
  smooth := contDiff_const.mul hg.smooth
  compactSupport := hg.compactSupport.mul_left
  tsupport_subset := by
    refine subset_trans ?_ hg.tsupport_subset
    exact closure_mono (Function.support_mul_subset_right _ _)

theorem sub (hg : IsBumpOn a b g) {h : ℝ → ℝ} (hh : IsBumpOn a b h) :
    IsBumpOn a b (fun x => g x - h x) := by
  have := hg.add (hh.smul (-1))
  simpa [sub_eq_add_neg] using this

end IsBumpOn

/-- A compact subset of `Ioo a b` is contained in a strictly smaller open interval. -/
theorem exists_Ioo_of_isCompact {a b : ℝ} (hab : a < b) {K : Set ℝ} (hcomp : IsCompact K)
    (hsub : K ⊆ Set.Ioo a b) :
    ∃ a₀ b₀ : ℝ, a < a₀ ∧ a₀ < b₀ ∧ b₀ < b ∧ K ⊆ Set.Ioo a₀ b₀ := by
  rcases eq_empty_or_nonempty K with hK | hK
  · refine ⟨a + (b - a) / 3, a + 2 * (b - a) / 3, by linarith, by linarith, by linarith, ?_⟩
    rw [hK]; exact empty_subset _
  · have hm : sInf K ∈ K := hcomp.sInf_mem hK
    have hM : sSup K ∈ K := hcomp.sSup_mem hK
    have hmI := hsub hm
    have hMI := hsub hM
    simp only [mem_Ioo] at hmI hMI
    refine ⟨(a + sInf K) / 2, (sSup K + b) / 2, by linarith [hmI.1], ?_, by linarith [hMI.2], ?_⟩
    · have : sInf K ≤ sSup K := le_csSup hcomp.bddAbove hm
      linarith [hmI.1, hMI.2]
    · intro x hx
      have h1 : sInf K ≤ x := csInf_le hcomp.bddBelow hx
      have h2 : x ≤ sSup K := le_csSup hcomp.bddAbove hx
      simp only [mem_Ioo]
      constructor <;> linarith [hmI.1, hMI.2]

/-- The support of a bump on `Ioo a b` is contained in a strictly smaller open interval. -/
theorem IsBumpOn.exists_Ioo {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) (hab : a < b) :
    ∃ a₀ b₀ : ℝ, a < a₀ ∧ a₀ < b₀ ∧ b₀ < b ∧ tsupport g ⊆ Set.Ioo a₀ b₀ :=
  exists_Ioo_of_isCompact hab hg.compactSupport hg.tsupport_subset

/-- If a function vanishes outside `Ioc a₀ b₀` then its integral over the line is the
interval integral over `a₀..b₀`. -/
theorem integral_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a₀ b₀ : ℝ} (hab : a₀ ≤ b₀) {F : ℝ → E} (hF : ∀ x ∉ Set.Ioc a₀ b₀, F x = 0) :
    ∫ x, F x = ∫ x in a₀..b₀, F x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

/-- A bump times a locally integrable function is integrable. -/
theorem IsBumpOn.integrable_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) {f : ℝ → E}
    (hf : LocallyIntegrable f volume) : Integrable (fun x => g x • f x) volume := by
  have hK : IsCompact (tsupport g) := hg.compactSupport
  have hfK : IntegrableOn f (tsupport g) volume := hf.integrableOn_isCompact hK
  have hint : IntegrableOn (fun x => g x • f x) (tsupport g) volume :=
    hfK.continuousOn_smul hg.continuous.continuousOn hK
  refine hint.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [this]

/-- The primitive of a bump with vanishing integral is again a bump, with derivative the
original bump. -/
theorem IsBumpOn.antideriv {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g)
    (h0 : ∫ x, g x = 0) :
    IsBumpOn a b (fun x => ∫ t in a..x, g t) ∧
      ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := by
  have hcont : Continuous g := hg.continuous
  have hderiv : ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := fun x =>
    (hcont.integral_hasStrictDerivAt a x).hasDerivAt
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hzero : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hsupp : ∀ x, x ∉ Set.Icc a₀ b₀ → (∫ t in a..x, g t) = 0 := by
    intro x hx
    rcases lt_or_ge x a₀ with hlt | hge
    · have hcongr : ∀ t ∈ Set.uIcc a x, g t = (0 : ℝ) := by
        intro t ht
        refine hzero t ?_
        simp only [mem_uIcc] at ht
        intro htI
        rcases ht with ht | ht
        · linarith [htI.1, ht.1]
        · linarith [htI.1, ht.2]
      calc (∫ t in a..x, g t) = ∫ _t in a..x, (0 : ℝ) :=
            intervalIntegral.integral_congr hcongr
        _ = 0 := by simp
    · have hxb : b₀ < x := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · linarith
        · exact hx
      have h1 : ∀ t ∉ Set.Ioc a x, g t = 0 := by
        intro t ht
        refine hzero t ?_
        simp only [mem_Ioc, not_and_or, not_le, not_lt] at ht
        intro htI
        rcases ht with ht | ht
        · linarith [htI.1]
        · linarith [htI.2]
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero h1, h0]
  refine ⟨⟨?_, ?_, ?_⟩, hderiv⟩
  · rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hd : deriv (fun x => ∫ t in a..x, g t) = g := funext fun x => (hderiv x).deriv
    rw [hd]
    exact hg.smooth
  · exact HasCompactSupport.intro (isCompact_Icc (a := a₀) (b := b₀)) hsupp
  · have h1 : tsupport (fun x => ∫ t in a..x, g t) ⊆ Set.Icc a₀ b₀ := by
      refine closure_minimal ?_ isClosed_Icc
      intro x hx
      by_contra hxc
      exact hx (hsupp x hxc)
    exact h1.trans (Set.Icc_subset_Ioo ha₀ hb₀)

/-- There is a bump function on `Ioo a b` with integral one. -/
theorem exists_isBumpOn_integral_eq_one {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, IsBumpOn a b χ ∧ ∫ x, χ x = 1 := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  let f : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  have hrOut : f.rOut = r := rfl
  refine ⟨f.normed volume, ⟨f.contDiff_normed, ?_, ?_⟩, f.integral_normed⟩
  · refine HasCompactSupport.intro (isCompact_closedBall c r) ?_
    intro x hx
    have hns : x ∉ Function.support (f.normed volume) := by
      rw [f.support_normed_eq, hrOut]
      intro hmem
      exact hx (Metric.ball_subset_closedBall hmem)
    simpa using hns
  · have h1 : tsupport (f.normed volume) ⊆ Metric.closedBall c r := by
      rw [tsupport, f.support_normed_eq, hrOut]
      exact Metric.closure_ball_subset_closedBall
    refine h1.trans ?_
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    obtain ⟨h1, h2⟩ := hx
    simp only [mem_Ioo]
    rw [hc, hrdef] at h1 h2
    constructor <;> linarith

end Brockian.Weyl

