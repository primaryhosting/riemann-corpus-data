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
# Weyl theory: the deficiency space of a Schrödinger operator is represented by ODE solutions

For a real (or complex) potential `q : ℝ → ℂ` the formal differential expression
`τ u = -u'' + q u` gives rise to a maximal operator on `L²(ℝ)`.  For `z : ℂ` the
*deficiency space* at `z` is the kernel of `τ - z` inside the maximal domain.

This file proves the two basic facts of Weyl's theory in this setting:

* the deficiency space is exactly the set of square integrable solutions of the
  ordinary differential equation `u'' = (q - z) u`;
* the space of *all* solutions of that ODE has dimension at most `2`, hence the
  deficiency index of the operator is at most `2`.

The second statement requires a regularity assumption on `q`; the (weak) form used here is
that `q` is bounded on every compact interval (`WeakRegularity`).  Continuous potentials
satisfy it (`WeakRegularity.of_continuous`).
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set

/-- **Weak regularity** of a potential: `q` is bounded on each compact interval.
This is weaker than continuity, and it is all that the uniqueness theory for the
associated ODE requires. -/
def WeakRegularity (q : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ x ∈ Set.Icc a b, ‖q x‖ ≤ C

theorem WeakRegularity.of_continuous {q : ℝ → ℂ} (hq : Continuous q) : WeakRegularity q := by
  intro a b
  exact (isCompact_Icc).exists_bound_of_continuousOn hq.continuousOn

/-- `u` and `v` form a solution pair of the ODE `u' = v`, `v' = (q - z) u`,
i.e. `u` solves `-u'' + q u = z u` with `v = u'`. -/
structure IsSolutionPair (q : ℝ → ℂ) (z : ℂ) (u v : ℝ → ℂ) : Prop where
  deriv_left : ∀ x, HasDerivAt u (v x) x
  deriv_right : ∀ x, HasDerivAt v ((q x - z) * u x) x

/-- `u` solves the differential equation `-u'' + q u = z u` on all of `ℝ`. -/
def IsODESolution (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ v, IsSolutionPair q z u v

theorem IsODESolution.differentiable {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ}
    (hu : IsODESolution q z u) : Differentiable ℝ u := by
  obtain ⟨v, h⟩ := hu
  exact fun x => (h.deriv_left x).differentiableAt

theorem IsSolutionPair.deriv_eq {q : ℝ → ℂ} {z : ℂ} {u v : ℝ → ℂ}
    (h : IsSolutionPair q z u v) : deriv u = v := by
  funext x
  exact (h.deriv_left x).deriv

theorem IsODESolution.deriv_deriv {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ}
    (hu : IsODESolution q z u) (x : ℝ) : deriv (deriv u) x = (q x - z) * u x := by
  obtain ⟨v, h⟩ := hu
  rw [h.deriv_eq]
  exact (h.deriv_right x).deriv

/-- The `ℂ`-vector space of all solutions of `-u'' + q u = z u`. -/
def solutionSubmodule (q : ℝ → ℂ) (z : ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {u | IsODESolution q z u}
  add_mem' := by
    rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
    refine ⟨v₁ + v₂, ⟨fun x => (h₁.deriv_left x).add (h₂.deriv_left x), fun x => ?_⟩⟩
    have := (h₁.deriv_right x).add (h₂.deriv_right x)
    simpa [Pi.add_apply, mul_add] using this
  zero_mem' := ⟨0, ⟨fun x => by simpa using hasDerivAt_const x (0 : ℂ),
    fun x => by simpa using hasDerivAt_const x (0 : ℂ)⟩⟩
  smul_mem' := by
    rintro c u ⟨v, h⟩
    refine ⟨c • v, ⟨fun x => (h.deriv_left x).const_smul c, fun x => ?_⟩⟩
    have := (h.deriv_right x).const_smul c
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this

@[simp] theorem mem_solutionSubmodule {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ} :
    u ∈ solutionSubmodule q z ↔ IsODESolution q z u := Iff.rfl

/-- The differential expression `τ u = -u'' + q u`. -/
noncomputable def tau (q u : ℝ → ℂ) : ℝ → ℂ := fun x => -deriv (deriv u) x + q x * u x

/-- The maximal operator domain: square integrable, twice differentiable functions `u`
with `τ u` again square integrable. -/
def maximalDomain (q : ℝ → ℂ) : Set (ℝ → ℂ) :=
  {u | MemLp u 2 volume ∧ Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
        MemLp (tau q u) 2 volume}

/-- The deficiency space of the maximal operator at `z`: the kernel of `τ - z`. -/
def deficiencySpace (q : ℝ → ℂ) (z : ℂ) : Set (ℝ → ℂ) :=
  {u | u ∈ maximalDomain q ∧ tau q u = fun x => z * u x}

/-- The deficiency space consists exactly of the square integrable solutions of the ODE. -/
theorem deficiencySpace_eq (q : ℝ → ℂ) (z : ℂ) :
    deficiencySpace q z = {u | MemLp u 2 volume ∧ IsODESolution q z u} := by
  ext u
  simp only [deficiencySpace, maximalDomain, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hL2, hd1, hd2, -⟩, heq⟩
    refine ⟨hL2, deriv u, ⟨fun x => (hd1 x).hasDerivAt, fun x => ?_⟩⟩
    have h1 : -deriv (deriv u) x + q x * u x = z * u x := congrFun heq x
    have h2 : deriv (deriv u) x = (q x - z) * u x := by linear_combination -h1
    exact h2 ▸ (hd2 x).hasDerivAt
  · rintro ⟨hL2, hsol⟩
    obtain ⟨v, h⟩ := hsol
    have hdu : deriv u = v := h.deriv_eq
    have hd1 : Differentiable ℝ u := fun x => (h.deriv_left x).differentiableAt
    have hd2 : Differentiable ℝ (deriv u) := by
      rw [hdu]; exact fun x => (h.deriv_right x).differentiableAt
    have htau : tau q u = fun x => z * u x := by
      funext x
      have := IsODESolution.deriv_deriv ⟨v, h⟩ x
      simp only [tau, this]
      ring
    exact ⟨⟨hL2, hd1, hd2, htau ▸ hL2.const_mul z⟩, htau⟩

/-- Uniqueness for the initial value problem: a solution vanishing to first order at a point
vanishes identically.  This is where weak regularity of the potential is used. -/
theorem IsSolutionPair.eq_zero_of_init {q : ℝ → ℂ} (hq : WeakRegularity q) {z : ℂ}
    {u v : ℝ → ℂ} (h : IsSolutionPair q z u v) (hu0 : u 0 = 0) (hv0 : v 0 = 0) : u = 0 := by
  funext x
  set a : ℝ := -(|x| + 1) with ha
  set b : ℝ := |x| + 1 with hb
  obtain ⟨C, hC⟩ := hq a b
  set V : ℝ → (ℂ × ℂ) → (ℂ × ℂ) := fun t w => (w.2, (q t - z) * w.1) with hV
  set K : NNReal := ⟨max 1 (C + ‖z‖), le_trans zero_le_one (le_max_left _ _)⟩ with hK
  have hKcoe : (K : ℝ) = max 1 (C + ‖z‖) := rfl
  have hbound : ∀ t ∈ Set.Ioo a b, ‖q t - z‖ ≤ (K : ℝ) := by
    intro t ht
    have h1 : ‖q t‖ ≤ C := hC t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h2 : ‖q t - z‖ ≤ ‖q t‖ + ‖z‖ := norm_sub_le _ _
    rw [hKcoe]
    exact le_trans h2 (le_trans (by linarith) (le_max_right _ _))
  have hlip : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K (V t) Set.univ := by
    intro t ht
    rw [lipschitzOnWith_univ]
    refine LipschitzWith.of_dist_le_mul fun w₁ w₂ => ?_
    have hd : dist ((q t - z) * w₁.1) ((q t - z) * w₂.1) = ‖q t - z‖ * dist w₁.1 w₂.1 := by
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
    have h1 : (0 : ℝ) ≤ dist w₁.1 w₂.1 := dist_nonneg
    have h2 : (0 : ℝ) ≤ dist w₁.2 w₂.2 := dist_nonneg
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by rw [hKcoe]; exact le_max_left _ _
    have hqK := hbound t ht
    rw [Prod.dist_eq, Prod.dist_eq]
    simp only [hV, hd]
    refine max_le ?_ ?_
    · calc dist w₁.2 w₂.2 ≤ (K : ℝ) * dist w₁.2 w₂.2 := by nlinarith
        _ ≤ (K : ℝ) * max (dist w₁.1 w₂.1) (dist w₁.2 w₂.2) := by
              have := le_max_right (dist w₁.1 w₂.1) (dist w₁.2 w₂.2)
              nlinarith
    · calc ‖q t - z‖ * dist w₁.1 w₂.1 ≤ (K : ℝ) * dist w₁.1 w₂.1 := by nlinarith
        _ ≤ (K : ℝ) * max (dist w₁.1 w₂.1) (dist w₁.2 w₂.2) := by
              have := le_max_left (dist w₁.1 w₂.1) (dist w₁.2 w₂.2)
              nlinarith
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h0mem : (0 : ℝ) ∈ Set.Ioo a b := by
    constructor <;> [linarith [ha]; linarith [hb]]
  have hxmem : x ∈ Set.Ioo a b := by
    constructor
    · have := neg_abs_le x; simp only [ha]; linarith
    · have := le_abs_self x; simp only [hb]; linarith
  have hf : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun t => (u t, v t)) (V t (u t, v t)) t ∧ (u t, v t) ∈ (Set.univ : Set (ℂ × ℂ)) :=
    fun t _ => ⟨(h.deriv_left t).prodMk (h.deriv_right t), Set.mem_univ _⟩
  have hg : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (V t (0, 0)) t ∧
        ((0 : ℂ), (0 : ℂ)) ∈ (Set.univ : Set (ℂ × ℂ)) := by
    intro t _
    refine ⟨?_, Set.mem_univ _⟩
    have : V t (0, 0) = (0, 0) := by simp [hV]
    rw [this]
    exact hasDerivAt_const t _
  have key := ODE_solution_unique_of_mem_Ioo hlip h0mem hf hg (by simp [hu0, hv0])
  have := key hxmem
  simpa using congrArg Prod.fst this

/-- The map sending a solution to its initial data `(u 0, u' 0)`. -/
noncomputable def initialData (q : ℝ → ℂ) (z : ℂ) : solutionSubmodule q z →ₗ[ℂ] ℂ × ℂ where
  toFun u := ((u : ℝ → ℂ) 0, deriv (u : ℝ → ℂ) 0)
  map_add' := by
    rintro ⟨u₁, h₁⟩ ⟨u₂, h₂⟩
    have hd₁ : Differentiable ℝ u₁ := IsODESolution.differentiable h₁
    have hd₂ : Differentiable ℝ u₂ := IsODESolution.differentiable h₂
    have : deriv (u₁ + u₂) 0 = deriv u₁ 0 + deriv u₂ 0 := deriv_add (hd₁ 0) (hd₂ 0)
    simp [this]
  map_smul' := by
    rintro c ⟨u, hu⟩
    have hd : Differentiable ℝ u := IsODESolution.differentiable hu
    have : deriv (c • u) 0 = c • deriv u 0 := deriv_const_smul c (hd 0)
    simp [this]

theorem initialData_injective {q : ℝ → ℂ} (hq : WeakRegularity q) (z : ℂ) :
    Function.Injective (initialData q z) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨u, hu⟩ hzero
  obtain ⟨v, hp⟩ := hu
  have hcoords : u 0 = 0 ∧ deriv u 0 = 0 := by
    simpa [initialData, Prod.ext_iff] using hzero
  have hv0 : v 0 = 0 := by rw [← congrFun hp.deriv_eq 0]; exact hcoords.2
  have : u = 0 := hp.eq_zero_of_init hq hcoords.1 hv0
  exact Subtype.ext this

/-- The solution space of the ODE is at most two dimensional. -/
theorem finrank_solutionSubmodule_le {q : ℝ → ℂ} (hq : WeakRegularity q) (z : ℂ) :
    Module.finrank ℂ (solutionSubmodule q z) ≤ 2 := by
  have h := (initialData q z).finrank_le_finrank_of_injective (initialData_injective hq z)
  simpa using h

/-- **Weyl's deficiency space representation.**  For a weakly regular potential `q` and any
`z : ℂ`, the deficiency space of the maximal operator associated with `τ u = -u'' + q u`
is precisely the set of square integrable solutions of the differential equation
`-u'' + q u = z u`, and the space of all solutions of that equation is at most two
dimensional; in particular the deficiency index at `z` is at most `2`. -/
theorem deficiencyRepresentsODE_of_weakRegularity {q : ℝ → ℂ} (hq : WeakRegularity q) (z : ℂ) :
    deficiencySpace q z = {u | MemLp u 2 volume ∧ u ∈ solutionSubmodule q z} ∧
      Module.finrank ℂ (solutionSubmodule q z) ≤ 2 :=
  ⟨deficiencySpace_eq q z, finrank_solutionSubmodule_le hq z⟩

/-- The same statement for a continuous potential, where the weak regularity hypothesis is
discharged automatically. -/
theorem deficiencyRepresentsODE_of_continuous {q : ℝ → ℂ} (hq : Continuous q) (z : ℂ) :
    deficiencySpace q z = {u | MemLp u 2 volume ∧ u ∈ solutionSubmodule q z} ∧
      Module.finrank ℂ (solutionSubmodule q z) ≤ 2 :=
  deficiencyRepresentsODE_of_weakRegularity (WeakRegularity.of_continuous hq) z

end Brockian.Weyl.DeficiencyODE

