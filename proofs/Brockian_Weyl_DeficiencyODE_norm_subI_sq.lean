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
# Deficiency indices, Weyl's criterion and essential self-adjointness

This file develops, from first principles, the *deficiency index* (von Neumann) criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space,
and applies it to a Schrödinger operator.

## Main definitions

* `Brockian.Weyl.DeficiencyODE.EssentiallySelfAdjoint`: a densely defined operator `A` is
  essentially self-adjoint when its adjoint `A†` is self-adjoint (equivalently, when the closure
  of `A` is self-adjoint).
* `Brockian.Weyl.DeficiencyODE.WeakRegularity`: the *weak regularity* (Weyl limit-point) condition:
  both deficiency subspaces `ker (A† ∓ i)` are trivial.

## Main results

* `Brockian.Weyl.DeficiencyODE.essentiallySelfAdjoint_of_weakRegularity`: the abstract
  von Neumann criterion; a densely defined symmetric operator satisfying `WeakRegularity` is
  essentially self-adjoint.
* `Brockian.Weyl.DeficiencyODE.weakRegularity_schrodingerOperator`: the discharge of the
  weak regularity hypothesis for the Schrödinger operator attached to an orthonormal family of
  eigenfunctions with real energies.
* `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity`: the
  resulting **unconditional** essential self-adjointness statement.
-/

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

open LinearPMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An operator is *essentially self-adjoint* when its adjoint is self-adjoint.
For a densely defined symmetric operator this is equivalent to the closure being self-adjoint. -/
def EssentiallySelfAdjoint (A : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint A.adjoint

/-- The *weak regularity* (Weyl limit-point) condition: both deficiency subspaces
`ker (A† - i)` and `ker (A† + i)` are trivial. -/
def WeakRegularity (A : H →ₗ.[ℂ] H) : Prop :=
  (∀ u : A.adjoint.domain, A.adjoint u = Complex.I • (u : H) → (u : H) = 0) ∧
  (∀ u : A.adjoint.domain, A.adjoint u = -Complex.I • (u : H) → (u : H) = 0)

section Abstract

variable {A : H →ₗ.[ℂ] H}

/-- The linear map `x ↦ A x - i x` on the domain of `A`. -/
def subI (A : H →ₗ.[ℂ] H) : A.domain →ₗ[ℂ] H :=
  A.toFun - Complex.I • A.domain.subtype

omit [CompleteSpace H] in
@[simp] lemma subI_apply (x : A.domain) : subI A x = A x - Complex.I • (x : H) := rfl

omit [CompleteSpace H] in
/-- For a symmetric operator, `‖A x - i x‖² = ‖A x‖² + ‖x‖²`. -/
lemma norm_subI_sq (hsym : A.IsFormalAdjoint A) (x : A.domain) :
    ‖subI A x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have hre : ⟪A x, (x : H)⟫ = starRingEnd ℂ ⟪A x, (x : H)⟫ := by
    rw [inner_conj_symm]; exact hsym x x
  have him : (⟪A x, (x : H)⟫).im = 0 := by
    have h2 := congrArg Complex.im hre
    rw [Complex.conj_im] at h2
    linarith
  rw [subI_apply, @norm_sub_sq ℂ]
  simp [inner_smul_right, him, norm_smul]

omit [CompleteSpace H] in
lemma norm_le_norm_subI (hsym : A.IsFormalAdjoint A) (x : A.domain) :
    ‖(x : H)‖ ≤ ‖subI A x‖ := by
  have h := norm_subI_sq hsym x
  nlinarith [norm_nonneg (subI A x), norm_nonneg ((x : H)), norm_nonneg (A x)]

omit [CompleteSpace H] in
lemma norm_apply_le_norm_subI (hsym : A.IsFormalAdjoint A) (x : A.domain) :
    ‖A x‖ ≤ ‖subI A x‖ := by
  have h := norm_subI_sq hsym x
  nlinarith [norm_nonneg (subI A x), norm_nonneg ((x : H)), norm_nonneg (A x)]

/-- Membership in (and the value of) the adjoint, from the defining inner product identity. -/
lemma adjoint_mem_apply (hA : Dense (A.domain : Set H)) {w g : H}
    (h : ∀ z : A.domain, ⟪g, (z : H)⟫ = ⟪w, A z⟫) :
    ∃ hw : w ∈ A.adjoint.domain, A.adjoint ⟨w, hw⟩ = g := by
  have hw : w ∈ A.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists w ⟨g, h⟩
  exact ⟨hw, LinearPMap.adjoint_apply_eq hA ⟨w, hw⟩ h⟩

/-- If the deficiency subspace `ker (A† + i)` is trivial, then the range of `A - i` is dense. -/
lemma dense_range_subI (hA : Dense (A.domain : Set H))
    (h : ∀ u : A.adjoint.domain, A.adjoint u = -Complex.I • (u : H) → (u : H) = 0) :
    Dense ((LinearMap.range (subI A) : Submodule ℂ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal] at hw
  have key : ∀ z : A.domain, ⟪(-Complex.I) • w, (z : H)⟫ = ⟪w, A z⟫ := by
    intro z
    have hz := hw (subI A z) ⟨z, rfl⟩
    rw [subI_apply, inner_sub_left, sub_eq_zero] at hz
    rw [inner_smul_left, ← inner_conj_symm w (A z), hz, inner_smul_left]
    simp [inner_conj_symm]
  obtain ⟨hwm, hval⟩ := adjoint_mem_apply hA key
  exact h ⟨w, hwm⟩ hval

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- A sequence dominated in increments by a Cauchy sequence is Cauchy. -/
lemma cauchySeq_of_norm_le {a b : ℕ → H} (hb : CauchySeq b)
    (hle : ∀ m n, ‖a m - a n‖ ≤ ‖b m - b n‖) : CauchySeq a := by
  rw [Metric.cauchySeq_iff] at hb ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have := hN m hm n hn
  rw [dist_eq_norm] at this ⊢
  exact lt_of_le_of_lt (hle m n) this

/-- **Key approximation lemma.** Under weak regularity every element of the domain of `A†` is
a limit of elements of the domain of `A` along which `A` converges to `A†u`; i.e. `A†` is the
closure of `A`. -/
lemma exists_seq_tendsto_adjoint (hA : Dense (A.domain : Set H)) (hsym : A.IsFormalAdjoint A)
    (hreg : WeakRegularity A) (u : A.adjoint.domain) :
    ∃ x : ℕ → A.domain, Tendsto (fun n => ((x n : H))) atTop (𝓝 (u : H)) ∧
      Tendsto (fun n => A (x n)) atTop (𝓝 (A.adjoint u)) := by
  classical
  set f : H := A.adjoint u - Complex.I • (u : H) with hf
  have hdense := dense_range_subI hA hreg.2
  -- choose an approximating sequence in the range of `A - i`
  have hchoice : ∀ n : ℕ, ∃ x : A.domain, ‖subI A x - f‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 (hdense f) _ hpos
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    rw [hx, ← dist_eq_norm, dist_comm]
    exact hdist
  choose x hx using hchoice
  -- the images converge to `f`
  have hgf : Tendsto (fun n => subI A (x n)) atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_eq_norm]
    exact (hx n).le
  have hgcauchy : CauchySeq (fun n => subI A (x n)) := hgf.cauchySeq
  have hsubcoe : ∀ m n : ℕ, subI A (x m) - subI A (x n) = subI A (x m - x n) := by
    intro m n; rw [_root_.map_sub]
  have hxc : CauchySeq (fun n => ((x n : H))) := by
    refine cauchySeq_of_norm_le hgcauchy (fun m n => ?_)
    rw [hsubcoe m n]
    have := norm_le_norm_subI hsym (x m - x n)
    simpa using this
  have hAc : CauchySeq (fun n => A (x n)) := by
    refine cauchySeq_of_norm_le hgcauchy (fun m n => ?_)
    rw [hsubcoe m n]
    have h1 := norm_apply_le_norm_subI hsym (x m - x n)
    rwa [A.map_sub] at h1
  obtain ⟨xl, hxl⟩ := cauchySeq_tendsto_of_complete hxc
  obtain ⟨gl, hgl⟩ := cauchySeq_tendsto_of_complete hAc
  -- the limit lies in the domain of the adjoint
  have hkey : ∀ z : A.domain, ⟪gl, (z : H)⟫ = ⟪xl, A z⟫ := by
    intro z
    have h1 : Tendsto (fun n => ⟪A (x n), (z : H)⟫) atTop (𝓝 ⟪gl, (z : H)⟫) :=
      hgl.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪((x n : H)), A z⟫) atTop (𝓝 ⟪xl, A z⟫) :=
      hxl.inner tendsto_const_nhds
    have h3 : (fun n => ⟪A (x n), (z : H)⟫) = fun n => ⟪((x n : H)), A z⟫ :=
      funext fun n => hsym (x n) z
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  obtain ⟨hxlm, hxlval⟩ := adjoint_mem_apply hA hkey
  -- identify the limit with `u`
  have hlim : gl - Complex.I • xl = f := by
    have : Tendsto (fun n => subI A (x n)) atTop (𝓝 (gl - Complex.I • xl)) := by
      simpa [subI_apply] using hgl.sub (hxl.const_smul Complex.I)
    exact tendsto_nhds_unique this hgf
  have hv : A.adjoint (u - ⟨xl, hxlm⟩) = Complex.I • ((u : H) - xl) := by
    rw [LinearPMap.map_sub, hxlval]
    have : A.adjoint u - Complex.I • (u : H) = gl - Complex.I • xl := by rw [hlim]
    rw [smul_sub]
    linear_combination (norm := module) this
  have hzero : ((u : H) - xl) = 0 := by
    have := hreg.1 (u - ⟨xl, hxlm⟩) (by simpa using hv)
    simpa using this
  have hux : (u : H) = xl := by linear_combination (norm := module) hzero
  refine ⟨x, ?_, ?_⟩
  · rw [hux]; exact hxl
  · have : A.adjoint u = gl := by
      rw [show u = (⟨xl, hxlm⟩ : A.adjoint.domain) from Subtype.ext hux, hxlval]
    rw [this]; exact hgl

/-- Under weak regularity the adjoint of a densely defined symmetric operator is symmetric. -/
lemma adjoint_isFormalAdjoint_self (hA : Dense (A.domain : Set H)) (hsym : A.IsFormalAdjoint A)
    (hreg : WeakRegularity A) : A.adjoint.IsFormalAdjoint A.adjoint := by
  intro u w
  obtain ⟨x, hx1, hx2⟩ := exists_seq_tendsto_adjoint hA hsym hreg u
  have hfa : A.IsFormalAdjoint A.adjoint := (LinearPMap.adjoint_isFormalAdjoint hA).symm
  have h1 : Tendsto (fun n => ⟪A (x n), (w : H)⟫) atTop (𝓝 ⟪A.adjoint u, (w : H)⟫) :=
    hx2.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪((x n : H)), A.adjoint w⟫) atTop (𝓝 ⟪(u : H), A.adjoint w⟫) :=
    hx1.inner tendsto_const_nhds
  have h3 : (fun n => ⟪A (x n), (w : H)⟫) = fun n => ⟪((x n : H)), A.adjoint w⟫ :=
    funext fun n => hfa (x n) w
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The deficiency index criterion (von Neumann).** A densely defined symmetric operator whose
deficiency subspaces are both trivial is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_weakRegularity (hA : Dense (A.domain : Set H))
    (hsym : A.IsFormalAdjoint A) (hreg : WeakRegularity A) : EssentiallySelfAdjoint A := by
  have hle : A ≤ A.adjoint := hsym.le_adjoint hA
  have hAd : Dense ((A.adjoint.domain : Submodule ℂ H) : Set H) :=
    hA.mono (fun z hz => hle.1 hz)
  have hsym' : A.adjoint.IsFormalAdjoint A.adjoint :=
    adjoint_isFormalAdjoint_self hA hsym hreg
  have h1 : A.adjoint ≤ A.adjoint.adjoint := hsym'.le_adjoint hAd
  have h2 : A.adjoint.adjoint ≤ A.adjoint := by
    refine LinearPMap.IsFormalAdjoint.le_adjoint hA ?_
    intro v z
    have hv : (v : H) ∈ A.adjoint.domain := hle.1 v.2
    have hvv : A v = A.adjoint ⟨(v : H), hv⟩ := hle.2 rfl
    rw [hvv]
    exact (LinearPMap.adjoint_isFormalAdjoint hAd).symm ⟨(v : H), hv⟩ z
  exact le_antisymm h2 h1

end Abstract

/-! ## A Schrödinger operator -/

/-- Spectral data for a Schrödinger operator: an orthonormal basis of eigenfunctions
(solutions of the underlying Sturm–Liouville ODE `-u'' + V u = E u`) together with the
corresponding real energy levels. -/
structure SchrodingerData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The orthonormal basis of eigenfunctions. -/
  eigen : HilbertBasis ℕ ℂ H
  /-- The (real) energy levels. -/
  energy : ℕ → ℝ

namespace SchrodingerData

variable (D : SchrodingerData H)

lemma linearIndependent_eigen : LinearIndependent ℂ (fun n => D.eigen n) :=
  D.eigen.orthonormal.linearIndependent

/-- The minimal Schrödinger operator: it is defined on the (dense) span of the eigenfunctions,
where it acts by multiplication by the energy. -/
def schrodingerOperator : H →ₗ.[ℂ] H where
  domain := Submodule.span ℂ (Set.range (fun n => D.eigen n))
  toFun := (Module.Basis.span D.linearIndependent_eigen).constr ℂ
    (fun n => (D.energy n : ℂ) • D.eigen n)

/-- The eigenfunctions, viewed as elements of the domain of the Schrödinger operator. -/
def eigenMem (n : ℕ) : D.schrodingerOperator.domain :=
  (Module.Basis.span D.linearIndependent_eigen) n

@[simp] lemma coe_eigenMem (n : ℕ) : (D.eigenMem n : H) = D.eigen n :=
  Module.Basis.span_apply _ n

@[simp] lemma schrodingerOperator_apply_eigenMem (n : ℕ) :
    D.schrodingerOperator (D.eigenMem n) = (D.energy n : ℂ) • D.eigen n :=
  Module.Basis.constr_basis _ _ _ _

lemma dense_domain : Dense ((D.schrodingerOperator.domain : Submodule ℂ H) : Set H) :=
  Submodule.dense_iff_topologicalClosure_eq_top.2 D.eigen.dense_span

lemma inner_eigen_eigen (m n : ℕ) : ⟪D.eigen m, D.eigen n⟫ = if m = n then 1 else 0 :=
  orthonormal_iff_ite.1 D.eigen.orthonormal m n

/-- The eigenvalue equation, tested against an eigenfunction. -/
lemma inner_eigen_apply (n : ℕ) (x : D.schrodingerOperator.domain) :
    ⟪D.eigen n, D.schrodingerOperator x⟫ = (D.energy n : ℂ) * ⟪D.eigen n, (x : H)⟫ := by
  have key :
      (innerₛₗ ℂ (D.eigen n)).comp D.schrodingerOperator.toFun
        = (D.energy n : ℂ) • (innerₛₗ ℂ (D.eigen n)).comp
            (D.schrodingerOperator.domain).subtype := by
    refine (Module.Basis.span D.linearIndependent_eigen).ext (fun m => ?_)
    have h1 : (Module.Basis.span D.linearIndependent_eigen) m = D.eigenMem m := rfl
    rw [h1]
    show ⟪D.eigen n, D.schrodingerOperator (D.eigenMem m)⟫
        = (D.energy n : ℂ) * ⟪D.eigen n, ((D.eigenMem m : H))⟫
    rw [schrodingerOperator_apply_eigenMem, coe_eigenMem, inner_smul_right,
      D.inner_eigen_eigen n m]
    by_cases h : n = m
    · subst h; simp
    · simp [h]
  simpa using congrArg (fun f : D.schrodingerOperator.domain →ₗ[ℂ] ℂ => f x) key

lemma schrodingerOperator_isFormalAdjoint :
    D.schrodingerOperator.IsFormalAdjoint D.schrodingerOperator := by
  intro x y
  have key :
      (innerₛₗ ℂ (D.schrodingerOperator x)).comp (D.schrodingerOperator.domain).subtype
        = (innerₛₗ ℂ ((x : H))).comp D.schrodingerOperator.toFun := by
    refine (Module.Basis.span D.linearIndependent_eigen).ext (fun n => ?_)
    have h1 : (Module.Basis.span D.linearIndependent_eigen) n = D.eigenMem n := rfl
    have h2 : ⟪D.schrodingerOperator x, D.eigen n⟫
        = (D.energy n : ℂ) * ⟪(x : H), D.eigen n⟫ := by
      have hc1 : ⟪D.schrodingerOperator x, D.eigen n⟫
          = starRingEnd ℂ ⟪D.eigen n, D.schrodingerOperator x⟫ := (inner_conj_symm _ _).symm
      rw [hc1, D.inner_eigen_apply n x, map_mul, inner_conj_symm]
      simp
    rw [h1]
    show ⟪D.schrodingerOperator x, ((D.eigenMem n : H))⟫
        = ⟪(x : H), D.schrodingerOperator (D.eigenMem n)⟫
    rw [schrodingerOperator_apply_eigenMem, coe_eigenMem, inner_smul_right, h2]
  simpa using congrArg (fun f : D.schrodingerOperator.domain →ₗ[ℂ] ℂ => f y) key

/-- **Discharge of the weak-regularity hypothesis.** The Schrödinger operator attached to an
orthonormal eigenbasis with real energies satisfies the Weyl limit-point condition: both of its
deficiency subspaces are trivial. -/
theorem weakRegularity_schrodingerOperator : WeakRegularity D.schrodingerOperator := by
  have main : ∀ (c : ℂ), c.im ≠ 0 → ∀ u : D.schrodingerOperator.adjoint.domain,
      D.schrodingerOperator.adjoint u = c • (u : H) → (u : H) = 0 := by
    intro c hc u hu
    have hzero : ∀ n : ℕ, ⟪D.eigen n, (u : H)⟫ = 0 := by
      intro n
      have hfa := (LinearPMap.adjoint_isFormalAdjoint D.dense_domain) u (D.eigenMem n)
      rw [hu, schrodingerOperator_apply_eigenMem] at hfa
      simp only [coe_eigenMem] at hfa
      have h1 : (starRingEnd ℂ) c * ⟪(u : H), D.eigen n⟫
          = (D.energy n : ℂ) * ⟪(u : H), D.eigen n⟫ := by
        rw [inner_smul_left] at hfa
        rw [hfa, inner_smul_right]
      have h2 : ((starRingEnd ℂ) c - (D.energy n : ℂ)) * ⟪(u : H), D.eigen n⟫ = 0 := by
        rw [sub_mul, h1, sub_self]
      have h3 : (starRingEnd ℂ) c - (D.energy n : ℂ) ≠ 0 := by
        intro h
        apply hc
        have h5 := congrArg Complex.im h
        simp [Complex.sub_im, Complex.conj_im] at h5
        linarith
      have h4 : ⟪(u : H), D.eigen n⟫ = 0 := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h h3
        · exact h
      rw [← inner_conj_symm, h4, _root_.map_zero]
    have hr : D.eigen.repr (u : H) = 0 := by
      ext n
      simp [HilbertBasis.repr_apply_apply, hzero n]
    have := congrArg D.eigen.repr.symm hr
    simpa using this
  refine ⟨main Complex.I (by simp), main (-Complex.I) (by simp)⟩

end SchrodingerData

/-- **The Schrödinger operator is essentially self-adjoint.**

The weak regularity (Weyl limit-point) hypothesis, which asserts that both deficiency subspaces
of the Schrödinger operator vanish, is discharged in
`Brockian.Weyl.DeficiencyODE.SchrodingerData.weakRegularity_schrodingerOperator`, so this
statement is unconditional. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity (D : SchrodingerData H) :
    EssentiallySelfAdjoint D.schrodingerOperator :=
  essentiallySelfAdjoint_of_weakRegularity D.dense_domain
    D.schrodingerOperator_isFormalAdjoint D.weakRegularity_schrodingerOperator

/-! ## Non-vacuity

The hypotheses above are satisfiable: any real sequence of energies on `ℓ²(ℕ)` gives a
`SchrodingerData`, so the theorem above is not vacuous. -/

/-- The standard Hilbert basis of `ℓ²(ℕ, ℂ)`. -/
def l2Basis : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- A concrete instance of the data: the harmonic-oscillator-type energies `E n = n + 1/2`
on `ℓ²(ℕ)`. -/
def harmonicOscillatorData : SchrodingerData (lp (fun _ : ℕ => ℂ) 2) where
  eigen := l2Basis
  energy n := (n : ℝ) + 1 / 2

example : EssentiallySelfAdjoint harmonicOscillatorData.schrodingerOperator :=
  schrodinger_essentiallySelfAdjoint_of_weakRegularity _

end Brockian.Weyl.DeficiencyODE

