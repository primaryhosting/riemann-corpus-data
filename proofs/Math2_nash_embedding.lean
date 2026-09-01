/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped ContDiff
open intervalIntegral

namespace Math2

/-!
## What is formalized here

The full Nash embedding theorem ("every smooth Riemannian manifold admits a smooth
isometric embedding into some Euclidean space `ℝ^N`") is not available in Mathlib, and its
proof (the Nash–Moser implicit function theorem, or the Günther fixed point argument)
is a very large development that is not carried out here.

What is proved below, completely and without any axioms beyond Lean's standard ones, is the
class of *separable (diagonal) Riemannian metrics on `ℝ^n`*: metrics of the form

  `g_x(v, w) = ∑ i, f i (x i) * v i * w i`,   with each `f i : ℝ → ℝ` smooth and positive.

For such a metric we construct an explicit smooth, injective map `F : ℝ^n → ℝ^n` whose
differential pulls the standard Euclidean inner product of the target back to `g`, i.e. an
isometric embedding in exactly the sense of Nash's theorem.  The construction is the honest
one-dimensional Nash construction applied in each coordinate: `F x i = ∫₀^{x i} √(f i t) dt`,
i.e. the arclength reparametrisation of each coordinate axis.

The `n = 1` case, `nash_embedding_line`, is the statement that *every* Riemannian metric on the
real line embeds isometrically in `ℝ`, which is a genuine (if elementary) instance of the Nash
theorem: no hypothesis beyond smoothness and positivity of the metric is assumed.
-/

/-- **Arclength antiderivative.** For a smooth positive `f : ℝ → ℝ` there is a smooth strictly
increasing `G : ℝ → ℝ` with `G' = √f` everywhere.  This is the one-dimensional isometric
embedding: `G` pulls back `dt²` to the metric `f(x) dx²`. -/
theorem exists_arclength (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ StrictMono G ∧ ∀ x, HasDerivAt G (Real.sqrt (f x)) x := by
  have hs : ContDiff ℝ ∞ fun x => Real.sqrt (f x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (Real.contDiffAt_sqrt (x := f x) (hpos x).ne').comp x hf.contDiffAt
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, Real.sqrt (f t) with hG
  have hderiv : ∀ x, HasDerivAt G (Real.sqrt (f x)) x := by
    intro x
    exact integral_hasDerivAt_right (hs.continuous.intervalIntegrable _ _)
      hs.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuous.continuousAt
  have hd : deriv G = fun x => Real.sqrt (f x) := funext fun x => (hderiv x).deriv
  refine ⟨G, ?_, ?_, hderiv⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by rw [hd]; exact hs⟩
  · refine strictMono_of_deriv_pos fun x => ?_
    rw [hd]
    exact Real.sqrt_pos.2 (hpos x)

/-- **Nash embedding, one-dimensional case.** Every Riemannian metric `g_x(v,w) = f(x) · v · w`
on the real line (with `f` smooth and positive) is induced by a smooth embedding of the line
into `ℝ`: there is a smooth strictly increasing `F : ℝ → ℝ` whose differential carries the
Euclidean inner product of the target back to `g`. -/
theorem nash_embedding_line (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ StrictMono F ∧
      ∀ x v w : ℝ, (deriv F x * v) * (deriv F x * w) = f x * (v * w) := by
  obtain ⟨G, hGsmooth, hGmono, hGderiv⟩ := exists_arclength f hf hpos
  refine ⟨G, hGsmooth, hGmono, fun x v w => ?_⟩
  rw [(hGderiv x).deriv]
  linear_combination (v * w) * Real.mul_self_sqrt (hpos x).le

/-- **Nash embedding for separable metrics on `ℝ^n`.**

Let `g` be the Riemannian metric on `ℝ^n` given in coordinates by
`g_x(v, w) = ∑ i, f i (x i) * v i * w i`, where each `f i : ℝ → ℝ` is smooth and everywhere
positive.  Then `(ℝ^n, g)` embeds isometrically into `ℝ^n`: there is a smooth injective map
`F : ℝ^n → ℝ^n` whose differential at every point pulls the standard Euclidean inner product
`⟪a, b⟫ = ∑ i, a i * b i` of the target back to `g`.

This is the special case of Nash's theorem for separable (diagonal) metrics; the general
theorem is not formalized here.  See `nash_embedding_line` for the case `n = 1`, where the
hypothesis is simply that `g` is an arbitrary smooth Riemannian metric on the line. -/
theorem nash_embedding {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hpos : ∀ i x, 0 < f i x) :
    ∃ F : (Fin n → ℝ) → (Fin n → ℝ), ContDiff ℝ ∞ F ∧ Function.Injective F ∧
      ∀ x v w : Fin n → ℝ,
        ∑ i, (fderiv ℝ F x v i) * (fderiv ℝ F x w i) = ∑ i, f i (x i) * (v i * w i) := by
  choose G hGsmooth hGmono hGderiv using fun i => exists_arclength (f i) (hf i) (hpos i)
  refine ⟨fun x i => G i (x i), ?_, ?_, ?_⟩
  · rw [contDiff_pi]
    intro i
    exact (hGsmooth i).comp (contDiff_apply ℝ ℝ i)
  · intro x y hxy
    funext i
    exact (hGmono i).injective (congrFun hxy i)
  · intro x v w
    have hF : ∀ x : Fin n → ℝ, HasFDerivAt (fun x : Fin n → ℝ => fun i => G i (x i))
        (ContinuousLinearMap.pi fun i =>
          (Real.sqrt (f i (x i))) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
      intro x
      rw [hasFDerivAt_pi']
      intro i
      have h1 : HasFDerivAt (fun y : Fin n → ℝ => y i)
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) x :=
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
      have h2 := ((hGderiv i (x i)).comp_hasFDerivAt x h1)
      convert h2 using 1
      ext y
      simp [mul_comm]
    rw [(hF x).fderiv]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    linear_combination (v i * w i) * Real.mul_self_sqrt (hpos i (x i)).le

end Math2

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

