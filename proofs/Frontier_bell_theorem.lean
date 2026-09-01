/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH bound: for outcomes in `[-1, 1]` (deterministic hidden-variable outcomes),
the CHSH combination is bounded by `2`. -/
theorem chsh_pointwise {a b c d : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) :
    a * c + a * d + b * c - b * d ≤ 2 := by
  have hcd : |c + d| + |c - d| ≤ 2 := by
    rw [abs_le] at hc hd
    rcases abs_cases (c + d) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (c - d) with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h, h'] <;>
        linarith [hc.1, hc.2, hd.1, hd.2]
  have h1 : a * (c + d) ≤ |c + d| := by
    calc a * (c + d) ≤ |a * (c + d)| := le_abs_self _
      _ = |a| * |c + d| := abs_mul _ _
      _ ≤ 1 * |c + d| := by gcongr
      _ = |c + d| := one_mul _
  have h2 : b * (c - d) ≤ |c - d| := by
    calc b * (c - d) ≤ |b * (c - d)| := le_abs_self _
      _ = |b| * |c - d| := abs_mul _ _
      _ ≤ 1 * |c - d| := by gcongr
      _ = |c - d| := one_mul _
  nlinarith [h1, h2, hcd]

variable {Λ : Type*} [MeasurableSpace Λ]

/-- A product of two bounded measurable functions is integrable w.r.t. a probability measure. -/
theorem integrable_mul_of_bounded {μ : Measure Λ} [IsProbabilityMeasure μ] {f g : Λ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, |f x| ≤ 1) (hg1 : ∀ x, |g x| ≤ 1) :
    Integrable (fun x => f x * g x) μ := by
  refine (integrable_const (1 : ℝ)).mono' (hf.mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  calc ‖f x * g x‖ = |f x| * |g x| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ 1 * 1 := by
        gcongr <;> [exact abs_nonneg _; exact hf1 x; exact hg1 x]
    _ = 1 := one_mul _
  
/-- **Bell's theorem / CHSH inequality for local hidden-variable models.**

A local hidden-variable model consists of a probability space `(Λ, μ)` of hidden variables
together with response functions `A₀, A₁` (Alice's two measurement settings) and `B₀, B₁`
(Bob's two settings), each taking values in `[-1, 1]`; the correlation predicted for a pair
of settings is `E(Aᵢ, Bⱼ) = ∫ Aᵢ Bⱼ dμ`.

The conclusion has two parts:

1. *(CHSH ≤ 2 classically.)* Every such model satisfies
   `E(A₀,B₀) + E(A₀,B₁) + E(A₁,B₀) - E(A₁,B₁) ≤ 2`.

2. *(No local hidden-variable model reproduces quantum mechanics.)* Consequently no such model
   can reproduce the quantum correlations of the singlet state at the optimal CHSH angles,
   namely `E(A₀,B₀) = E(A₀,B₁) = E(A₁,B₀) = √2/2` and `E(A₁,B₁) = -√2/2`, since those values
   give the CHSH combination the value `2√2 > 2`.
-/
theorem bell_theorem (μ : Measure Λ) [IsProbabilityMeasure μ] (A₀ A₁ B₀ B₁ : Λ → ℝ)
    (hA₀ : Measurable A₀) (hA₁ : Measurable A₁) (hB₀ : Measurable B₀) (hB₁ : Measurable B₁)
    (hA₀1 : ∀ x, |A₀ x| ≤ 1) (hA₁1 : ∀ x, |A₁ x| ≤ 1)
    (hB₀1 : ∀ x, |B₀ x| ≤ 1) (hB₁1 : ∀ x, |B₁ x| ≤ 1) :
    (∫ x, A₀ x * B₀ x ∂μ) + (∫ x, A₀ x * B₁ x ∂μ) + (∫ x, A₁ x * B₀ x ∂μ)
        - (∫ x, A₁ x * B₁ x ∂μ) ≤ 2 ∧
      ¬ ((∫ x, A₀ x * B₀ x ∂μ) = Real.sqrt 2 / 2 ∧ (∫ x, A₀ x * B₁ x ∂μ) = Real.sqrt 2 / 2 ∧
          (∫ x, A₁ x * B₀ x ∂μ) = Real.sqrt 2 / 2 ∧
          (∫ x, A₁ x * B₁ x ∂μ) = -(Real.sqrt 2 / 2)) := by
  have i₀₀ : Integrable (fun x => A₀ x * B₀ x) μ :=
    integrable_mul_of_bounded hA₀ hB₀ hA₀1 hB₀1
  have i₀₁ : Integrable (fun x => A₀ x * B₁ x) μ :=
    integrable_mul_of_bounded hA₀ hB₁ hA₀1 hB₁1
  have i₁₀ : Integrable (fun x => A₁ x * B₀ x) μ :=
    integrable_mul_of_bounded hA₁ hB₀ hA₁1 hB₀1
  have i₁₁ : Integrable (fun x => A₁ x * B₁ x) μ :=
    integrable_mul_of_bounded hA₁ hB₁ hA₁1 hB₁1
  have key : (∫ x, A₀ x * B₀ x ∂μ) + (∫ x, A₀ x * B₁ x ∂μ) + (∫ x, A₁ x * B₀ x ∂μ)
      - (∫ x, A₁ x * B₁ x ∂μ) ≤ 2 := by
    have hsum : (∫ x, A₀ x * B₀ x ∂μ) + (∫ x, A₀ x * B₁ x ∂μ) + (∫ x, A₁ x * B₀ x ∂μ)
        - (∫ x, A₁ x * B₁ x ∂μ)
        = ∫ x, (A₀ x * B₀ x + A₀ x * B₁ x + A₁ x * B₀ x - A₁ x * B₁ x) ∂μ := by
      rw [integral_sub (((i₀₀.add i₀₁).add i₁₀)) i₁₁, integral_add (i₀₀.add i₀₁) i₁₀,
        integral_add i₀₀ i₀₁]
    rw [hsum]
    have hle : ∫ x, (A₀ x * B₀ x + A₀ x * B₁ x + A₁ x * B₀ x - A₁ x * B₁ x) ∂μ
        ≤ ∫ _x, (2 : ℝ) ∂μ := by
      refine integral_mono (((i₀₀.add i₀₁).add i₁₀).sub i₁₁) (integrable_const _)
        (fun x => chsh_pointwise (hA₀1 x) (hA₁1 x) (hB₀1 x) (hB₁1 x))
    simpa using hle
  refine ⟨key, ?_⟩
  rintro ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩
  rw [h₀₀, h₀₁, h₁₀, h₁₁] at key
  have h2 : (1.41 : ℝ) < Real.sqrt 2 := by
    have : (1.41 : ℝ) = Real.sqrt (1.41 ^ 2) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Frontier

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

