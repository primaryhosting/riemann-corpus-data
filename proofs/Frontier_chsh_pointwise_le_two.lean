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

namespace Frontier

open MeasureTheory

/-- A **local hidden-variable model** for a two-party, two-setting, ±1-outcome experiment.

A hidden variable `x` is drawn from a probability space `(Λ, μ)`.  Alice's outcome
`A a x` depends only on her setting `a : Bool` and on the hidden variable, and likewise
Bob's outcome `B b x` depends only on his setting `b : Bool` and on the hidden variable
(this is the *locality* assumption).  Outcomes are bounded by `1` in absolute value. -/
structure LHVModel where
  /-- The space of hidden variables. -/
  Λ : Type
  /-- The measurable structure on the hidden-variable space. -/
  mΛ : MeasurableSpace Λ
  /-- The distribution of the hidden variable. -/
  μ : Measure Λ
  /-- The hidden variable is distributed according to a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- Alice's outcome as a function of her setting and the hidden variable. -/
  A : Bool → Λ → ℝ
  /-- Bob's outcome as a function of his setting and the hidden variable. -/
  B : Bool → Λ → ℝ
  measA : ∀ a, Measurable (A a)
  measB : ∀ b, Measurable (B b)
  boundA : ∀ a x, |A a x| ≤ 1
  boundB : ∀ b x, |B b x| ≤ 1

attribute [instance] LHVModel.mΛ LHVModel.prob

/-- The correlation predicted by a local hidden-variable model for settings `a`, `b`:
the expectation of the product of the two outcomes. -/
noncomputable def LHVModel.corr (M : LHVModel) (a b : Bool) : ℝ :=
  ∫ x, M.A a x * M.B b x ∂M.μ

/-- The CHSH combination of four correlation values. -/
def chsh (E : Bool → Bool → ℝ) : ℝ :=
  E false false + E false true + E true false - E true true

/-- Pointwise CHSH bound for numbers bounded by `1` in absolute value. -/
theorem chsh_pointwise_le_two (a0 a1 b0 b1 : ℝ) (h0 : |a0| ≤ 1) (h1 : |a1| ≤ 1)
    (g0 : |b0| ≤ 1) (g1 : |b1| ≤ 1) :
    a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 ≤ 2 := by
  have e0 : a0 * (b0 + b1) ≤ |b0 + b1| := by
    calc a0 * (b0 + b1) ≤ |a0 * (b0 + b1)| := le_abs_self _
      _ = |a0| * |b0 + b1| := abs_mul _ _
      _ ≤ 1 * |b0 + b1| := by gcongr
      _ = |b0 + b1| := one_mul _
  have e1 : a1 * (b0 - b1) ≤ |b0 - b1| := by
    calc a1 * (b0 - b1) ≤ |a1 * (b0 - b1)| := le_abs_self _
      _ = |a1| * |b0 - b1| := abs_mul _ _
      _ ≤ 1 * |b0 - b1| := by gcongr
      _ = |b0 - b1| := one_mul _
  rcases abs_cases (b0 + b1) with ⟨p1, _⟩ | ⟨p1, _⟩ <;>
    rcases abs_cases (b0 - b1) with ⟨p2, _⟩ | ⟨p2, _⟩ <;>
      rw [abs_le] at g0 g1 <;> nlinarith [e0, e1]

/-- Products of outcomes are integrable in any local hidden-variable model. -/
theorem LHVModel.integrable_prod (M : LHVModel) (a b : Bool) :
    Integrable (fun x => M.A a x * M.B b x) M.μ := by
  refine Integrable.of_bound ((M.measA a).mul (M.measB b)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_one₀ (M.boundA a x) (abs_nonneg _) (M.boundB b x)

/-- **Bell/CHSH inequality**: every local hidden-variable model satisfies `CHSH ≤ 2`. -/
theorem chsh_le_two (M : LHVModel) : chsh M.corr ≤ 2 := by
  have hsum : chsh M.corr =
      ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
            + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ := by
    have s1 := integral_add (M.integrable_prod false false) (M.integrable_prod false true)
    have s2 := integral_add ((M.integrable_prod false false).add (M.integrable_prod false true))
      (M.integrable_prod true false)
    have s3 := integral_sub (((M.integrable_prod false false).add
      (M.integrable_prod false true)).add (M.integrable_prod true false))
      (M.integrable_prod true true)
    simp only [Pi.add_apply] at s2 s3
    rw [s3, s2, s1]
    rfl
  rw [hsum]
  have hint : Integrable (fun x => M.A false x * M.B false x + M.A false x * M.B true x
      + M.A true x * M.B false x - M.A true x * M.B true x) M.μ :=
    (((M.integrable_prod false false).add (M.integrable_prod false true)).add
      (M.integrable_prod true false)).sub (M.integrable_prod true true)
  have hle : ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
      + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ
      ≤ ∫ _x, (2 : ℝ) ∂M.μ := by
    refine integral_mono hint (integrable_const 2) (fun x => ?_)
    exact chsh_pointwise_le_two _ _ _ _ (M.boundA false x) (M.boundA true x)
      (M.boundB false x) (M.boundB true x)
  simpa using hle

/-- A deterministic local hidden-variable model achieving the CHSH value `2`:
Alice always outputs `+1`, and Bob outputs `+1` for his first setting and `-1` for the second.
In particular local hidden-variable models exist, so `Frontier.bell_theorem` is not vacuous,
and the bound in `Frontier.chsh_le_two` is sharp. -/
noncomputable def extremalLHVModel : LHVModel where
  Λ := Unit
  mΛ := inferInstance
  μ := Measure.dirac ()
  prob := inferInstance
  A := fun _ _ => 1
  B := fun b _ => if b then -1 else 1
  measA := fun _ => measurable_const
  measB := fun _ => measurable_const
  boundA := fun _ _ => by norm_num
  boundB := fun b _ => by cases b <;> norm_num

/-- The bound `CHSH ≤ 2` for local hidden-variable models is attained. -/
theorem chsh_extremalLHVModel : chsh extremalLHVModel.corr = 2 := by
  simp [chsh, LHVModel.corr, extremalLHVModel]
  norm_num

/-- Alice's two measurement directions (angles). -/
noncomputable def angleA (a : Bool) : ℝ := if a then Real.pi / 2 else 0

/-- Bob's two measurement directions (angles). -/
noncomputable def angleB (b : Bool) : ℝ := if b then -(Real.pi / 4) else Real.pi / 4

/-- The quantum-mechanical correlations for a maximally entangled two-qubit state measured
along the directions `angleA a` and `angleB b`: `E(a,b) = cos (angleA a - angleB b)`. -/
noncomputable def quantumCorr (a b : Bool) : ℝ := Real.cos (angleA a - angleB b)

/-- The quantum correlations violate the CHSH bound: their CHSH value is `2 √2`. -/
theorem chsh_quantumCorr : chsh quantumCorr = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (Real.pi / 2 - -(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
    have : Real.pi / 2 - -(Real.pi / 4) = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, h4]
  have hneg : Real.cos (0 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [zero_sub, Real.cos_neg, h4]
  have h2 : Real.cos (0 - -(Real.pi / 4)) = Real.sqrt 2 / 2 := by
    have : (0 : ℝ) - -(Real.pi / 4) = Real.pi / 4 := by ring
    rw [this, h4]
  have h3 : Real.cos (Real.pi / 2 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    have : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [this, h4]
  simp only [chsh, quantumCorr, angleA, angleB, if_true, if_false, Bool.false_eq_true]
  rw [hneg, h2, h3, h34]
  ring

/-- **Bell's theorem**: no local hidden-variable model reproduces the quantum correlations.

Indeed, every local hidden-variable model obeys the CHSH inequality `CHSH ≤ 2`
(`Frontier.chsh_le_two`), whereas the quantum correlations achieve `CHSH = 2√2 > 2`. -/
theorem bell_theorem : ¬ ∃ M : LHVModel, ∀ a b : Bool, M.corr a b = quantumCorr a b := by
  rintro ⟨M, hM⟩
  have hEq : chsh M.corr = chsh quantumCorr := by
    simp only [chsh, hM]
  have h1 : chsh M.corr ≤ 2 := chsh_le_two M
  rw [hEq, chsh_quantumCorr] at h1
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

end Frontier

