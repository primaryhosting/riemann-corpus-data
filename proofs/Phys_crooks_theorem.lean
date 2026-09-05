/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- The work distribution associated with a path weight `p : Γ → ℝ` and a work
functional `W : Γ → ℝ`: the total weight of all trajectories performing work `w`. -/
noncomputable def workDist {Γ : Type*} [Fintype Γ] (W : Γ → ℝ) (p : Γ → ℝ) (w : ℝ) : ℝ :=
  ∑ g : Γ, if W g = w then p g else 0

/-- **Crooks fluctuation theorem.**

Setting: a finite set `Γ` of microscopic trajectories, a time-reversal involution
`rev : Γ → Γ`, a work functional `W` that is odd under time reversal
(`W (rev g) = - W g`), and path weights `pF`, `pR` for the forward and the reverse
protocol satisfying *microscopic reversibility*
`pF g = exp (β * (W g - ΔF)) * pR (rev g)`.

Conclusion: the forward and reverse work distributions satisfy
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`. -/
theorem crooks_theorem {Γ : Type*} [Fintype Γ] (rev : Γ → Γ)
    (hrev : Function.Involutive rev) (W : Γ → ℝ) (hW : ∀ g : Γ, W (rev g) = -W g)
    (pF pR : Γ → ℝ) (beta dF : ℝ)
    (hmicro : ∀ g : Γ, pF g = Real.exp (beta * (W g - dF)) * pR (rev g)) (w : ℝ) :
    workDist W pF w = Real.exp (beta * (w - dF)) * workDist W pR (-w) := by
  unfold Phys.workDist
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective rev hrev.bijective _ _ ?_
  intro g
  by_cases hg : W g = w
  · rw [if_pos hg, hW g, hg, if_pos rfl, hmicro g, hg]
  · rw [if_neg hg, hW g, if_neg (by simpa using hg), mul_zero]

/-- Ratio form of the Crooks fluctuation theorem: whenever the reverse work
distribution at `-w` is nonzero, `P_F(w) / P_R(-w) = e^{β (w - ΔF)}`. -/
theorem crooks_theorem_ratio {Γ : Type*} [Fintype Γ] (rev : Γ → Γ)
    (hrev : Function.Involutive rev) (W : Γ → ℝ) (hW : ∀ g : Γ, W (rev g) = -W g)
    (pF pR : Γ → ℝ) (beta dF : ℝ)
    (hmicro : ∀ g : Γ, pF g = Real.exp (beta * (W g - dF)) * pR (rev g)) (w : ℝ)
    (hne : workDist W pR (-w) ≠ 0) :
    workDist W pF w / workDist W pR (-w) = Real.exp (beta * (w - dF)) := by
  rw [crooks_theorem rev hrev W hW pF pR beta dF hmicro w,
    mul_div_assoc, div_self hne, mul_one]

end Phys

