/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset

/-- The probability that a protocol with path weights `p` and work function `W`
produces total work `w`, in a finite path space. -/
noncomputable def workDist {Γ : Type*} [Fintype Γ] (p : Γ → ℝ) (W : Γ → ℝ) (w : ℝ) : ℝ :=
  ∑ g ∈ univ.filter (fun g => W g = w), p g

/-- Microscopic reversibility summed over all paths doing work `w`:
the forward work distribution equals `e^{β(w-ΔF)}` times the reverse work
distribution evaluated at `-w`. -/
theorem crooks_identity {Γ : Type*} [Fintype Γ] (r : Γ ≃ Γ) (W : Γ → ℝ) (pF pR : Γ → ℝ)
    (beta dF w : ℝ) (hW : ∀ g, W (r g) = -W g)
    (hmicro : ∀ g, pF g = Real.exp (beta * (W g - dF)) * pR (r g)) :
    workDist pF W w = Real.exp (beta * (w - dF)) * workDist pR W (-w) := by
  classical
  unfold workDist
  rw [Finset.mul_sum]
  have hrev : ∑ g ∈ univ.filter (fun g => W g = -w), Real.exp (beta * (w - dF)) * pR g
      = ∑ g ∈ univ.filter (fun g => W g = w), Real.exp (beta * (w - dF)) * pR (r g) := by
    refine (Finset.sum_equiv r ?_ ?_).symm
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hW i]
      constructor
      · intro h; rw [h]
      · intro h; linarith
    · intro i _; rfl
  rw [hrev]
  refine Finset.sum_congr rfl ?_
  intro g hg
  have hgw : W g = w := by simpa using (Finset.mem_filter.mp hg).2
  rw [hmicro g, hgw]

/-- **Crooks fluctuation theorem.**  For a finite space of microscopic paths `Γ`
equipped with a time-reversal involution `r`, a work function `W` that is odd
under time reversal, and forward/reverse path weights `pF`, `pR` satisfying
microscopic reversibility `pF γ = e^{β(W γ - ΔF)} pR (r γ)`, the forward and
reverse work distributions satisfy
`P_F(W) / P_R(-W) = e^{β(W - ΔF)}`. -/
theorem crooks_theorem {Γ : Type*} [Fintype Γ] (r : Γ ≃ Γ) (W : Γ → ℝ) (pF pR : Γ → ℝ)
    (beta dF w : ℝ) (hW : ∀ g, W (r g) = -W g)
    (hmicro : ∀ g, pF g = Real.exp (beta * (W g - dF)) * pR (r g))
    (hne : workDist pR W (-w) ≠ 0) :
    workDist pF W w / workDist pR W (-w) = Real.exp (beta * (w - dF)) := by
  rw [crooks_identity r W pF pR beta dF w hW hmicro]
  field_simp

end Phys

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

