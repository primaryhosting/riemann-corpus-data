import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The work distribution associated to a path measure `p` on a finite set of
microscopic trajectories `Γ`, with work functional `W`: the probability of
observing work value `w` is the total weight of the trajectories realizing it. -/
noncomputable def workDist {Γ : Type*} [Fintype Γ] (W : Γ → ℝ) (p : Γ → ℝ) (w : ℝ) : ℝ :=
  ∑ γ ∈ Finset.univ.filter (fun γ => W γ = w), p γ

/-- **Key intermediate lemma (path-reversal reindexing).**
If `R` is the time-reversal involution on trajectories and it flips the sign of the
work, then summing the reverse-process weights of the reversals of the trajectories
of work `w` computes exactly the reverse work distribution at `-w`. -/
theorem sum_reverse_eq_workDist_neg {Γ : Type*} [Fintype Γ]
    (W : Γ → ℝ) (R : Γ → Γ) (hR : Function.Involutive R)
    (hW : ∀ γ, W (R γ) = -W γ) (pR : Γ → ℝ) (w : ℝ) :
    ∑ γ ∈ Finset.univ.filter (fun γ => W γ = w), pR (R γ) = workDist W pR (-w) := by
  unfold workDist
  refine Finset.sum_nbij' (i := R) (j := R) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [hW, ha]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have := hW a
    rw [ha] at this
    simpa using this
  · intro a _; exact hR a
  · intro a _; exact hR a
  · intro a _; rfl

/-- **Crooks fluctuation theorem.**
Setting: a finite set `Γ` of microscopic trajectories, a time-reversal involution
`R : Γ → Γ` which flips the sign of the work `W`, forward and reverse path weights
`pF`, `pR`, inverse temperature `β` and free-energy difference `ΔF`, related by
microscopic reversibility `pF γ = e^{β (W γ - ΔF)} · pR (R γ)`.

Conclusion: the forward and reverse *work distributions* obey
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`, i.e. `P_F(W) / P_R(-W) = e^{β (W - ΔF)}`
whenever `P_R(-W) ≠ 0`. -/
theorem crooks_theorem {Γ : Type*} [Fintype Γ]
    (W : Γ → ℝ) (R : Γ → Γ) (hR : Function.Involutive R)
    (hW : ∀ γ, W (R γ) = -W γ)
    (pF pR : Γ → ℝ) (β ΔF : ℝ)
    (hmicro : ∀ γ, pF γ = Real.exp (β * (W γ - ΔF)) * pR (R γ))
    (w : ℝ) :
    workDist W pF w = Real.exp (β * (w - ΔF)) * workDist W pR (-w) ∧
      (workDist W pR (-w) ≠ 0 →
        workDist W pF w / workDist W pR (-w) = Real.exp (β * (w - ΔF))) := by
  have key : workDist W pF w = Real.exp (β * (w - ΔF)) * workDist W pR (-w) := by
    have h1 : workDist W pF w
        = ∑ γ ∈ Finset.univ.filter (fun γ => W γ = w),
            Real.exp (β * (w - ΔF)) * pR (R γ) := by
      unfold workDist
      refine Finset.sum_congr rfl ?_
      intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
      rw [hmicro γ, hγ]
    rw [h1, ← Finset.mul_sum, sum_reverse_eq_workDist_neg W R hR hW pR w]
  refine ⟨key, ?_⟩
  intro hne
  rw [key, mul_div_assoc, div_self hne, mul_one]

end Phys

