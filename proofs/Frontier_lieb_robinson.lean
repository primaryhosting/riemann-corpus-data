import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option grind.warning false

namespace Frontier

/-- **Key intermediate lemma (Grönwall estimate).**

If a vector-valued function `G : ℝ → E` is differentiable and its derivative obeys the
linear bound `‖G' t‖ ≤ v * ‖G t‖`, then `‖G t‖` grows at most exponentially:
`‖G t‖ ≤ ‖G 0‖ * exp (v * t)` for `t ≥ 0`.

This is the analytic heart of the Lieb–Robinson bound: the commutator
`G t = [A t, B]` satisfies exactly such a differential inequality, with `v` playing the
role of the Lieb–Robinson velocity. -/
theorem gronwall_norm_le_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) (v : ℝ) (hG : Differentiable ℝ G)
    (hd : ∀ t, ‖deriv G t‖ ≤ v * ‖G t‖) :
    ∀ t, 0 ≤ t → ‖G t‖ ≤ ‖G 0‖ * Real.exp (v * t) := by
  intro t ht
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := G) (f' := deriv G)
    (δ := ‖G 0‖) (K := v) (ε := 0) (a := 0) (b := t)
    (hG.continuous.continuousOn)
    (fun x _ => ((hG x).hasDerivAt).hasDerivWithinAt)
    le_rfl
    (fun x _ => by simpa using hd x)
    t (Set.mem_Icc.2 ⟨ht, le_rfl⟩)
  simpa [gronwallBound_ε0] using key

/-- **Lieb–Robinson bound: an effective light cone for local spin dynamics.**

Let `A : ℝ → E` be the Heisenberg-evolved observable `A t` in a normed algebra of
observables `E`, and let `B : E` be a second observable.  Write
`G t = A t * B - B * A t` for the commutator, which measures how much the evolved `A`
"feels" the region where `B` is supported.

Under the two physical hypotheses

* (dynamics) the commutator is differentiable in time and obeys the Lieb–Robinson
  differential inequality `‖G' t‖ ≤ v * ‖G t‖`, with `v` the Lieb–Robinson velocity;
* (locality at time zero) the observables are almost commuting at `t = 0`, with the
  exponentially small defect `‖G 0‖ ≤ 2 * cA * cB * exp (-d)` coming from the distance
  `d` between the supports of `A` and `B`,

one obtains the light-cone estimate

`‖[A t, B]‖ ≤ 2 * cA * cB * exp (v * t - d)`,

which is exponentially small outside the light cone `v * t < d`. -/
theorem lieb_robinson {E : Type*} [NormedRing E] [NormedSpace ℝ E]
    (A : ℝ → E) (B : E) (v d cA cB : ℝ)
    (hdiff : Differentiable ℝ fun t => A t * B - B * A t)
    (hLR : ∀ t, ‖deriv (fun t => A t * B - B * A t) t‖ ≤ v * ‖A t * B - B * A t‖)
    (hinit : ‖A 0 * B - B * A 0‖ ≤ 2 * cA * cB * Real.exp (-d)) :
    ∀ t, 0 ≤ t → ‖A t * B - B * A t‖ ≤ 2 * cA * cB * Real.exp (v * t - d) := by
  intro t ht
  have hG := gronwall_norm_le_exp (fun t => A t * B - B * A t) v hdiff hLR t ht
  calc ‖A t * B - B * A t‖
      ≤ ‖A 0 * B - B * A 0‖ * Real.exp (v * t) := hG
    _ ≤ (2 * cA * cB * Real.exp (-d)) * Real.exp (v * t) := by
        exact mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le
    _ = 2 * cA * cB * Real.exp (v * t - d) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

end Frontier

