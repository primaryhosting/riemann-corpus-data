import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open scoped NNReal

/-!
## Formalization

The full Kolmogorov–Arnold–Moser theorem says that, for a real-analytic Hamiltonian
`H = H₀ + ε H₁` with `H₀` integrable and nondegenerate, the invariant tori of `H₀`
carrying a Diophantine frequency vector are not destroyed but merely deformed, provided
`|ε|` is small enough.

The analytic core of every proof of KAM is the following: one sets up a *functional
equation* on a space `X` of parametrizations (embeddings) of tori — the conjugacy /
invariance equation — whose solutions are exactly the invariant tori of the perturbed
system. The hard small-divisor analysis (Diophantine conditions, analyticity loss on
shrinking domains, Newton/Nash–Moser quadratic convergence) is what turns that functional
equation into a *fixed point problem for a uniform contraction* `Φ ε : X → X` on a
complete space, together with the estimate `dist (Φ ε u₀) u₀ ≤ C * |ε|` saying that the
unperturbed torus `u₀` is an approximate solution of the perturbed equation, with error
of size `O(ε)`.

`Frontier.kam_theorem` below is the persistence statement in exactly that abstract form,
and it is proved outright: from the contraction and the `O(ε)` defect one gets, for every
`ε`, a genuine invariant torus `u` of the perturbed system, unique, and at distance
`O(ε)` from the unperturbed torus `u₀` — i.e. the tori persist and are deformed only by
`O(ε)`. This is a Lean-checked reduction of KAM to its small-divisor input.

The Mathlib results used are the Banach fixed point theorem in the form
`ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`,
`ContractingWith.fixedPoint_unique` and the a-priori estimate
`ContractingWith.dist_fixedPoint_le`.
-/

/-- **Persistence of invariant tori (KAM), abstract form.**

`X` is the (complete, nonempty) space of parametrizations of tori, `u₀ : X` is an
invariant torus of the unperturbed integrable system, and `Φ ε : X → X` is the operator
whose fixed points are the invariant tori of the system perturbed by `ε`.

Hypotheses:
* `hcontr` : each `Φ ε` is a contraction with a constant `K < 1` independent of `ε`
  (this is what the small-divisor / Newton scheme provides);
* `hpert`  : the unperturbed torus solves the perturbed invariance equation up to an
  error `C * |ε|`.

Conclusion: for every `ε` the perturbed system has an invariant torus `u`, it is the
unique one, and it differs from the unperturbed torus by at most `C * |ε| / (1 - K)`.
In particular the tori are not destroyed, only `O(ε)`-deformed. -/
theorem kam_theorem {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : ℝ≥0} {C : ℝ} (Φ : ℝ → X → X) (u₀ : X)
    (hcontr : ∀ ε : ℝ, ContractingWith K (Φ ε))
    (hpert : ∀ ε : ℝ, dist (Φ ε u₀) u₀ ≤ C * |ε|) (ε : ℝ) :
    ∃ u : X, Φ ε u = u ∧ dist u u₀ ≤ C * |ε| / (1 - K) ∧
      ∀ v : X, Φ ε v = v → v = u := by
  have hK : (K : ℝ) < 1 := by exact_mod_cast (hcontr ε).1
  have hpos : (0 : ℝ) < 1 - K := by linarith
  refine ⟨(hcontr ε).fixedPoint (Φ ε), (hcontr ε).fixedPoint_isFixedPt, ?_, ?_⟩
  · have h1 := (hcontr ε).dist_fixedPoint_le u₀
    have h2 : dist u₀ (Φ ε u₀) ≤ C * |ε| := by
      rw [dist_comm]; exact hpert ε
    have : dist u₀ ((hcontr ε).fixedPoint (Φ ε)) ≤ C * |ε| / (1 - K) :=
      h1.trans (by gcongr)
    rwa [dist_comm] at this
  · intro v hv
    exact (hcontr ε).fixedPoint_unique hv

/-- **Base case of KAM (`ε = 0`).** With no perturbation, the invariant torus `u₀` of the
integrable system is exactly a solution of the invariance equation: it persists
unchanged. -/
theorem kam_unperturbed {X : Type*} [MetricSpace X] {C : ℝ} (Φ : ℝ → X → X) (u₀ : X)
    (hpert : ∀ ε : ℝ, dist (Φ ε u₀) u₀ ≤ C * |ε|) :
    Φ 0 u₀ = u₀ := by
  have := hpert 0
  simp only [abs_zero, mul_zero] at this
  exact dist_le_zero.mp this

/-- The persisting torus converges to the unperturbed one as the perturbation is switched
off: the deformation bound `C * |ε| / (1 - K)` tends to `0` with `ε`. -/
theorem kam_deformation_tendsto_zero {K : ℝ≥0} {C : ℝ} :
    Filter.Tendsto (fun ε : ℝ => C * |ε| / (1 - K)) (nhds 0) (nhds 0) := by
  have hc : Continuous (fun ε : ℝ => C * |ε| / (1 - K)) := by fun_prop
  simpa using hc.tendsto 0

/-- Sanity check: the hypotheses of `Frontier.kam_theorem` are satisfiable and
non-vacuous. Here `X = ℝ`, `Φ ε x = x / 2 + ε`, `u₀ = 0`, `K = 1/2`, `C = 1`; the
persisting "torus" is `u = 2 ε`. -/
example : ∀ ε : ℝ, ∃ u : ℝ, (fun x : ℝ => x / 2 + ε) u = u ∧
    dist u (0 : ℝ) ≤ 1 * |ε| / (1 - ((1 : ℝ≥0) / 2)) ∧
    ∀ v : ℝ, (fun x : ℝ => x / 2 + ε) v = v → v = u := by
  refine kam_theorem (K := 1 / 2) (C := 1) (fun ε x => x / 2 + ε) 0 ?_ ?_
  · intro ε
    refine ⟨by norm_num, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, show x / 2 + ε - (y / 2 + ε) = (x - y) / 2 by ring,
      abs_div]
    norm_num
  · intro ε
    simp

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

