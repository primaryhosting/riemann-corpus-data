/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

/-- **Aggregation lemma (sure-thing principle).**

If the common-knowledge event `C` is partitioned into the information cells of an agent
(the cells are the fibres of `f` inside `C`, indexed by `I`), and on every cell the
conditional probability of `E` equals `q`, then the conditional probability of `E`
on all of `C` is again `q`.

Here `μ : Ω → ℝ` is the (common) prior weight function, the numerator
`∑ x ∈ S, if x ∈ E then μ x else 0` is the mass of `E ∩ S`, and the denominator
`∑ x ∈ S, μ x` is the mass of `S`; a statement `num = q * den` is the (denominator-free)
form of "the posterior of `E` given `S` is `q`". -/
theorem posterior_constant_on_cells
    {Ω ι : Type*} [DecidableEq ι]
    (μ : Ω → ℝ) (E C : Finset Ω) [DecidablePred (· ∈ E)]
    (f : Ω → ι) (I : Finset ι) (hf : ∀ x ∈ C, f x ∈ I) (q : ℝ)
    (h : ∀ i ∈ I, (∑ x ∈ C with f x = i, if x ∈ E then μ x else 0)
          = q * ∑ x ∈ C with f x = i, μ x) :
    (∑ x ∈ C, if x ∈ E then μ x else 0) = q * ∑ x ∈ C, μ x := by
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun x => if x ∈ E then μ x else 0),
      ← Finset.sum_fiberwise_of_maps_to hf μ, Finset.mul_sum]
  exact Finset.sum_congr rfl h

/-- **Aumann's agreement theorem (base case).**

Two agents share a common prior `μ` on a finite state space and consider an event `E`.
Let `C` be a common-knowledge event at the actual state: `C` is a union of cells of agent
1's information partition (the fibres of `f`, indexed by `I`) and also a union of cells of
agent 2's information partition (the fibres of `g`, indexed by `K`) — i.e. `C` is a member
of the meet of the two partitions.

Assume it is common knowledge that agent 1's posterior of `E` is `q₁` and agent 2's is `q₂`;
formally, on every cell of agent 1 inside `C` the posterior of `E` equals `q₁` (hypothesis
`h₁`, written in the denominator-free form `mass (E ∩ cell) = q₁ * mass cell`), and likewise
for agent 2 with `q₂`.

Then, provided `C` has positive prior mass, `q₁ = q₂`: the agents cannot agree to disagree. -/
theorem aumann_agreement
    {Ω ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (μ : Ω → ℝ) (E C : Finset Ω) [DecidablePred (· ∈ E)]
    (f : Ω → ι) (g : Ω → κ) (I : Finset ι) (K : Finset κ)
    (hf : ∀ x ∈ C, f x ∈ I) (hg : ∀ x ∈ C, g x ∈ K)
    (q₁ q₂ : ℝ)
    (h₁ : ∀ i ∈ I, (∑ x ∈ C with f x = i, if x ∈ E then μ x else 0)
          = q₁ * ∑ x ∈ C with f x = i, μ x)
    (h₂ : ∀ j ∈ K, (∑ x ∈ C with g x = j, if x ∈ E then μ x else 0)
          = q₂ * ∑ x ∈ C with g x = j, μ x)
    (hC : 0 < ∑ x ∈ C, μ x) :
    q₁ = q₂ := by
  have e₁ := posterior_constant_on_cells μ E C f I hf q₁ h₁
  have e₂ := posterior_constant_on_cells μ E C g K hg q₂ h₂
  have : q₁ * (∑ x ∈ C, μ x) = q₂ * ∑ x ∈ C, μ x := by rw [← e₁, ← e₂]
  exact mul_right_cancel₀ (ne_of_gt hC) this

/-- Sanity check (non-vacuity): the hypotheses of `aumann_agreement` are simultaneously
satisfiable with two *genuinely different* information partitions.

Four equally likely states `0,1,2,3`; the event is `E = {0,3}`. Agent 1 observes `x / 2`
(cells `{0,1}`, `{2,3}`), agent 2 observes `x % 2` (cells `{0,2}`, `{1,3}`). Every cell of
every agent contains exactly one state of `E`, so both posteriors are `1/2`, and the theorem
returns that common value. -/
example : (1 / 2 : ℝ) = 1 / 2 :=
  aumann_agreement (Ω := Fin 4) (fun _ => 1) {0, 3} univ
    (fun x => x.val / 2) (fun x => x.val % 2) {0, 1} {0, 1}
    (by intro x _; fin_cases x <;> decide) (by intro x _; fin_cases x <;> decide)
    (1 / 2) (1 / 2)
    (by
      intro i hi
      fin_cases hi <;>
        · rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
          norm_num; decide)
    (by
      intro j hj
      fin_cases hj <;>
        · rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
          norm_num; decide)
    (by norm_num)

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

