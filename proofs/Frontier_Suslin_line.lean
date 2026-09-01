import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
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

namespace Frontier

universe u

/-- **The countable chain condition (ccc).**  A topological space satisfies the ccc if every
family of pairwise disjoint nonempty open sets is countable. -/
def IsCCC (α : Type u) [TopologicalSpace α] : Prop :=
  ∀ 𝒰 : Set (Set α), (∀ U ∈ 𝒰, IsOpen U) → (∀ U ∈ 𝒰, U.Nonempty) →
    𝒰.PairwiseDisjoint id → 𝒰.Countable

/-- **A Suslin line.**  A linearly ordered set, equipped with its order topology, which is
densely ordered, has no endpoints, has at least two points, satisfies the countable chain
condition, but is *not* separable (i.e. has no countable dense subset).

This is exactly the object whose existence Suslin's problem asks about: the classical
characterisation of `ℝ` (Cantor) says that a densely ordered, endpointless, *separable*,
order-complete linear order is order-isomorphic to `ℝ`; Suslin asked whether "separable" may be
weakened to "ccc".  A Suslin line is a counterexample. -/
def IsSuslinLine (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α] : Prop :=
  DenselyOrdered α ∧ NoMinOrder α ∧ NoMaxOrder α ∧ Nontrivial α ∧ IsCCC α ∧
    ¬ TopologicalSpace.SeparableSpace α

/-- **Suslin's Hypothesis (SH):** there is no Suslin line.  (This statement is independent of
ZFC: Jensen's diamond principle `◊` implies its failure, while `MA + ¬CH` implies it.) -/
def SuslinHypothesis : Prop :=
  ∀ (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α], ¬ IsSuslinLine α

/-- Every separable space satisfies the countable chain condition:  a pairwise disjoint family
of nonempty open sets injects into any countable dense subset. -/
theorem isCCC_of_separableSpace (α : Type u) [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] : IsCCC α := by
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense α
  intro 𝒰 hopen hne hdisj
  have hs' : Countable ↥s := hs.to_subtype
  have key : ∀ U : ↥𝒰, ∃ x : ↥s, (x : α) ∈ (U : Set α) := by
    intro U
    obtain ⟨x, hxU, hxs⟩ := hdense.inter_open_nonempty _ (hopen U U.2) (hne U U.2)
    exact ⟨⟨x, hxs⟩, hxU⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro U V h
    by_contra hUV
    have hd : Disjoint (id (U : Set α)) (id (V : Set α)) :=
      hdisj U.2 V.2 (fun e => hUV (Subtype.ext e))
    exact Set.disjoint_left.mp hd (hf U) (by rw [h]; exact hf V)
  exact Set.countable_coe_iff.mp (Function.Injective.countable hinj)

/-- A countable space is separable, hence a Suslin line must be uncountable. -/
theorem not_countable_of_isSuslinLine (α : Type u) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : ¬ Countable α := by
  intro hc
  exact h.2.2.2.2.2 ⟨⟨Set.univ, Set.countable_univ, dense_univ⟩⟩

/-- The real line is not a Suslin line: it is separable. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := fun h => h.2.2.2.2.2 inferInstance

/-- **Suslin's problem, formalised.**

1. *(Separability implies ccc.)*  Every separable space satisfies the countable chain condition;
   thus the ccc is a genuine weakening of separability, and this is the weakening appearing in
   Suslin's problem.
2. *(Base case: the real line.)*  `ℝ` — with its order topology — is ccc and separable, hence is
   not a Suslin line.
3. *(Any Suslin line is uncountable.)*
4. *(Precise reduction.)*  Suslin's Hypothesis holds if and only if every densely ordered
   linear order without endpoints and with at least two points which satisfies the countable
   chain condition (in its order topology) is separable. -/
theorem Suslin_line :
    (∀ (α : Type u) [TopologicalSpace α] [TopologicalSpace.SeparableSpace α], IsCCC α) ∧
    (IsCCC ℝ ∧ TopologicalSpace.SeparableSpace ℝ ∧ ¬ IsSuslinLine ℝ) ∧
    (∀ (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
      IsSuslinLine α → ¬ Countable α) ∧
    (SuslinHypothesis.{u} ↔
      ∀ (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
        DenselyOrdered α → NoMinOrder α → NoMaxOrder α → Nontrivial α → IsCCC α →
          TopologicalSpace.SeparableSpace α) := by
  refine ⟨fun α _ _ => isCCC_of_separableSpace α,
    ⟨isCCC_of_separableSpace ℝ, inferInstance, not_isSuslinLine_real⟩,
    fun α _ _ _ h => not_countable_of_isSuslinLine α h, ?_⟩
  constructor
  · intro hSH α _ _ _ hd hmin hmax hnt hccc
    by_contra hsep
    exact hSH α ⟨hd, hmin, hmax, hnt, hccc, hsep⟩
  · rintro h α _ _ _ ⟨hd, hmin, hmax, hnt, hccc, hsep⟩
    exact hsep (h α hd hmin hmax hnt hccc)

end Frontier

