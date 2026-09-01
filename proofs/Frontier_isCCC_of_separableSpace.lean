/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/
def IsCCC (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ A : Set (Set X), (∀ s ∈ A, IsOpen s) → (∀ s ∈ A, s.Nonempty) →
    A.PairwiseDisjoint id → A.Countable

/-- A **Suslin line**: a linearly ordered set, equipped with its order topology, which is
densely ordered without endpoints, satisfies the countable chain condition, but is *not*
separable (it has no countable dense subset).

This is the object whose existence Suslin's problem asks about: `ℝ` is characterised (up to
order isomorphism) as the unique complete densely ordered separable linear order without
endpoints, and Suslin asked whether "separable" can be weakened to "ccc". -/
structure IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] : Prop where
  /-- the topology is the order topology -/
  orderTopology : OrderTopology X
  /-- the order is dense -/
  denselyOrdered : DenselyOrdered X
  /-- there is no least element -/
  noMin : NoMinOrder X
  /-- there is no greatest element -/
  noMax : NoMaxOrder X
  /-- the countable chain condition holds -/
  ccc : IsCCC X
  /-- there is no countable dense subset -/
  not_separable : ¬ SeparableSpace X

/-- The statement "a Suslin line exists". -/
def SuslinLineExists : Prop :=
  ∃ (X : Type) (i : LinearOrder X) (τ : TopologicalSpace X), @IsSuslinLine X i τ

/-- **Suslin's Hypothesis** (SH): there is no Suslin line.  Equivalently, every ccc densely
ordered linear order without endpoints (with its order topology) is separable.

SH is independent of ZFC: Jensen's diamond principle `◊` (which holds in Gödel's constructible
universe `L`) implies the existence of a Suslin line, hence `¬ SH`, while Martin's Axiom
together with `¬ CH` implies SH. -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type) (i : LinearOrder X) (τ : TopologicalSpace X), ¬ @IsSuslinLine X i τ

/-- Every separable space satisfies the countable chain condition.  This is the reason a Suslin
line is a genuine weakening of the classical characterisation of `ℝ`: it is the Mathlib lemma
`Set.PairwiseDisjoint.countable_of_isOpen`. -/
theorem isCCC_of_separableSpace (X : Type u) [TopologicalSpace X] [SeparableSpace X] :
    IsCCC X := fun _A hopen hne hdisj => hdisj.countable_of_isOpen hopen hne

/-- A separable linearly ordered space is not a Suslin line. -/
theorem not_isSuslinLine_of_separableSpace (X : Type u) [LinearOrder X] [TopologicalSpace X]
    [SeparableSpace X] : ¬ IsSuslinLine X := fun h => h.not_separable ‹SeparableSpace X›

/-- A Suslin line is uncountable. -/
theorem not_countable_of_isSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : ¬ Countable X := fun _ => h.not_separable inferInstance

/-- A Suslin line is not second countable. -/
theorem not_secondCountable_of_isSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : ¬ SecondCountableTopology X := fun _ => h.not_separable inferInstance

/-- A linear order with a countable *order-dense* subset (one meeting every nonempty open
interval) is separable in the order topology. -/
theorem separableSpace_of_countable_orderDense (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [Nontrivial X] {D : Set X} (hD : D.Countable)
    (h : ∀ a b : X, a < b → ∃ c ∈ D, a < c ∧ c < b) : SeparableSpace X :=
  ⟨⟨D, hD, dense_of_exists_between fun _ _ hab => h _ _ hab⟩⟩

/-- A Suslin line has no countable order-dense subset: there is no countable `D` meeting every
nonempty open interval. -/
theorem no_countable_orderDense_of_isSuslinLine (X : Type u) [LinearOrder X]
    [TopologicalSpace X] (hX : IsSuslinLine X) :
    ¬ ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → ∃ c ∈ D, a < c ∧ c < b := by
  rintro ⟨D, hD, hdense⟩
  haveI := hX.orderTopology
  haveI : Nontrivial X := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact not_countable_of_isSuslinLine X hX inferInstance
  exact hX.not_separable (separableSpace_of_countable_orderDense X hD hdense)

/-- The real line is not a Suslin line: it is separable (`ℚ` is dense in it). -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ :=
  not_isSuslinLine_of_separableSpace ℝ

/-- The rational line is not a Suslin line. -/
theorem not_isSuslinLine_rat : ¬ IsSuslinLine ℚ :=
  not_isSuslinLine_of_separableSpace ℚ

/-- **Suslin's problem, precisely stated, together with the elementary reductions.**

1. A Suslin line exists if and only if Suslin's Hypothesis fails (this fixes the precise meaning
   of the problem; the two sides are the two horns of the ZFC-independent dichotomy, `◊` giving
   a Suslin line and `MA + ¬CH` giving SH).
2. Every separable space is ccc, so the ccc requirement in the definition of a Suslin line is a
   genuine weakening of separability (Mathlib: `Set.PairwiseDisjoint.countable_of_isOpen`).
3. No separable linear order is a Suslin line; in particular a Suslin line must be uncountable,
   fail to be second countable, and have no countable order-dense subset.
4. Base cases: neither `ℝ` nor `ℚ` is a Suslin line. -/
theorem Suslin_line :
    (SuslinLineExists ↔ ¬ SuslinHypothesis) ∧
    (∀ (X : Type u) (_ : TopologicalSpace X), SeparableSpace X → IsCCC X) ∧
    (∀ (X : Type u) (i : LinearOrder X) (τ : TopologicalSpace X),
        SeparableSpace X → ¬ @IsSuslinLine X i τ) ∧
    (∀ (X : Type u) (i : LinearOrder X) (τ : TopologicalSpace X), @IsSuslinLine X i τ →
        IsCCC X ∧ ¬ SeparableSpace X ∧ ¬ Countable X ∧ ¬ @SecondCountableTopology X τ ∧
        ¬ ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → ∃ c ∈ D, a < c ∧ c < b) ∧
    (¬ IsSuslinLine ℝ ∧ ¬ IsSuslinLine ℚ) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, not_isSuslinLine_real, not_isSuslinLine_rat⟩
  · rintro ⟨X, i, τ, hX⟩ hSH
    exact hSH X i τ hX
  · intro hSH
    by_contra hne
    exact hSH fun X i τ hX => hne ⟨X, i, τ, hX⟩
  · intro X τ hsep
    exact @isCCC_of_separableSpace X τ hsep
  · intro X i τ hsep
    exact @not_isSuslinLine_of_separableSpace X i τ hsep
  · intro X i τ hX
    exact ⟨hX.ccc, hX.not_separable, not_countable_of_isSuslinLine X hX,
      not_secondCountable_of_isSuslinLine X hX, no_countable_orderDense_of_isSuslinLine X hX⟩

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

