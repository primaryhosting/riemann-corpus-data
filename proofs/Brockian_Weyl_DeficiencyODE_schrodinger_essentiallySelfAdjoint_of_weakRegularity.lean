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

import Mathlib

/-!
# Essential self-adjointness of symmetric unbounded operators

This file develops the basic von Neumann criterion for essential self-adjointness of a
densely defined symmetric operator on a complex Hilbert space, phrased for `LinearPMap`s.
-/

open scoped ComplexConjugate InnerProductSpace
open LinearPMap

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An unbounded operator is *essentially self-adjoint* if its closure is self-adjoint. -/
def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint T.closure

section Closure

variable (T : H →ₗ.[ℂ] H)

omit [CompleteSpace H] in
theorem dense_closure_domain (hT : Dense (T.domain : Set H)) :
    Dense (T.closure.domain : Set H) :=
  hT.mono (fun _ hx => T.le_closure.1 hx)

/-- If `⟪w, x⟫ = ⟪y, T x⟫` on the domain of `T`, the same holds on the domain of the closure. -/
theorem inner_eq_of_closure {w y : H} (hclosable : T.IsClosable)
    (h : ∀ x : T.domain, (inner ℂ w (x : H)) = inner ℂ y (T x)) (x : T.closure.domain) :
    (inner ℂ w (x : H)) = inner ℂ y (T.closure x) := by
  have hmem : ((x : H), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hclosable.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hclosed : IsClosed {p : H × H | (inner ℂ w p.1 : ℂ) = inner ℂ y p.2} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hsub : (T.graph : Set (H × H)) ⊆ {p : H × H | (inner ℂ w p.1 : ℂ) = inner ℂ y p.2} := by
    rintro ⟨a, b⟩ hab
    obtain ⟨z, hz1, hz2⟩ := (T.mem_graph_iff).1 hab
    simp only [Set.mem_setOf_eq] at hz1 hz2 ⊢
    rw [← hz1, ← hz2]
    exact h z
  have hsub' : (T.graph.topologicalClosure : Set (H × H)) ⊆
      {p : H × H | (inner ℂ w p.1 : ℂ) = inner ℂ y p.2} := by
    simpa [Submodule.topologicalClosure_coe] using closure_minimal hsub hclosed
  exact hsub' hmem

/-- The adjoint of the closure is the adjoint. -/
theorem adjoint_closure_eq (hT : Dense (T.domain : Set H)) : T.closure† = T† := by
  have hTc : Dense (T.closure.domain : Set H) := dense_closure_domain T hT
  have h1 : T.closure† ≤ T† := by
    refine ⟨fun y hy => ?_, ?_⟩
    · refine mem_adjoint_domain_of_exists _ ⟨T.closure† ⟨y, hy⟩, fun x => ?_⟩
      have hx : (x : H) ∈ T.closure.domain := T.le_closure.1 x.2
      have hval : T.closure ⟨(x : H), hx⟩ = T x := (T.le_closure.2 rfl).symm
      have := (adjoint_isFormalAdjoint hTc) ⟨y, hy⟩ ⟨(x : H), hx⟩
      simpa [hval] using this
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only at hxy
      subst hxy
      refine (adjoint_apply_eq hT ⟨x, hy⟩ (fun v => ?_)).symm
      have hv : (v : H) ∈ T.closure.domain := T.le_closure.1 v.2
      have hval : T.closure ⟨(v : H), hv⟩ = T v := (T.le_closure.2 rfl).symm
      have := (adjoint_isFormalAdjoint hTc) ⟨x, hx⟩ ⟨(v : H), hv⟩
      simpa [hval] using this
  have h2 : T† ≤ T.closure† := by
    by_cases hclosable : T.IsClosable
    · refine ⟨fun y hy => ?_, ?_⟩
      · exact mem_adjoint_domain_of_exists _ ⟨T† ⟨y, hy⟩, fun x =>
          inner_eq_of_closure T hclosable (fun v => (adjoint_isFormalAdjoint hT) ⟨y, hy⟩ v) x⟩
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simp only at hxy
        subst hxy
        exact (adjoint_apply_eq hTc ⟨x, hy⟩ (fun v =>
          inner_eq_of_closure T hclosable
            (fun u => (adjoint_isFormalAdjoint hT) ⟨x, hx⟩ u) v)).symm
    · rw [closure_def' hclosable]
  exact le_antisymm h1 h2

end Closure

end Brockian.Weyl

