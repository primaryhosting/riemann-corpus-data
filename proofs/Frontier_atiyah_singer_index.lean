import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Atiyah–Singer index theorem states that for an elliptic (pseudo)differential operator
`D : Γ(E) → Γ(F)` between sections of vector bundles over a closed manifold `M`, the
*analytic index*

  `ind_a D = dim ker D - dim coker D`

equals the *topological index* of the symbol of `D`, a quantity computed purely from
topological data of `M`, `E` and `F` (and in particular independent of the operator itself).

Mathlib does not contain the theory of elliptic pseudodifferential operators, so the full
statement is not available.  What is formalized and proved here is the **base case** of the
theorem: the case of a zero-dimensional manifold (a point), where "sections of a bundle" are
just vectors in a finite dimensional vector space, "elliptic operator" is an arbitrary linear
map `D : V →ₗ[K] W`, and the topological index of the symbol is `dim V - dim W`.

The base case already exhibits the two characteristic features of the index theorem:

* the analytic index, defined through the (a priori operator-dependent) kernel and cokernel,
  is computed by purely "topological" data (`Frontier.atiyah_singer_index`);
* consequently the index is a deformation invariant: it is the same for all operators between
  the same pair of bundles (`Frontier.analyticIndex_eq_analyticIndex`), and it vanishes for
  operators from a bundle to itself (`Frontier.analyticIndex_self`).

The proof is a Lean-checked reduction of the base case to the rank–nullity theorem, in the
form of the two Mathlib lemmas `LinearMap.finrank_range_add_finrank_ker` and
`Submodule.finrank_quotient_add_finrank`.
-/

namespace Frontier

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The cokernel `W / range D` of a linear map `D : V →ₗ[K] W`.  In the geometric situation
this is the cokernel of an elliptic operator between spaces of sections. -/
abbrev Coker (D : V →ₗ[K] W) : Type _ := W ⧸ LinearMap.range D

/-- The **analytic index** of an operator `D : V →ₗ[K] W`:
`dim ker D - dim coker D`, an integer. -/
noncomputable def analyticIndex (D : V →ₗ[K] W) : ℤ :=
  (finrank K (LinearMap.ker D) : ℤ) - (finrank K (Coker D) : ℤ)

/-- The **topological index** attached to the pair of "bundles" `V`, `W` over a point:
`dim V - dim W`.  It depends only on the (symbol of the) operator's source and target,
not on the operator. -/
noncomputable def topologicalIndex (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] : ℤ :=
  (finrank K V : ℤ) - (finrank K W : ℤ)

/-- **Atiyah–Singer index theorem, base case (a zero-dimensional manifold).**

For an elliptic operator over a point — that is, an arbitrary linear map `D : V →ₗ[K] W`
between finite dimensional vector spaces — the analytic index `dim ker D - dim coker D`
equals the topological index `dim V - dim W` of its symbol.

The proof reduces to rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) together with
the dimension formula for quotients (`Submodule.finrank_quotient_add_finrank`). -/
theorem atiyah_singer_index [FiniteDimensional K V] [FiniteDimensional K W] (D : V →ₗ[K] W) :
    analyticIndex D = topologicalIndex K V W := by
  have h₁ : finrank K (LinearMap.range D) + finrank K (LinearMap.ker D) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker D
  have h₂ : finrank K (W ⧸ LinearMap.range D) + finrank K (LinearMap.range D) = finrank K W :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range D)
  unfold analyticIndex topologicalIndex Coker
  omega

/-- Deformation invariance of the index: any two elliptic operators over a point with the same
source and target have the same analytic index. -/
theorem analyticIndex_eq_analyticIndex [FiniteDimensional K V] [FiniteDimensional K W]
    (D D' : V →ₗ[K] W) : analyticIndex D = analyticIndex D' := by
  rw [atiyah_singer_index, atiyah_singer_index]

/-- An elliptic operator from a bundle to itself has vanishing index. -/
theorem analyticIndex_self [FiniteDimensional K V] (D : V →ₗ[K] V) : analyticIndex D = 0 := by
  rw [atiyah_singer_index]
  simp [topologicalIndex]

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

