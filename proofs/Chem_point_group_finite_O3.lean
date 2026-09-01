/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix

/-- `O3` is the orthogonal group of `ℝ³`, realized as the group of `3 × 3` real orthogonal
matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- **Key intermediate lemma.** A linear map of `ℝ³` (given by a matrix) is determined by its
values on a spanning set of vectors. Chemically: a symmetry operation of a molecule is completely
determined by what it does to the (finitely many) nuclei, provided these span space. -/
theorem matrix_eq_of_eq_on_spanning_set
    {A B : Matrix (Fin 3) (Fin 3) ℝ} {S : Set (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ S = ⊤)
    (h : ∀ v ∈ S, A *ᵥ v = B *ᵥ v) : A = B := by
  have hlin : A.mulVecLin = B.mulVecLin := LinearMap.ext_on hspan h
  exact Matrix.toLin'.injective hlin

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

A molecule is modelled by a finite set `S` of nuclear positions in `ℝ³` which is not contained in
any plane through the origin (i.e. `S` spans `ℝ³`); this non-degeneracy is exactly what excludes
the infinite point groups `C∞v`, `D∞h` of linear molecules.  Its point group is any subgroup `G`
of the orthogonal group `O(3)` all of whose elements permute the nuclei, i.e. map `S` into itself.
The conclusion is that `G` is finite.

The proof uses `matrix_eq_of_eq_on_spanning_set`: restricting a symmetry operation to `S` gives an
injection of `G` into the (finite) set of self-maps of `S`. -/
theorem point_group_finite_O3
    (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤)
    (G : Subgroup O3)
    (hG : ∀ A ∈ G, ∀ v ∈ S, ((A : O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v ∈ S) :
    Finite G := by
  -- restriction of a group element to a self-map of the nuclear set
  set F : G → (S → S) := fun A v =>
    ⟨((A : O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (v : Fin 3 → ℝ), hG _ A.2 _ v.2⟩ with hF
  have hinj : Function.Injective F := by
    intro A B hAB
    have h : ∀ v ∈ (S : Set (Fin 3 → ℝ)),
        ((A : O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v
          = ((B : O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v := by
      intro v hv
      have := congrArg Subtype.val (congrFun hAB ⟨v, hv⟩)
      simpa [hF] using this
    have hmat := matrix_eq_of_eq_on_spanning_set hspan h
    exact Subtype.ext (Subtype.ext hmat)
  exact Finite.of_injective F hinj

end Chem

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

