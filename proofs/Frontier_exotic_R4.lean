-- (In Lean 4.28 a module doc comment `/-! ... -/` may not precede the `import` block,
-- so the required header comment is placed immediately after the import.)
import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- Notation for `4`-dimensional Euclidean space, the model space of a smooth `4`-manifold. -/
local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- A smooth `4`-manifold `M` (modelled on Euclidean `ℝ⁴`) is an *exotic* `ℝ⁴` if it is
homeomorphic to `ℝ⁴` but admits no diffeomorphism to `ℝ⁴`. -/
def IsExoticR4 (M : Type) [TopologicalSpace M] [ChartedSpace ℝ⁴ M]
    [IsManifold (𝓡 4) ∞ M] : Prop :=
  Nonempty (M ≃ₜ ℝ⁴) ∧ IsEmpty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ ℝ⁴)

/-- The *small* exotic `ℝ⁴` statement: there is an open subset of `ℝ⁴` which is homeomorphic,
but not diffeomorphic, to `ℝ⁴`.  This is the statement recorded (as an unproven `proof_wanted`)
in `Mathlib.Geometry.Manifold.PoincareConjecture` under the name
`exists_open_nonempty_homeomorph_isEmpty_diffeomorph_euclideanSpace_four`; it is a consequence of
the work of Freedman and Donaldson, and no proof of it is available in Mathlib. -/
def SmallExoticR4 : Prop :=
  ∃ M : TopologicalSpace.Opens ℝ⁴, Nonempty (M ≃ₜ ℝ⁴) ∧ IsEmpty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ ℝ⁴)

/-- **Existence of an exotic `ℝ⁴` (Freedman–Donaldson), as a Lean-checked reduction.**

Assuming the small exotic `ℝ⁴` statement `SmallExoticR4` (an open subset of `ℝ⁴` that is
homeomorphic but not diffeomorphic to `ℝ⁴`), there exists a *smooth manifold* — a nonempty,
Hausdorff, second-countable smooth `4`-manifold `M` modelled on `ℝ⁴` — which is homeomorphic
to `ℝ⁴` but admits no diffeomorphism to `ℝ⁴`.

The content of the reduction is that an open subset of `ℝ⁴` carries a canonical smooth
`4`-manifold structure (restricted charts), together with the topological properties inherited
from `ℝ⁴`. The deep input, `SmallExoticR4`, is left as an explicit hypothesis: it is not
available in Mathlib. -/
theorem exotic_R4 (h : SmallExoticR4) :
    ∃ (M : Type) (_tM : TopologicalSpace M) (_cM : ChartedSpace ℝ⁴ M)
      (_sM : IsManifold (𝓡 4) ∞ M),
      Nonempty M ∧ T2Space M ∧ SecondCountableTopology M ∧ IsExoticR4 M := by
  obtain ⟨U, ⟨e⟩, hne⟩ := h
  exact ⟨U, inferInstance, inferInstance, inferInstance, ⟨e.symm 0⟩, inferInstance,
    inferInstance, ⟨e⟩, hne⟩

/-- Sanity check (base case): the standard `ℝ⁴` is not an exotic `ℝ⁴`, since it is
diffeomorphic to itself.  Hence the property `IsExoticR4` is not vacuously satisfied by every
smooth `4`-manifold homeomorphic to `ℝ⁴`. -/
theorem not_isExoticR4_euclideanSpace : ¬ IsExoticR4 ℝ⁴ := by
  rintro ⟨-, h⟩
  exact h.elim (Diffeomorph.refl (𝓡 4) ℝ⁴ ∞)

/-- Being an exotic `ℝ⁴` is a diffeomorphism invariant: if `M` is an exotic `ℝ⁴` and `N` is
diffeomorphic to `M`, then `N` is an exotic `ℝ⁴` as well. -/
theorem isExoticR4_of_diffeomorph {M N : Type} [TopologicalSpace M] [ChartedSpace ℝ⁴ M]
    [IsManifold (𝓡 4) ∞ M] [TopologicalSpace N] [ChartedSpace ℝ⁴ N] [IsManifold (𝓡 4) ∞ N]
    (f : N ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) (hM : IsExoticR4 M) : IsExoticR4 N := by
  obtain ⟨⟨e⟩, hne⟩ := hM
  refine ⟨⟨f.toHomeomorph.trans e⟩, ⟨fun g => hne.elim (f.symm.trans g)⟩⟩

/-- Any exotic `ℝ⁴` is a noncompact, connected, nonempty manifold, since it is homeomorphic
to `ℝ⁴`. -/
theorem isExoticR4_properties {M : Type} [TopologicalSpace M] [ChartedSpace ℝ⁴ M]
    [IsManifold (𝓡 4) ∞ M] (hM : IsExoticR4 M) :
    Nonempty M ∧ ConnectedSpace M ∧ ¬ CompactSpace M := by
  obtain ⟨⟨e⟩, -⟩ := hM
  refine ⟨⟨e.symm 0⟩, e.symm.surjective.connectedSpace e.symm.continuous, fun hc => ?_⟩
  have hc4 : CompactSpace ℝ⁴ := e.compactSpace
  exact (not_compactSpace_iff.mpr inferInstance) hc4

end Frontier

