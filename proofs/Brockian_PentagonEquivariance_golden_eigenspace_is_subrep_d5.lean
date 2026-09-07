/-
  Brockian/PentagonEquivariance.lean

  **The golden spectrum is representation-theoretically forced.**

  `Brockian.PentagonIsotypic` / `Brockian.PentagonMultiplicities` diagonalized the
  C₅ adjacency operator `A = ρ + ρ⁻¹` on `VertexSpace = Fin 5 → ℂ`, produced the
  Fourier eigenmodes, identified the golden eigenvalue `φ − 1`, and computed the
  geometric multiplicity `finrank (eigenspace adjL (φ−1)) = 2`.  What was NOT made
  explicit there is *why* that 2-dimensional eigenspace is not an accident: it is
  the χ_golden **isotypic block** — a subrepresentation of the pentagon's full
  symmetry group `D₅` acting on `VertexSpace`.

  This file supplies that mechanism.  The adjacency operator `A = ρ + ρ⁻¹` is the
  sum over the two nearest-neighbour rotations; because the `D₅` pullback action
  `d5Pull` is a group action and `ρ = d5Pull (r 1)`, every symmetry `g ∈ D₅`
  *commutes* with `A` (rotations commute because `C₅` is abelian; a reflection
  `s` conjugates `{ρ, ρ⁻¹}` to `{ρ⁻¹, ρ}`, so it fixes their sum).  An operator
  that commutes with the whole group carries every eigenspace to itself, so the
  golden eigenspace is `D₅`-invariant: **a subrepresentation on which `A` acts as
  the scalar `φ − 1` (Schur).**  The golden value is thus forced by symmetry, not
  chosen.

  ## What is proved
    * `d5Pull_sr_apply`               — reflection pullback `(sr b)·f (x) = f(−b−x)`.
    * `adjacency_comm_rot`            — `A` commutes with every rotation `d5Pull (r a)`.
    * `adjacency_comm_d5`             — `A` commutes with EVERY `g ∈ D₅` (rotations
                                        AND reflections): full `D₅`-equivariance.
    * `golden_eigenspace_invariant_rot` / `_d5`
                                      — the golden eigenspace is carried into itself
                                        by every rotation / every `D₅` element.
    * `golden_eigenspace_is_subrep`  — the capstone: the golden eigenspace is a
                                        `D₅`-invariant subspace of dimension `2`.

  No new axioms; no `sorry`/`admit`/`native_decide`.  Verified on AXLE at
  `lean-4.32.0`; `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.PentagonIsotypic
import Brockian.PentagonMultiplicities

open BigOperators
open DihedralGroup
open Module
open Brockian.Automorphism
open Brockian.D5Representation
open Brockian.D5Isotypic
open Brockian.PentagonIsotypic
open Brockian.PentagonMultiplicities

namespace Brockian.PentagonEquivariance

/-! ### Reflection pullback in coordinates

The rotation pullback `d5Pull (r k) f x = f (x − k)` is already available
(`d5Pull_r_apply`).  We add the companion for reflections: `sr b` acts by the
orientation-reversing involution `x ↦ −b − x`. -/

/-- Pullback by the reflection `sr b`: `(sr b · f)(x) = f(−b − x)`. -/
theorem d5Pull_sr_apply (b : Fin 5) (f : VertexSpace) (x : Fin 5) :
    d5Pull (sr b) f x = f (-b - x) := by
  simp [d5Pull_apply, dihedralHom_sr, reflIso, reflEquiv]

/-! ### Adjacency commutes with the symmetry action -/

/-- **Adjacency commutes with every rotation.**  `A ∘ ρ^a = ρ^a ∘ A`.  Since
`A = ρ + ρ⁻¹` and rotations of `C₅` commute (the cyclic group is abelian), the
adjacency operator is `C₅`-equivariant. -/
theorem adjacency_comm_rot (a : Fin 5) (f : VertexSpace) :
    adjacency (d5Pull (r a) f) = d5Pull (r a) (adjacency f) := by
  unfold adjacency
  rw [map_add, d5Pull_r_mul, d5Pull_r_mul, d5Pull_r_mul, d5Pull_r_mul,
    add_comm (1 : Fin 5) a, add_comm (-1 : Fin 5) a]

/-- **Full `D₅`-equivariance of the adjacency operator.**  `A` commutes with every
symmetry `g ∈ D₅` — rotations (abelianness of `C₅`) and reflections alike.  A
reflection `s` satisfies `s ρ s⁻¹ = ρ⁻¹`, so it swaps the two summands of
`A = ρ + ρ⁻¹` and leaves the sum invariant. -/
theorem adjacency_comm_d5 (g : DihedralGroup 5) (f : VertexSpace) :
    adjacency (d5Pull g f) = d5Pull g (adjacency f) := by
  obtain (a | b) := g
  · exact adjacency_comm_rot a f
  · funext x
    simp only [adjacency_apply, d5Pull_sr_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> abel

/-! ### The golden eigenspace is a subrepresentation -/

/-- **The golden eigenspace is invariant under every rotation.**  Applying any
rotation `ρ^a` to a golden eigenvector yields a golden eigenvector: the golden
spectrum is representation-theoretically forced by the `C₅` symmetry. -/
theorem golden_eigenspace_invariant_rot (a : Fin 5) (v : VertexSpace)
    (hv : v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) :
    d5Pull (r a) v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [adjL_apply, adjacency_comm_rot, ← adjL_apply, hv, map_smul]

/-- **The golden eigenspace is invariant under the full `D₅` action.**  Every
symmetry `g ∈ D₅` (rotation or reflection) carries a golden eigenvector to a
golden eigenvector: the golden eigenspace is a genuine subrepresentation. -/
theorem golden_eigenspace_invariant_d5 (g : DihedralGroup 5) (v : VertexSpace)
    (hv : v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) :
    d5Pull g v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [adjL_apply, adjacency_comm_d5, ← adjL_apply, hv, map_smul]

/-- **The golden spectrum is representation-theoretically forced.**  The golden
eigenspace of the C₅ adjacency operator is a 2-dimensional `D₅`-invariant subspace
— the χ_golden isotypic block — on which the adjacency acts as the scalar `φ − 1`
(Schur).  Invariance is stated for the rotation subgroup `C₅ ≤ D₅`; the strictly
stronger full-`D₅` invariance is `golden_eigenspace_invariant_d5`. -/
theorem golden_eigenspace_is_subrep :
    (∀ a : Fin 5, ∀ v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ),
        d5Pull (r a) v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) ∧
    finrank ℂ (Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) = 2 :=
  ⟨golden_eigenspace_invariant_rot, finrank_eigenspace_golden⟩

/-- **Full-`D₅` capstone.**  The golden eigenspace is a 2-dimensional subspace
invariant under the entire pentagon symmetry group `D₅` — a bona fide
subrepresentation, the χ_golden isotypic block. -/
theorem golden_eigenspace_is_subrep_d5 :
    (∀ g : DihedralGroup 5, ∀ v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ),
        d5Pull g v ∈ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) ∧
    finrank ℂ (Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) = 2 :=
  ⟨golden_eigenspace_invariant_d5, finrank_eigenspace_golden⟩

end Brockian.PentagonEquivariance
