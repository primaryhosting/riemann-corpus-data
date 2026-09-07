/-
  Brockian/WeylWeightedRellich.lean

  The abstract weighted-Rellich step used in compact-resolvent proofs.  If a
  bounded resolvent lifts into a weighted energy space and the inclusion of
  that space into the Hilbert space is compact, then the resolvent is compact.

  Mathlib 4.32 contains compact operators but no Rellich--Kondrachov theorem
  for weighted Sobolev spaces.  Accordingly this module proves every routing
  step after the compact embedding and records that embedding as an explicit,
  non-vacuous `IsCompactOperator` field.
-/
import Mathlib
import Brockian.WeylKatoResolventPackage

namespace Brockian.Weyl.WeightedRellich

open Brockian.Weyl.KatoResolventPackage

variable {H E Eadd Esub : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Eadd] [NormedSpace ℂ Eadd]
  [NormedAddCommGroup Esub] [NormedSpace ℂ Esub]

/-- A resolvent factorization through a compactly embedded weighted space.
The `lift` is the elliptic estimate; `compact_embedding` is the weighted
Rellich theorem; `factorization` identifies their composite with the actual
resolvent. -/
structure Factorization (R : H →L[ℂ] H) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] where
  embedding : E →L[ℂ] H
  lift : H →L[ℂ] E
  compact_embedding : IsCompactOperator embedding
  factorization : embedding.comp lift = R

/-- The compact-embedding factorization makes the resolvent compact. -/
theorem Factorization.isCompactOperator {R : H →L[ℂ] H}
    (F : Factorization R E) : IsCompactOperator R := by
  change IsCompactOperator (fun x : H => R x)
  have heq : (fun x : H => F.embedding (F.lift x)) = fun x : H => R x := by
    funext x
    exact congrArg (fun A : H →L[ℂ] H => A x) F.factorization
  rw [← heq]
  exact F.compact_embedding.comp_clm F.lift

/-- Compactness gives compact closure of the image of every closed ball. -/
theorem Factorization.isCompact_closure_image_closedBall {R : H →L[ℂ] H}
    (F : Factorization R E) (r : ℝ) :
    IsCompact (closure (R '' Metric.closedBall 0 r)) :=
  F.isCompactOperator.isCompact_closure_image_closedBall r

/-- The factorization interface is exact: an already compact map factors
through itself and the identity. -/
noncomputable def Factorization.ofCompact (R : H →L[ℂ] H)
    (hR : IsCompactOperator R) : Factorization R H where
  embedding := R
  lift := ContinuousLinearMap.id ℂ H
  compact_embedding := hR
  factorization := by ext x; rfl

/-- Both unit-shift resolvents are compact once each has a weighted-Rellich
factorization. -/
theorem compact_resolvents_of_factorizations {T : H →ₗ.[ℂ] H}
    (hres : ResolventAtI T)
    (Fadd : Factorization hres.Radd Eadd)
    (Fsub : Factorization hres.Rsub Esub) :
    IsCompactOperator hres.Radd ∧ IsCompactOperator hres.Rsub :=
  ⟨Fadd.isCompactOperator, Fsub.isCompactOperator⟩

end Brockian.Weyl.WeightedRellich
