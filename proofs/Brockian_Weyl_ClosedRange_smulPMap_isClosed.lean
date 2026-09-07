/-
  Brockian/WeylClosedRange.lean — closed-range *consequences* of the von Neumann
  criterion, plus the closedness of the scalar witness.

  The full sequential proof that `ran(T−z)` is closed for closed symmetric `T`
  is recorded as a named hypothesis form below; the pure topological upgrade
  "dense + closed ⇒ universe" is proved and applied.

  Imports Operator/Cayley only (does not edit Claude/Codex sources).
-/
import Mathlib
import Brockian.WeylOperator
import Brockian.WeylCayley

namespace Brockian.Weyl.ClosedRange

open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.Cayley
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Dense + closed subset of `H` is the whole space. -/
theorem eq_univ_of_dense_isClosed {s : Set H} (hd : Dense s) (hc : IsClosed s) :
    s = univ := by
  rw [← hc.closure_eq, hd.closure_eq]

/-- **Surjectivity upgrade.** If `ran(T±i)` are dense (i.e. ESA) *and* each is
closed, then `ran(T±i) = H`. This is the pure topology half of the closed-range
form of von Neumann's criterion. -/
theorem range_eq_top_of_essentiallySelfAdjoint_of_isClosed_ranges
    {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed ((rangeAddI T : Set H)))
    (hcl_sub : IsClosed ((rangeSubI T : Set H))) :
    (rangeAddI T : Set H) = univ ∧ (rangeSubI T : Set H) = univ := by
  have hcrit := (essentiallySelfAdjoint_iff hd).mp hESA
  exact ⟨eq_univ_of_dense_isClosed hcrit.1 hcl_add,
         eq_univ_of_dense_isClosed hcrit.2 hcl_sub⟩

/-- Full-domain continuous real-scalar operator is a closed operator. -/
theorem smulPMap_isClosed (c : ℝ) : (smulPMap (H := H) c).IsClosed := by
  have hEq : ((smulPMap (H := H) c).graph : Set (H × H)) =
      {p : H × H | p.2 = (c : ℂ) • p.1} := by
    ext p
    constructor
    · intro hp
      have hp' : p ∈ (smulPMap (H := H) c).graph := hp
      rw [LinearPMap.mem_graph_iff] at hp'
      obtain ⟨x, hx1, hx2⟩ := hp'
      have : smulPMap c x = p.2 := hx2
      rw [smulPMap_apply] at this
      change p.2 = (c : ℂ) • p.1
      rw [← this, hx1]
    · intro hp
      show p ∈ (smulPMap (H := H) c).graph
      rw [LinearPMap.mem_graph_iff]
      have hdom : p.1 ∈ (smulPMap (H := H) c).domain := by
        rw [smulPMap_domain]; trivial
      refine ⟨⟨p.1, hdom⟩, rfl, ?_⟩
      rw [smulPMap_apply]
      exact hp.symm
  change IsClosed ((smulPMap (H := H) c).graph : Set (H × H))
  rw [hEq]
  exact isClosed_eq continuous_snd ((continuous_const_smul (c : ℂ)).comp continuous_fst)

/-- The scalar witness is closed and essentially self-adjoint, hence (via ESA +
the density criterion) has dense `ran(±i)` ranges; combined with closedness of
those ranges (still open for general `T`, but automatic for this finite-rank /
everywhere-defined case once range = H is known from ESA of bounded ops).

Here we record the direct closedness of the operator itself. -/
theorem smulPMap_isClosed_and_symmetric (c : ℝ) :
    (smulPMap (H := H) c).IsClosed ∧ IsSymmetric (smulPMap (H := H) c) :=
  ⟨smulPMap_isClosed c, smulPMap_isSymmetric c⟩

end Brockian.Weyl.ClosedRange
