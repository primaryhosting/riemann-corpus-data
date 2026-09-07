/-
  Brockian/WeylUpstream.lean

  General Hilbert-space statements extracted from the Weyl campaign.  The
  declarations in this module mention neither the Brockian potential nor RH;
  they are candidates for a later Mathlib contribution.
-/
import Brockian.WeylClosedShiftedRanges
import Brockian.WeylSelfAdjointExtension

namespace Brockian.Weyl.Upstream

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.Closure
open Brockian.Weyl.ClosedRangeClosure
open Brockian.Weyl.ClosedShiftedRanges
open Brockian.Weyl.Extension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- If a symmetric core has self-adjoint closure, every nonreal deficiency
space of the core is trivial.  This is useful beyond the special unit shifts
used in the definition of essential self-adjointness. -/
theorem deficiencySpace_eq_bot_of_closure_isSelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H))
    (hclosure : IsSelfAdjoint T.closure) {z : ℂ} (hz : z.im ≠ 0) :
    deficiencySpace T z = ⊥ := by
  have heq : T.closure = T.adjoint :=
    (isSelfAdjoint_closure_iff_eq_adjoint hT hd).mp hclosure
  rw [Submodule.eq_bot_iff]
  intro g hg
  have heig : T.adjoint g = z • (g : H) :=
    (mem_deficiencySpace_iff T z g).mp hg
  have hgraph : ((g : H), z • (g : H)) ∈ T.closure.graph := by
    have hadj : ((g : H), z • (g : H)) ∈ T.adjoint.graph := by
      simpa [heig] using T.adjoint.mem_graph g
    rwa [heq]
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨v, hv, hTv⟩ := hgraph
  have hv0 : (v : H) = 0 :=
    (closure_isSymmetric hT hd).eq_zero_of_apply_eq_smul hz (by
      simpa [hv] using hTv)
  have hvg : (v : H) = (g : H) := by
    simpa using hv
  apply Subtype.ext
  change (g : H) = 0
  rw [← hvg]
  exact hv0

/-- For a densely defined symmetric operator, the deficiency-space definition
of essential self-adjointness is equivalent to self-adjointness of its graph
closure.  This is the standard closure formulation of von Neumann's criterion. -/
theorem essentiallySelfAdjoint_iff_closure_isSelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) :
    EssentiallySelfAdjoint T ↔ IsSelfAdjoint T.closure := by
  constructor
  · exact closure_isSelfAdjoint_of_essentiallySelfAdjoint hT hd
  · intro hclosure
    constructor
    · exact deficiencySpace_eq_bot_of_closure_isSelfAdjoint hT hd hclosure
        (by norm_num [Complex.I_im])
    · exact deficiencySpace_eq_bot_of_closure_isSelfAdjoint hT hd hclosure
        (by norm_num [Complex.I_im])

end Brockian.Weyl.Upstream
