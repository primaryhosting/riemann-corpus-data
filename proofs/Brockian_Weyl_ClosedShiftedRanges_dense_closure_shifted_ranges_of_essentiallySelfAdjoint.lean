/-
  Assembly from the project's deficiency-space definition of essential
  self-adjointness to the self-adjoint closure.

  The analytic closed-range theorem is deliberately not proved here.  The
  results below isolate it as the two hypotheses that the shifted ranges of
  `T.closure` are closed.  Once those hypotheses are supplied, core ESA gives
  density of the closure ranges, hence surjectivity, `T.closure = T.adjoint`,
  self-adjointness of the closure, and bounded resolvents at both unit shifts.
-/
import Mathlib
import Brockian.WeylClosedRange
import Brockian.WeylClosedRangeClosure
import Brockian.WeylResolventFromESA
import Brockian.WeylSelfAdjointExtension

namespace Brockian.Weyl.ClosedShiftedRanges

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.Cayley
open Brockian.Weyl.ClosedRange
open Brockian.Weyl.ClosedRangeClosure
open Brockian.Weyl.ResolventFromESA
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.Extension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### A core's shifted range lies in the extension's shifted range -/

/-- The `T + i` core range is contained in the corresponding closure range. -/
theorem rangeAddI_le_closure (T : H →ₗ.[ℂ] H) :
    rangeAddI T ≤ rangeAddI T.closure := by
  simpa [rangeAddI] using rangeSMulSub_mono (LinearPMap.le_closure T) (-Complex.I)

/-- The `T - i` core range is contained in the corresponding closure range. -/
theorem rangeSubI_le_closure (T : H →ₗ.[ℂ] H) :
    rangeSubI T ≤ rangeSubI T.closure := by
  simpa [rangeSubI] using rangeSMulSub_mono (LinearPMap.le_closure T) Complex.I

/-! ### ESA density transfers from the core to its closure -/

/-- Core ESA makes both shifted ranges of `T.closure` dense.  This uses only
the von Neumann density criterion for the core and range monotonicity. -/
theorem dense_closure_shifted_ranges_of_essentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hESA : EssentiallySelfAdjoint T) :
    Dense (rangeAddI T.closure : Set H) ∧
      Dense (rangeSubI T.closure : Set H) := by
  have hcore := (essentiallySelfAdjoint_iff hd).mp hESA
  exact
    ⟨hcore.1.mono (SetLike.coe_subset_coe.mpr (rangeAddI_le_closure T)),
      hcore.2.mono (SetLike.coe_subset_coe.mpr (rangeSubI_le_closure T))⟩

/-- If the two shifted ranges of the closure are closed, core ESA upgrades
them from dense to all of `H`.  These closedness assumptions are precisely the
analytic input owned by the closed-range module. -/
theorem closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint_of_isClosed
    {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T.closure : Set H))
    (hcl_sub : IsClosed (rangeSubI T.closure : Set H)) :
    (rangeAddI T.closure : Set H) = Set.univ ∧
      (rangeSubI T.closure : Set H) = Set.univ := by
  have hrange := dense_closure_shifted_ranges_of_essentiallySelfAdjoint hd hESA
  exact
    ⟨eq_univ_of_dense_isClosed hrange.1 hcl_add,
      eq_univ_of_dense_isClosed hrange.2 hcl_sub⟩

/-- The closure of a densely defined symmetric operator has closed unit-shift
ranges.  This is the assembly point for the analytic theorem proved in
`WeylClosedRangeClosure`. -/
theorem isClosed_closure_shifted_ranges
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) :
    IsClosed (rangeAddI T.closure : Set H) ∧
      IsClosed (rangeSubI T.closure : Set H) := by
  have hclosable : T.IsClosable :=
    Brockian.Weyl.Closure.symmetric_isClosable hT hd
  exact isClosed_rangeAddI_and_rangeSubI
    hclosable.closure_isClosed (closure_isSymmetric hT hd)

/-- For an essentially self-adjoint symmetric core, both unit shifts of its
closure are surjective. -/
theorem closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T) :
    (rangeAddI T.closure : Set H) = Set.univ ∧
      (rangeSubI T.closure : Set H) = Set.univ := by
  have hclosed := isClosed_closure_shifted_ranges hT hd
  exact closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint_of_isClosed
    hd hESA hclosed.1 hclosed.2

/-! ### Surjectivity closes the adjoint-domain gap -/

/-- Surjectivity of `T.closure + i`, together with vanishing `-i` deficiency,
puts every vector in `dom(T*)` into `dom(T.closure)`. -/
theorem adjoint_domain_le_closure_domain_of_essentiallySelfAdjoint_of_rangeAddI
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T)
    (hadd : (rangeAddI T.closure : Set H) = Set.univ) :
    T.adjoint.domain ≤ T.closure.domain := by
  intro y hy
  let yAdj : T.adjoint.domain := ⟨y, hy⟩
  have hu : T.adjoint yAdj + Complex.I • y ∈
      (rangeAddI T.closure : Set H) := by
    rw [hadd]
    exact Set.mem_univ _
  rw [rangeAddI] at hu
  obtain ⟨v, hv⟩ := mem_rangeSMulSub.mp hu
  have hcl_le : T.closure ≤ T.adjoint :=
    Brockian.Weyl.Closure.symmetric_closure_le_adjoint hT hd
  have hvAdj : (v : H) ∈ T.adjoint.domain := hcl_le.1 v.2
  let vAdj : T.adjoint.domain := ⟨(v : H), hvAdj⟩
  have hvact : T.adjoint.toFun vAdj = T.closure v := (hcl_le.2 rfl).symm
  have hv' : T.closure v + Complex.I • (v : H) =
      T.adjoint yAdj + Complex.I • y := by
    simpa using hv
  have hyact : T.adjoint.toFun yAdj =
      T.closure v + Complex.I • (v : H) - Complex.I • y := by
    exact (eq_sub_iff_add_eq).2 hv'.symm
  let d : T.adjoint.domain := yAdj - vAdj
  have hdeig : T.adjoint d = (-Complex.I) • (d : H) := by
    change T.adjoint.toFun (yAdj - vAdj) =
      (-Complex.I) • ((yAdj : H) - (vAdj : H))
    rw [T.adjoint.toFun.map_sub, hvact, hyact]
    module
  have hd0 : (d : H) = 0 :=
    adjoint_eigen_neg_I_eq_zero_of_essSA hESA hdeig
  have hyv : y = (v : H) := by
    apply sub_eq_zero.mp
    simpa [d, yAdj, vAdj] using hd0
  rw [hyv]
  exact v.2

/-- Under core ESA and closed shifted ranges of the closure, the closure is
exactly the adjoint. -/
theorem closure_eq_adjoint_of_essentiallySelfAdjoint_of_isClosed_ranges
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T.closure : Set H))
    (hcl_sub : IsClosed (rangeSubI T.closure : Set H)) :
    T.closure = T.adjoint := by
  have hranges :=
    closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint_of_isClosed
      hd hESA hcl_add hcl_sub
  apply le_antisymm
  · exact Brockian.Weyl.Closure.symmetric_closure_le_adjoint hT hd
  · refine ⟨adjoint_domain_le_closure_domain_of_essentiallySelfAdjoint_of_rangeAddI
        hT hd hESA hranges.1, ?_⟩
    intro x y hxy
    have hcl_le : T.closure ≤ T.adjoint :=
      Brockian.Weyl.Closure.symmetric_closure_le_adjoint hT hd
    exact (hcl_le.2 hxy.symm).symm

/-- Core ESA plus the analytic closed-range theorem makes the closure genuinely
self-adjoint. -/
theorem closure_isSelfAdjoint_of_essentiallySelfAdjoint_of_isClosed_ranges
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T.closure : Set H))
    (hcl_sub : IsClosed (rangeSubI T.closure : Set H)) :
    IsSelfAdjoint T.closure := by
  exact (isSelfAdjoint_closure_iff_eq_adjoint hT hd).2
    (closure_eq_adjoint_of_essentiallySelfAdjoint_of_isClosed_ranges
      hT hd hESA hcl_add hcl_sub)

/-- The project definition of essential self-adjointness now implies the
classical closure identity `T̄ = T*`. -/
theorem closure_eq_adjoint_of_essentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T) :
    T.closure = T.adjoint := by
  have hclosed := isClosed_closure_shifted_ranges hT hd
  exact closure_eq_adjoint_of_essentiallySelfAdjoint_of_isClosed_ranges
    hT hd hESA hclosed.1 hclosed.2

/-- A densely defined symmetric operator with trivial unit deficiency spaces
has a self-adjoint closure. -/
theorem closure_isSelfAdjoint_of_essentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T) :
    IsSelfAdjoint T.closure := by
  exact (isSelfAdjoint_closure_iff_eq_adjoint hT hd).2
    (closure_eq_adjoint_of_essentiallySelfAdjoint hT hd hESA)

/-! ### Resolvents on the self-adjoint closure -/

/-- Core ESA plus closed closure-ranges constructs the bounded right resolvents
at both unit shifts on the self-adjoint closure. -/
noncomputable def closureResolventAtIOfEssentiallySelfAdjointOfIsClosedRanges
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T.closure : Set H))
    (hcl_sub : IsClosed (rangeSubI T.closure : Set H)) :
    ResolventAtI T.closure := by
  have hranges :=
    closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint_of_isClosed
      hd hESA hcl_add hcl_sub
  exact resolventAtIOfSurjectiveShiftedRanges
    (closure_isSymmetric hT hd) hranges.1 hranges.2

/-- The canonical bounded unit-shift resolvents on the self-adjoint closure of an
essentially self-adjoint symmetric core. -/
noncomputable def closureResolventAtIOfEssentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) (hESA : EssentiallySelfAdjoint T) :
    ResolventAtI T.closure := by
  have hranges :=
    closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint hT hd hESA
  exact resolventAtIOfSurjectiveShiftedRanges
    (closure_isSymmetric hT hd) hranges.1 hranges.2

end Brockian.Weyl.ClosedShiftedRanges
