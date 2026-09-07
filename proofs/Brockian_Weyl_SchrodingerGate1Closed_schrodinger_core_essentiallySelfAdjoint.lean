/-
  Brockian/WeylSchrodingerGate1Closed.lean

  End-to-end Gate 1 for the concrete one-dimensional Schrodinger operator on
  the Schwartz core.  The weak Fourier-energy theorem supplies essential
  self-adjointness; the abstract closed-range package then identifies the
  closure with the adjoint, proves that closure self-adjoint, and constructs
  its bounded resolvents at the two unit imaginary shifts.
-/
import Brockian.WeylWeakEnergy
import Brockian.WeylClosedShiftedRanges

open MeasureTheory Complex SchwartzMap
open scoped InnerProductSpace

namespace Brockian.Weyl.SchrodingerGate1Closed

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.ClosedRange
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.ClosedShiftedRanges

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- Continuous bounded real potentials give an essentially self-adjoint
minimal Schrodinger operator on the Schwartz core. -/
theorem schrodinger_core_essentiallySelfAdjoint
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  Brockian.WeylWeakEnergy.schrodinger_essentiallySelfAdjoint_of_continuous_bounded
    V hVc M hV

/-- The closure of the concrete minimal operator is exactly its adjoint. -/
theorem schrodinger_closure_eq_adjoint
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    (schrodingerPMap V hVc M hV).closure =
      (schrodingerPMap V hVc M hV).adjoint :=
  closure_eq_adjoint_of_essentiallySelfAdjoint
    (schrodingerPMap_isSymmetric V hVc M hV)
    (schrodingerPMap_dense V hVc M hV)
    (schrodinger_core_essentiallySelfAdjoint V hVc M hV)

/-- Both unit imaginary shifts of the self-adjoint closure are surjective. -/
theorem schrodinger_closure_shifted_ranges_eq_univ
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    (rangeAddI (schrodingerPMap V hVc M hV).closure : Set L2R) = Set.univ /\
      (rangeSubI (schrodingerPMap V hVc M hV).closure : Set L2R) = Set.univ :=
  closure_shifted_ranges_eq_univ_of_essentiallySelfAdjoint
    (schrodingerPMap_isSymmetric V hVc M hV)
    (schrodingerPMap_dense V hVc M hV)
    (schrodinger_core_essentiallySelfAdjoint V hVc M hV)

/-- The closure of the concrete minimal Schrodinger operator is self-adjoint. -/
theorem schrodinger_closure_isSelfAdjoint
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    IsSelfAdjoint (schrodingerPMap V hVc M hV).closure :=
  closure_isSelfAdjoint_of_essentiallySelfAdjoint
    (schrodingerPMap_isSymmetric V hVc M hV)
    (schrodingerPMap_dense V hVc M hV)
    (schrodinger_core_essentiallySelfAdjoint V hVc M hV)

/-- Canonical bounded right resolvents at both unit imaginary shifts of the
self-adjoint closure. -/
noncomputable def schrodinger_closureResolventAtI
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    ResolventAtI (schrodingerPMap V hVc M hV).closure :=
  closureResolventAtIOfEssentiallySelfAdjoint
    (schrodingerPMap_isSymmetric V hVc M hV)
    (schrodingerPMap_dense V hVc M hV)
    (schrodinger_core_essentiallySelfAdjoint V hVc M hV)

end Brockian.Weyl.SchrodingerGate1Closed
