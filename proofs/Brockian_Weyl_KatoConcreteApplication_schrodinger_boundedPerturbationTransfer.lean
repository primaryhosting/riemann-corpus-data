/-
  Concrete application of the bounded-perturbation interface to the verified
  one-dimensional Schrodinger operator.

  The independent weak-energy proof already establishes essential
  self-adjointness for every continuous bounded real potential.  Combining
  that theorem with the exact `schrodingerPMap = perturb free potential`
  identity discharges `BoundedPerturbationTransfer` for this concrete family.

  The later theorems in this module also apply the unconditional general
  Kato-Rellich theorem to the same concrete operator.  The free-core ESA input
  is obtained by specializing the independent weak-energy theorem to `V = 0`.
-/
import Brockian.WeylSchrodingerGate1Closed
import Brockian.WeylSchrodingerGate1Final
import Brockian.WeylKatoRangeDensity
import Brockian.WeylKatoRellich

namespace Brockian.Weyl.KatoConcreteApplication

open Brockian.Weyl.KatoUnbounded
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Closed
open Brockian.Weyl.SchrodingerGate1Final

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

def zeroPotential : Real -> Real := fun _ => 0

theorem continuous_zeroPotential : Continuous zeroPotential := continuous_const

theorem zeroPotential_bound : forall x, |zeroPotential x| <= 0 := by
  intro x
  simp [zeroPotential]

/-- Multiplication by the zero potential is the zero bounded operator. -/
theorem potentialMulCLM_zero :
    potentialMulCLM zeroPotential continuous_zeroPotential 0 zeroPotential_bound =
      (0 : L2R →L[Complex] L2R) := by
  ext u
  filter_upwards [Brockian.WeylWeakEnergy.potentialMulCLM_coeFn
      zeroPotential continuous_zeroPotential 0 zeroPotential_bound u] with x hmul
  rw [hmul]
  simp [zeroPotential]

/-- The free Schwartz-core Laplacian is ESA, obtained as the zero-potential
specialization of the independent weak-energy theorem. -/
theorem freeSchrodingerPMap_essentiallySelfAdjoint :
    EssentiallySelfAdjoint freeSchrodingerPMap := by
  have h := schrodinger_core_essentiallySelfAdjoint zeroPotential
    continuous_zeroPotential 0 zeroPotential_bound
  rw [schrodingerPMap_eq_perturb_free, potentialMulCLM_zero,
    Brockian.Weyl.KatoRangeDensity.perturb_zero_eq] at h
  exact h

/-- The concrete bounded multiplication perturbation satisfies the exact
range-density transfer required by the Kato interface. The input ESA theorem
comes from the independent weak Fourier-energy route. -/
theorem schrodinger_boundedPerturbationTransfer
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    BoundedPerturbationTransfer freeSchrodingerPMap
      (potentialMulCLM V hVc M hV) :=
  (schrodinger_essentiallySelfAdjoint_iff_katoTransfer V hVc M hV).mp
    (schrodinger_core_essentiallySelfAdjoint V hVc M hV)

/-- End-to-end application of the Kato assembly to the actual
`-d^2/dx^2 + V` Schwartz-core operator. The transfer premise is supplied by
`schrodinger_boundedPerturbationTransfer`, not left as a conditional input. -/
theorem schrodinger_essentiallySelfAdjoint_via_kato_application
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_katoTransfer V hVc M hV
    (schrodinger_boundedPerturbationTransfer V hVc M hV)

/-- Direct application of the unconditional bounded Kato-Rellich theorem to
the concrete decomposition `-d^2 + V`. -/
theorem schrodinger_essentiallySelfAdjoint_via_kato_rellich
    (V : Real -> Real) (hVc : Continuous V) (M : Real)
    (hV : forall x, |V x| <= M) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) := by
  rw [schrodingerPMap_eq_perturb_free]
  exact Brockian.Weyl.KatoRellich.essentiallySelfAdjoint_bounded_perturbation
    freeSchrodingerPMap_isSymmetric freeSchrodingerPMap_dense
    freeSchrodingerPMap_essentiallySelfAdjoint
    (isSelfAdjoint_potentialMulCLM V hVc M hV)

end Brockian.Weyl.KatoConcreteApplication
