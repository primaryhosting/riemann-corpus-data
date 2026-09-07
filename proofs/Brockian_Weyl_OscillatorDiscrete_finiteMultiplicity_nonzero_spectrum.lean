/-
  Brockian/WeylOscillatorDiscrete.lean

  Compact-resolvent and spectral consequences for the harmonic-oscillator
  route.  The weighted Rellich embedding and oscillator ESA remain explicit
  inputs; from them, compactness and the Fredholm nonzero-spectrum conclusion
  are proved without further analytic assumptions.

  Mathlib 4.32 does not provide spectral mapping for unbounded `LinearPMap`s or
  the isolation/accumulation theorem for compact-operator eigenvalues.  Thus we
  do not overstate the result as a complete discrete-spectrum theorem for the
  original unbounded operator.
-/
import Mathlib
import Brockian.WeylHarmonicOscillator
import Brockian.WeylWeightedRellich
import Brockian.WeylClosedShiftedRanges

namespace Brockian.Weyl.OscillatorDiscrete

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.ClosedShiftedRanges
open Brockian.Weyl.WeightedRellich
open Brockian.Weyl.HarmonicOscillator

variable {H Eadd Esub : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Eadd] [NormedSpace ℂ Eadd]
  [NormedAddCommGroup Esub] [NormedSpace ℂ Esub]

/-- Both canonical unit-shift resolvents of an operator, together with proofs
that they are compact operators. -/
structure CompactResolventAtI (T : H →ₗ.[ℂ] H) where
  resolvent : ResolventAtI T
  compact_add : IsCompactOperator resolvent.Radd
  compact_sub : IsCompactOperator resolvent.Rsub

/-- Weighted-Rellich factorizations construct a compact-resolvent package. -/
def CompactResolventAtI.ofFactorizations {T : H →ₗ.[ℂ] H}
    (hres : ResolventAtI T)
    (Fadd : Factorization hres.Radd Eadd)
    (Fsub : Factorization hres.Rsub Esub) : CompactResolventAtI T where
  resolvent := hres
  compact_add := Fadd.isCompactOperator
  compact_sub := Fsub.isCompactOperator

/-- The precise nonzero spectral conclusion supplied by Mathlib's Fredholm
alternative for compact operators. -/
def NonzeroSpectrumIsPointSpectrum (R : H →L[ℂ] H) : Prop :=
  ∀ μ : ℂ, μ ≠ 0 →
    (μ ∈ spectrum ℂ R ↔ Module.End.HasEigenvalue (R : Module.End ℂ H) μ)

/-- A compact operator's nonzero spectrum consists exactly of eigenvalues. -/
theorem nonzeroSpectrumIsPointSpectrum_of_isCompact (R : H →L[ℂ] H)
    (hR : IsCompactOperator R) : NonzeroSpectrumIsPointSpectrum R := by
  intro μ hμ
  exact (hR.hasEigenvalue_iff_mem_spectrum hμ).symm

/-- A nonzero eigenspace of a compact operator is finite-dimensional.  On the
eigenspace the operator is `μ` times the identity; compactness survives
restriction and rescaling by `μ⁻¹`, so the identity is compact. -/
theorem finiteDimensional_eigenspace_of_isCompact (R : H →L[ℂ] H)
    (hR : IsCompactOperator R) {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace (R : Module.End ℂ H) μ) := by
  let E := Module.End.eigenspace (R : Module.End ℂ H) μ
  have hcomp : IsCompactOperator (fun x : E => R (x : H)) := by
    simpa [Function.comp_def] using hR.comp_clm E.subtypeL
  have hmaps : ∀ x : E, R (x : H) ∈ E := by
    intro x
    rw [Module.End.mem_eigenspace_iff]
    have hx : R (x : H) = μ • (x : H) :=
      Module.End.mem_eigenspace_iff.mp x.2
    calc
      R (R (x : H)) = R (μ • (x : H)) := congrArg R hx
      _ = μ • R (x : H) := map_smul R μ (x : H)
  have hcod : IsCompactOperator
      (Set.codRestrict (fun x : E => R (x : H)) E hmaps) :=
    hcomp.codRestrict hmaps (ContinuousLinearMap.isClosed_eigenspace R μ)
  have hscaled : IsCompactOperator
      (μ⁻¹ • Set.codRestrict (fun x : E => R (x : H)) E hmaps) :=
    hcod.smul μ⁻¹
  have heq :
      (μ⁻¹ • Set.codRestrict (fun x : E => R (x : H)) E hmaps) =
        (id : E → E) := by
    funext x
    apply Subtype.ext
    change μ⁻¹ • R (x : H) = (x : H)
    calc
      μ⁻¹ • R (x : H) = μ⁻¹ • (μ • (x : H)) :=
        congrArg (fun y : H => μ⁻¹ • y) (Module.End.mem_eigenspace_iff.mp x.2)
      _ = (x : H) := inv_smul_smul₀ hμ (x : H)
  apply FiniteDimensional.of_isCompactOperator_id
  rw [← heq]
  exact hscaled

/-- The nonzero compact-operator spectrum is point spectrum with finite
multiplicity.  Isolation and the assertion that zero is the only accumulation
point are deliberately not included. -/
def FiniteMultiplicityNonzeroSpectrum (R : H →L[ℂ] H) : Prop :=
  ∀ μ : ℂ, μ ≠ 0 →
    (μ ∈ spectrum ℂ R ↔ Module.End.HasEigenvalue (R : Module.End ℂ H) μ) ∧
      FiniteDimensional ℂ (Module.End.eigenspace (R : Module.End ℂ H) μ)

/-- Compactness supplies the finite-multiplicity nonzero spectral package. -/
theorem finiteMultiplicityNonzeroSpectrum_of_isCompact (R : H →L[ℂ] H)
    (hR : IsCompactOperator R) : FiniteMultiplicityNonzeroSpectrum R := by
  intro μ hμ
  exact ⟨(hR.hasEigenvalue_iff_mem_spectrum hμ).symm,
    finiteDimensional_eigenspace_of_isCompact R hR hμ⟩

/-- Both resolvents in a compact-resolvent package have nonzero point spectrum. -/
theorem CompactResolventAtI.nonzero_spectrum_is_point_spectrum
    {T : H →ₗ.[ℂ] H} (h : CompactResolventAtI T) :
    NonzeroSpectrumIsPointSpectrum h.resolvent.Radd ∧
      NonzeroSpectrumIsPointSpectrum h.resolvent.Rsub :=
  ⟨nonzeroSpectrumIsPointSpectrum_of_isCompact _ h.compact_add,
    nonzeroSpectrumIsPointSpectrum_of_isCompact _ h.compact_sub⟩

/-- Both compact unit resolvents have nonzero point spectrum of finite
multiplicity. -/
theorem CompactResolventAtI.finiteMultiplicity_nonzero_spectrum
    {T : H →ₗ.[ℂ] H} (h : CompactResolventAtI T) :
    FiniteMultiplicityNonzeroSpectrum h.resolvent.Radd ∧
      FiniteMultiplicityNonzeroSpectrum h.resolvent.Rsub :=
  ⟨finiteMultiplicityNonzeroSpectrum_of_isCompact _ h.compact_add,
    finiteMultiplicityNonzeroSpectrum_of_isCompact _ h.compact_sub⟩

/-- The canonical unit-shift resolvents on the self-adjoint closure of an
essentially self-adjoint harmonic-oscillator core. -/
noncomputable def harmonicOscillatorClosureResolventAtI
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap) :
    ResolventAtI harmonicOscillatorPMap.closure :=
  closureResolventAtIOfEssentiallySelfAdjoint
    harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense hESA

/-- Oscillator ESA plus the two weighted-Rellich factorizations gives compact
unit resolvents for the self-adjoint closure. -/
noncomputable def harmonicOscillatorCompactResolventAtI_of_weightedRellich
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap)
    (Fadd : Factorization (harmonicOscillatorClosureResolventAtI hESA).Radd Eadd)
    (Fsub : Factorization (harmonicOscillatorClosureResolventAtI hESA).Rsub Esub) :
    CompactResolventAtI harmonicOscillatorPMap.closure :=
  CompactResolventAtI.ofFactorizations
    (harmonicOscillatorClosureResolventAtI hESA) Fadd Fsub

/-- The verified spectral consequence for the oscillator closure: under ESA
and weighted Rellich, every nonzero spectral value of either unit resolvent is
an eigenvalue. -/
theorem harmonicOscillator_resolvent_nonzero_spectrum_of_weightedRellich
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap)
    (Fadd : Factorization (harmonicOscillatorClosureResolventAtI hESA).Radd Eadd)
    (Fsub : Factorization (harmonicOscillatorClosureResolventAtI hESA).Rsub Esub) :
    NonzeroSpectrumIsPointSpectrum
        (harmonicOscillatorClosureResolventAtI hESA).Radd ∧
      NonzeroSpectrumIsPointSpectrum
        (harmonicOscillatorClosureResolventAtI hESA).Rsub :=
  CompactResolventAtI.nonzero_spectrum_is_point_spectrum
    (harmonicOscillatorCompactResolventAtI_of_weightedRellich hESA Fadd Fsub)

/-- Finite-multiplicity refinement of the oscillator resolvent conclusion. -/
theorem harmonicOscillator_resolvent_finiteMultiplicity_of_weightedRellich
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap)
    (Fadd : Factorization (harmonicOscillatorClosureResolventAtI hESA).Radd Eadd)
    (Fsub : Factorization (harmonicOscillatorClosureResolventAtI hESA).Rsub Esub) :
    FiniteMultiplicityNonzeroSpectrum
        (harmonicOscillatorClosureResolventAtI hESA).Radd ∧
      FiniteMultiplicityNonzeroSpectrum
        (harmonicOscillatorClosureResolventAtI hESA).Rsub :=
  CompactResolventAtI.finiteMultiplicity_nonzero_spectrum
    (harmonicOscillatorCompactResolventAtI_of_weightedRellich hESA Fadd Fsub)

end Brockian.Weyl.OscillatorDiscrete
