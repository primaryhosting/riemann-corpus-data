/-
  Brockian/WeylGate1Bounded.lean — Gate 1 for the *bounded* Brockian potential.

  Composes already-verified pieces (no new analysis):

    SpectralGate1.isSelfAdjoint_primeGaussianMulCLM
    Weyl.ESA.clm_essentiallySelfAdjoint
    Weyl.Kato.dense_range_add_sub_of_selfAdjoint / isSelfAdjoint_add

  ## What is proved

    * `primeGaussianMul_essentiallySelfAdjoint`
    * `primeGaussianMul_dense_range_sub`
    * `add_primeGaussian_dense_range_sub`
    * `add_primeGaussian_isSelfAdjoint`
    * `add_primeGaussian_essentiallySelfAdjoint`

  ## Honest scope

  Not essential self-adjointness of unbounded `−d²/dx² + V`. That still needs
  the Laplacian plus continuous-bounded-V / bridge-deficiency targets.
-/
import Mathlib
import Brockian.SpectralGate1
import Brockian.WeylEssSelfAdjoint
import Brockian.WeylKato
import Brockian.WeylOperator

open MeasureTheory
open Brockian.SpectralGate1
open Brockian.Weyl.Operator Brockian.Weyl.ESA Brockian.Weyl.Kato

namespace Brockian.Weyl.Gate1Bounded

/-- The L² space of the Brockian potential (notation only). -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **Gate 1 (potential term).** Prime-Gaussian multiplication is essentially
self-adjoint on `L²(ℝ)`. -/
theorem primeGaussianMul_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤) :=
  clm_essentiallySelfAdjoint primeGaussianMulCLM isSelfAdjoint_primeGaussianMulCLM

/-- Non-real shift of the potential has dense range (Kato with free part `0`). -/
theorem primeGaussianMul_dense_range_sub {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Set.range fun v : H2 => primeGaussianMulCLM v - z • v) := by
  -- free part 0 is self-adjoint; 0 + M_V = M_V
  have h0 : IsSelfAdjoint (0 : H2 →L[ℂ] H2) := IsSelfAdjoint.zero (R := H2 →L[ℂ] H2)
  simpa using dense_range_add_sub_of_selfAdjoint h0 isSelfAdjoint_primeGaussianMulCLM z hz

/-- Bounded free part + Brockian potential: dense range of non-real shifts. -/
theorem add_primeGaussian_dense_range_sub {T : H2 →L[ℂ] H2}
    (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Set.range fun v => (T + primeGaussianMulCLM) v - z • v) :=
  dense_range_add_sub_of_selfAdjoint hT isSelfAdjoint_primeGaussianMulCLM z hz

theorem add_primeGaussian_isSelfAdjoint {T : H2 →L[ℂ] H2}
    (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (T + primeGaussianMulCLM) :=
  isSelfAdjoint_add hT isSelfAdjoint_primeGaussianMulCLM

theorem add_primeGaussian_essentiallySelfAdjoint {T : H2 →L[ℂ] H2}
    (hT : IsSelfAdjoint T) :
    EssentiallySelfAdjoint ((T + primeGaussianMulCLM).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (add_primeGaussian_isSelfAdjoint hT)

end Brockian.Weyl.Gate1Bounded
