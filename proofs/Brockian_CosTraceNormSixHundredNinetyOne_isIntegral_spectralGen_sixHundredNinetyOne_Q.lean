/-
  Brockian/CosTraceNormSixHundredNinetyOne.lean — spectral generator at p = 691.

  [ℚ(2 cos 2π/691):ℚ] = 345 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredNinetyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredNinetyOne : Nat.Prime 691 := by decide

theorem sixHundredNinetyOne_ne_two : (691 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredNinetyOne : (minpoly ℚ (spectralGen 691)).natDegree = 345 :=
  real_subfield_degree prime_sixHundredNinetyOne sixHundredNinetyOne_ne_two

theorem isIntegral_spectralGen_sixHundredNinetyOne : IsIntegral ℤ (spectralGen 691) :=
  isIntegral_spectralGen prime_sixHundredNinetyOne

theorem isIntegral_spectralGen_sixHundredNinetyOne_Q : IsIntegral ℚ (spectralGen 691) :=
  isIntegral_spectralGen_ℚ prime_sixHundredNinetyOne

theorem isIntegral_and_degree_sixHundredNinetyOne :
    IsIntegral ℤ (spectralGen 691) ∧
      (minpoly ℚ (spectralGen 691)).natDegree = 345 :=
  ⟨isIntegral_spectralGen_sixHundredNinetyOne, degree_sixHundredNinetyOne⟩

theorem sixHundredNinetyOne_pack :
    IsIntegral ℤ (spectralGen 691) ∧
      (minpoly ℚ (spectralGen 691)).natDegree = 345 :=
  isIntegral_and_degree_sixHundredNinetyOne

end Brockian.CosTraceNormSixHundredNinetyOne
