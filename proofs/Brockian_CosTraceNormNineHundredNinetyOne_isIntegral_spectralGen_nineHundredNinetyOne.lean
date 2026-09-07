/-
  Brockian/CosTraceNormNineHundredNinetyOne.lean — spectral generator at p = 991.

  [ℚ(2 cos 2π/991):ℚ] = 495 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredNinetyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredNinetyOne : Nat.Prime 991 := by decide

theorem nineHundredNinetyOne_ne_two : (991 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredNinetyOne : (minpoly ℚ (spectralGen 991)).natDegree = 495 :=
  real_subfield_degree prime_nineHundredNinetyOne nineHundredNinetyOne_ne_two

theorem isIntegral_spectralGen_nineHundredNinetyOne : IsIntegral ℤ (spectralGen 991) :=
  isIntegral_spectralGen prime_nineHundredNinetyOne

theorem isIntegral_spectralGen_nineHundredNinetyOne_Q : IsIntegral ℚ (spectralGen 991) :=
  isIntegral_spectralGen_ℚ prime_nineHundredNinetyOne

theorem isIntegral_and_degree_nineHundredNinetyOne :
    IsIntegral ℤ (spectralGen 991) ∧
      (minpoly ℚ (spectralGen 991)).natDegree = 495 :=
  ⟨isIntegral_spectralGen_nineHundredNinetyOne, degree_nineHundredNinetyOne⟩

theorem nineHundredNinetyOne_pack :
    IsIntegral ℤ (spectralGen 991) ∧
      (minpoly ℚ (spectralGen 991)).natDegree = 495 :=
  isIntegral_and_degree_nineHundredNinetyOne

end Brockian.CosTraceNormNineHundredNinetyOne
