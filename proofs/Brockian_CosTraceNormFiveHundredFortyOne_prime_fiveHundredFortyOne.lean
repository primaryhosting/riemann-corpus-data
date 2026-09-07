/-
  Brockian/CosTraceNormFiveHundredFortyOne.lean — spectral generator at p = 541.

  [ℚ(2 cos 2π/541):ℚ] = 270 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredFortyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredFortyOne : Nat.Prime 541 := by decide

theorem fiveHundredFortyOne_ne_two : (541 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredFortyOne : (minpoly ℚ (spectralGen 541)).natDegree = 270 :=
  real_subfield_degree prime_fiveHundredFortyOne fiveHundredFortyOne_ne_two

theorem isIntegral_spectralGen_fiveHundredFortyOne : IsIntegral ℤ (spectralGen 541) :=
  isIntegral_spectralGen prime_fiveHundredFortyOne

theorem isIntegral_spectralGen_fiveHundredFortyOne_Q : IsIntegral ℚ (spectralGen 541) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredFortyOne

theorem isIntegral_and_degree_fiveHundredFortyOne :
    IsIntegral ℤ (spectralGen 541) ∧
      (minpoly ℚ (spectralGen 541)).natDegree = 270 :=
  ⟨isIntegral_spectralGen_fiveHundredFortyOne, degree_fiveHundredFortyOne⟩

theorem fiveHundredFortyOne_pack :
    IsIntegral ℤ (spectralGen 541) ∧
      (minpoly ℚ (spectralGen 541)).natDegree = 270 :=
  isIntegral_and_degree_fiveHundredFortyOne

end Brockian.CosTraceNormFiveHundredFortyOne
