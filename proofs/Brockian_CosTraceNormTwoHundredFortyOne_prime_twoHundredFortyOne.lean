/-
  Brockian/CosTraceNormTwoHundredFortyOne.lean — spectral generator at p = 241.

  [ℚ(2 cos 2π/241):ℚ] = 120 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredFortyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredFortyOne : Nat.Prime 241 := by decide

theorem twoHundredFortyOne_ne_two : (241 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredFortyOne : (minpoly ℚ (spectralGen 241)).natDegree = 120 :=
  real_subfield_degree prime_twoHundredFortyOne twoHundredFortyOne_ne_two

theorem isIntegral_spectralGen_twoHundredFortyOne : IsIntegral ℤ (spectralGen 241) :=
  isIntegral_spectralGen prime_twoHundredFortyOne

theorem isIntegral_spectralGen_twoHundredFortyOne_Q : IsIntegral ℚ (spectralGen 241) :=
  isIntegral_spectralGen_ℚ prime_twoHundredFortyOne

theorem isIntegral_and_degree_twoHundredFortyOne :
    IsIntegral ℤ (spectralGen 241) ∧
      (minpoly ℚ (spectralGen 241)).natDegree = 120 :=
  ⟨isIntegral_spectralGen_twoHundredFortyOne, degree_twoHundredFortyOne⟩

theorem twoHundredFortyOne_pack :
    IsIntegral ℤ (spectralGen 241) ∧
      (minpoly ℚ (spectralGen 241)).natDegree = 120 :=
  isIntegral_and_degree_twoHundredFortyOne

end Brockian.CosTraceNormTwoHundredFortyOne
