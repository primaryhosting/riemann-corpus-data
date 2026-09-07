/-
  Brockian/CosTraceNormNineHundredFortyOne.lean — spectral generator at p = 941.

  [ℚ(2 cos 2π/941):ℚ] = 470 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredFortyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredFortyOne : Nat.Prime 941 := by decide

theorem nineHundredFortyOne_ne_two : (941 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredFortyOne : (minpoly ℚ (spectralGen 941)).natDegree = 470 :=
  real_subfield_degree prime_nineHundredFortyOne nineHundredFortyOne_ne_two

theorem isIntegral_spectralGen_nineHundredFortyOne : IsIntegral ℤ (spectralGen 941) :=
  isIntegral_spectralGen prime_nineHundredFortyOne

theorem isIntegral_spectralGen_nineHundredFortyOne_Q : IsIntegral ℚ (spectralGen 941) :=
  isIntegral_spectralGen_ℚ prime_nineHundredFortyOne

theorem isIntegral_and_degree_nineHundredFortyOne :
    IsIntegral ℤ (spectralGen 941) ∧
      (minpoly ℚ (spectralGen 941)).natDegree = 470 :=
  ⟨isIntegral_spectralGen_nineHundredFortyOne, degree_nineHundredFortyOne⟩

theorem nineHundredFortyOne_pack :
    IsIntegral ℤ (spectralGen 941) ∧
      (minpoly ℚ (spectralGen 941)).natDegree = 470 :=
  isIntegral_and_degree_nineHundredFortyOne

end Brockian.CosTraceNormNineHundredFortyOne
