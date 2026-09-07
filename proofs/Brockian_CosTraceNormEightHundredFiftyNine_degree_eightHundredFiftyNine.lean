/-
  Brockian/CosTraceNormEightHundredFiftyNine.lean — spectral generator at p = 859.

  [ℚ(2 cos 2π/859):ℚ] = 429 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredFiftyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredFiftyNine : Nat.Prime 859 := by decide

theorem eightHundredFiftyNine_ne_two : (859 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredFiftyNine : (minpoly ℚ (spectralGen 859)).natDegree = 429 :=
  real_subfield_degree prime_eightHundredFiftyNine eightHundredFiftyNine_ne_two

theorem isIntegral_spectralGen_eightHundredFiftyNine : IsIntegral ℤ (spectralGen 859) :=
  isIntegral_spectralGen prime_eightHundredFiftyNine

theorem isIntegral_spectralGen_eightHundredFiftyNine_Q : IsIntegral ℚ (spectralGen 859) :=
  isIntegral_spectralGen_ℚ prime_eightHundredFiftyNine

theorem isIntegral_and_degree_eightHundredFiftyNine :
    IsIntegral ℤ (spectralGen 859) ∧
      (minpoly ℚ (spectralGen 859)).natDegree = 429 :=
  ⟨isIntegral_spectralGen_eightHundredFiftyNine, degree_eightHundredFiftyNine⟩

theorem eightHundredFiftyNine_pack :
    IsIntegral ℤ (spectralGen 859) ∧
      (minpoly ℚ (spectralGen 859)).natDegree = 429 :=
  isIntegral_and_degree_eightHundredFiftyNine

end Brockian.CosTraceNormEightHundredFiftyNine
