/-
  Brockian/CosTraceNormTwoHundredFiftyOne.lean — spectral generator at p = 251.

  [ℚ(2 cos 2π/251):ℚ] = 125 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredFiftyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredFiftyOne : Nat.Prime 251 := by decide

theorem twoHundredFiftyOne_ne_two : (251 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredFiftyOne : (minpoly ℚ (spectralGen 251)).natDegree = 125 :=
  real_subfield_degree prime_twoHundredFiftyOne twoHundredFiftyOne_ne_two

theorem isIntegral_spectralGen_twoHundredFiftyOne : IsIntegral ℤ (spectralGen 251) :=
  isIntegral_spectralGen prime_twoHundredFiftyOne

theorem isIntegral_spectralGen_twoHundredFiftyOne_Q : IsIntegral ℚ (spectralGen 251) :=
  isIntegral_spectralGen_ℚ prime_twoHundredFiftyOne

theorem isIntegral_and_degree_twoHundredFiftyOne :
    IsIntegral ℤ (spectralGen 251) ∧
      (minpoly ℚ (spectralGen 251)).natDegree = 125 :=
  ⟨isIntegral_spectralGen_twoHundredFiftyOne, degree_twoHundredFiftyOne⟩

theorem twoHundredFiftyOne_pack :
    IsIntegral ℤ (spectralGen 251) ∧
      (minpoly ℚ (spectralGen 251)).natDegree = 125 :=
  isIntegral_and_degree_twoHundredFiftyOne

end Brockian.CosTraceNormTwoHundredFiftyOne
