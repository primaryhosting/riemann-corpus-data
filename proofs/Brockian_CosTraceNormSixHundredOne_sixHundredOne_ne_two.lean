/-
  Brockian/CosTraceNormSixHundredOne.lean — spectral generator at p = 601.

  [ℚ(2 cos 2π/601):ℚ] = 300 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredOne : Nat.Prime 601 := by decide

theorem sixHundredOne_ne_two : (601 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredOne : (minpoly ℚ (spectralGen 601)).natDegree = 300 :=
  real_subfield_degree prime_sixHundredOne sixHundredOne_ne_two

theorem isIntegral_spectralGen_sixHundredOne : IsIntegral ℤ (spectralGen 601) :=
  isIntegral_spectralGen prime_sixHundredOne

theorem isIntegral_spectralGen_sixHundredOne_Q : IsIntegral ℚ (spectralGen 601) :=
  isIntegral_spectralGen_ℚ prime_sixHundredOne

theorem isIntegral_and_degree_sixHundredOne :
    IsIntegral ℤ (spectralGen 601) ∧
      (minpoly ℚ (spectralGen 601)).natDegree = 300 :=
  ⟨isIntegral_spectralGen_sixHundredOne, degree_sixHundredOne⟩

theorem sixHundredOne_pack :
    IsIntegral ℤ (spectralGen 601) ∧
      (minpoly ℚ (spectralGen 601)).natDegree = 300 :=
  isIntegral_and_degree_sixHundredOne

end Brockian.CosTraceNormSixHundredOne
