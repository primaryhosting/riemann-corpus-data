/-
  Brockian/CosTraceNormSevenHundredNine.lean — spectral generator at p = 709.

  [ℚ(2 cos 2π/709):ℚ] = 354 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredNine : Nat.Prime 709 := by decide

theorem sevenHundredNine_ne_two : (709 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredNine : (minpoly ℚ (spectralGen 709)).natDegree = 354 :=
  real_subfield_degree prime_sevenHundredNine sevenHundredNine_ne_two

theorem isIntegral_spectralGen_sevenHundredNine : IsIntegral ℤ (spectralGen 709) :=
  isIntegral_spectralGen prime_sevenHundredNine

theorem isIntegral_spectralGen_sevenHundredNine_Q : IsIntegral ℚ (spectralGen 709) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredNine

theorem isIntegral_and_degree_sevenHundredNine :
    IsIntegral ℤ (spectralGen 709) ∧
      (minpoly ℚ (spectralGen 709)).natDegree = 354 :=
  ⟨isIntegral_spectralGen_sevenHundredNine, degree_sevenHundredNine⟩

theorem sevenHundredNine_pack :
    IsIntegral ℤ (spectralGen 709) ∧
      (minpoly ℚ (spectralGen 709)).natDegree = 354 :=
  isIntegral_and_degree_sevenHundredNine

end Brockian.CosTraceNormSevenHundredNine
