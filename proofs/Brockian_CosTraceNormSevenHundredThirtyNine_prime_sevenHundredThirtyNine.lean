/-
  Brockian/CosTraceNormSevenHundredThirtyNine.lean — spectral generator at p = 739.

  [ℚ(2 cos 2π/739):ℚ] = 369 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredThirtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredThirtyNine : Nat.Prime 739 := by decide

theorem sevenHundredThirtyNine_ne_two : (739 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredThirtyNine : (minpoly ℚ (spectralGen 739)).natDegree = 369 :=
  real_subfield_degree prime_sevenHundredThirtyNine sevenHundredThirtyNine_ne_two

theorem isIntegral_spectralGen_sevenHundredThirtyNine : IsIntegral ℤ (spectralGen 739) :=
  isIntegral_spectralGen prime_sevenHundredThirtyNine

theorem isIntegral_spectralGen_sevenHundredThirtyNine_Q : IsIntegral ℚ (spectralGen 739) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredThirtyNine

theorem isIntegral_and_degree_sevenHundredThirtyNine :
    IsIntegral ℤ (spectralGen 739) ∧
      (minpoly ℚ (spectralGen 739)).natDegree = 369 :=
  ⟨isIntegral_spectralGen_sevenHundredThirtyNine, degree_sevenHundredThirtyNine⟩

theorem sevenHundredThirtyNine_pack :
    IsIntegral ℤ (spectralGen 739) ∧
      (minpoly ℚ (spectralGen 739)).natDegree = 369 :=
  isIntegral_and_degree_sevenHundredThirtyNine

end Brockian.CosTraceNormSevenHundredThirtyNine
