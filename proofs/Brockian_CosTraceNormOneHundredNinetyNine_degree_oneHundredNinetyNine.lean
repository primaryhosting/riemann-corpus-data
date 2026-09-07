/-
  Brockian/CosTraceNormOneHundredNinetyNine.lean — spectral generator at p = 199.

  [ℚ(2 cos 2π/199):ℚ] = 99 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredNinetyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredNinetyNine : Nat.Prime 199 := by decide

theorem oneHundredNinetyNine_ne_two : (199 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredNinetyNine : (minpoly ℚ (spectralGen 199)).natDegree = 99 :=
  real_subfield_degree prime_oneHundredNinetyNine oneHundredNinetyNine_ne_two

theorem isIntegral_spectralGen_oneHundredNinetyNine : IsIntegral ℤ (spectralGen 199) :=
  isIntegral_spectralGen prime_oneHundredNinetyNine

theorem isIntegral_spectralGen_oneHundredNinetyNine_Q : IsIntegral ℚ (spectralGen 199) :=
  isIntegral_spectralGen_ℚ prime_oneHundredNinetyNine

theorem isIntegral_and_degree_oneHundredNinetyNine :
    IsIntegral ℤ (spectralGen 199) ∧
      (minpoly ℚ (spectralGen 199)).natDegree = 99 :=
  ⟨isIntegral_spectralGen_oneHundredNinetyNine, degree_oneHundredNinetyNine⟩

theorem oneHundredNinetyNine_pack :
    IsIntegral ℤ (spectralGen 199) ∧
      (minpoly ℚ (spectralGen 199)).natDegree = 99 :=
  isIntegral_and_degree_oneHundredNinetyNine

end Brockian.CosTraceNormOneHundredNinetyNine
