/-
  Brockian/CosTraceNormOneHundredNinetyOne.lean — spectral generator at p = 191.

  [ℚ(2 cos 2π/191):ℚ] = 95 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredNinetyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredNinetyOne : Nat.Prime 191 := by decide

theorem oneHundredNinetyOne_ne_two : (191 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredNinetyOne : (minpoly ℚ (spectralGen 191)).natDegree = 95 :=
  real_subfield_degree prime_oneHundredNinetyOne oneHundredNinetyOne_ne_two

theorem isIntegral_spectralGen_oneHundredNinetyOne : IsIntegral ℤ (spectralGen 191) :=
  isIntegral_spectralGen prime_oneHundredNinetyOne

theorem isIntegral_spectralGen_oneHundredNinetyOne_Q : IsIntegral ℚ (spectralGen 191) :=
  isIntegral_spectralGen_ℚ prime_oneHundredNinetyOne

theorem isIntegral_and_degree_oneHundredNinetyOne :
    IsIntegral ℤ (spectralGen 191) ∧
      (minpoly ℚ (spectralGen 191)).natDegree = 95 :=
  ⟨isIntegral_spectralGen_oneHundredNinetyOne, degree_oneHundredNinetyOne⟩

theorem oneHundredNinetyOne_pack :
    IsIntegral ℤ (spectralGen 191) ∧
      (minpoly ℚ (spectralGen 191)).natDegree = 95 :=
  isIntegral_and_degree_oneHundredNinetyOne

end Brockian.CosTraceNormOneHundredNinetyOne
