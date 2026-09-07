/-
  Brockian/CosTraceNormOneHundredNinetyThree.lean — spectral generator at p = 193.

  [ℚ(2 cos 2π/193):ℚ] = 96 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredNinetyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredNinetyThree : Nat.Prime 193 := by decide

theorem oneHundredNinetyThree_ne_two : (193 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredNinetyThree : (minpoly ℚ (spectralGen 193)).natDegree = 96 :=
  real_subfield_degree prime_oneHundredNinetyThree oneHundredNinetyThree_ne_two

theorem isIntegral_spectralGen_oneHundredNinetyThree : IsIntegral ℤ (spectralGen 193) :=
  isIntegral_spectralGen prime_oneHundredNinetyThree

theorem isIntegral_spectralGen_oneHundredNinetyThree_Q : IsIntegral ℚ (spectralGen 193) :=
  isIntegral_spectralGen_ℚ prime_oneHundredNinetyThree

theorem isIntegral_and_degree_oneHundredNinetyThree :
    IsIntegral ℤ (spectralGen 193) ∧
      (minpoly ℚ (spectralGen 193)).natDegree = 96 :=
  ⟨isIntegral_spectralGen_oneHundredNinetyThree, degree_oneHundredNinetyThree⟩

theorem oneHundredNinetyThree_pack :
    IsIntegral ℤ (spectralGen 193) ∧
      (minpoly ℚ (spectralGen 193)).natDegree = 96 :=
  isIntegral_and_degree_oneHundredNinetyThree

end Brockian.CosTraceNormOneHundredNinetyThree
