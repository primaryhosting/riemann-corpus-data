/-
  Brockian/CosTraceNormTwoHundredTwentySeven.lean — spectral generator at p = 227.

  [ℚ(2 cos 2π/227):ℚ] = 113 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredTwentySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredTwentySeven : Nat.Prime 227 := by decide

theorem twoHundredTwentySeven_ne_two : (227 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredTwentySeven : (minpoly ℚ (spectralGen 227)).natDegree = 113 :=
  real_subfield_degree prime_twoHundredTwentySeven twoHundredTwentySeven_ne_two

theorem isIntegral_spectralGen_twoHundredTwentySeven : IsIntegral ℤ (spectralGen 227) :=
  isIntegral_spectralGen prime_twoHundredTwentySeven

theorem isIntegral_spectralGen_twoHundredTwentySeven_Q : IsIntegral ℚ (spectralGen 227) :=
  isIntegral_spectralGen_ℚ prime_twoHundredTwentySeven

theorem isIntegral_and_degree_twoHundredTwentySeven :
    IsIntegral ℤ (spectralGen 227) ∧
      (minpoly ℚ (spectralGen 227)).natDegree = 113 :=
  ⟨isIntegral_spectralGen_twoHundredTwentySeven, degree_twoHundredTwentySeven⟩

theorem twoHundredTwentySeven_pack :
    IsIntegral ℤ (spectralGen 227) ∧
      (minpoly ℚ (spectralGen 227)).natDegree = 113 :=
  isIntegral_and_degree_twoHundredTwentySeven

end Brockian.CosTraceNormTwoHundredTwentySeven
