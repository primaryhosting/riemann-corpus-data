/-
  Brockian/CosTraceNormEightHundredTwentySeven.lean — spectral generator at p = 827.

  [ℚ(2 cos 2π/827):ℚ] = 413 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredTwentySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredTwentySeven : Nat.Prime 827 := by decide

theorem eightHundredTwentySeven_ne_two : (827 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredTwentySeven : (minpoly ℚ (spectralGen 827)).natDegree = 413 :=
  real_subfield_degree prime_eightHundredTwentySeven eightHundredTwentySeven_ne_two

theorem isIntegral_spectralGen_eightHundredTwentySeven : IsIntegral ℤ (spectralGen 827) :=
  isIntegral_spectralGen prime_eightHundredTwentySeven

theorem isIntegral_spectralGen_eightHundredTwentySeven_Q : IsIntegral ℚ (spectralGen 827) :=
  isIntegral_spectralGen_ℚ prime_eightHundredTwentySeven

theorem isIntegral_and_degree_eightHundredTwentySeven :
    IsIntegral ℤ (spectralGen 827) ∧
      (minpoly ℚ (spectralGen 827)).natDegree = 413 :=
  ⟨isIntegral_spectralGen_eightHundredTwentySeven, degree_eightHundredTwentySeven⟩

theorem eightHundredTwentySeven_pack :
    IsIntegral ℤ (spectralGen 827) ∧
      (minpoly ℚ (spectralGen 827)).natDegree = 413 :=
  isIntegral_and_degree_eightHundredTwentySeven

end Brockian.CosTraceNormEightHundredTwentySeven
