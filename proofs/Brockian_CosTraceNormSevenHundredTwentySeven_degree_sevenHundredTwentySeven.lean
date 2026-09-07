/-
  Brockian/CosTraceNormSevenHundredTwentySeven.lean — spectral generator at p = 727.

  [ℚ(2 cos 2π/727):ℚ] = 363 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredTwentySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredTwentySeven : Nat.Prime 727 := by decide

theorem sevenHundredTwentySeven_ne_two : (727 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredTwentySeven : (minpoly ℚ (spectralGen 727)).natDegree = 363 :=
  real_subfield_degree prime_sevenHundredTwentySeven sevenHundredTwentySeven_ne_two

theorem isIntegral_spectralGen_sevenHundredTwentySeven : IsIntegral ℤ (spectralGen 727) :=
  isIntegral_spectralGen prime_sevenHundredTwentySeven

theorem isIntegral_spectralGen_sevenHundredTwentySeven_Q : IsIntegral ℚ (spectralGen 727) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredTwentySeven

theorem isIntegral_and_degree_sevenHundredTwentySeven :
    IsIntegral ℤ (spectralGen 727) ∧
      (minpoly ℚ (spectralGen 727)).natDegree = 363 :=
  ⟨isIntegral_spectralGen_sevenHundredTwentySeven, degree_sevenHundredTwentySeven⟩

theorem sevenHundredTwentySeven_pack :
    IsIntegral ℤ (spectralGen 727) ∧
      (minpoly ℚ (spectralGen 727)).natDegree = 363 :=
  isIntegral_and_degree_sevenHundredTwentySeven

end Brockian.CosTraceNormSevenHundredTwentySeven
