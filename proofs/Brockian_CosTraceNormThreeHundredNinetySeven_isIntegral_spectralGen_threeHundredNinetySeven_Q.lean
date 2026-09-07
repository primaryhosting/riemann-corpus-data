/-
  Brockian/CosTraceNormThreeHundredNinetySeven.lean — spectral generator at p = 397.

  [ℚ(2 cos 2π/397):ℚ] = 198 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredNinetySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredNinetySeven : Nat.Prime 397 := by decide

theorem threeHundredNinetySeven_ne_two : (397 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredNinetySeven : (minpoly ℚ (spectralGen 397)).natDegree = 198 :=
  real_subfield_degree prime_threeHundredNinetySeven threeHundredNinetySeven_ne_two

theorem isIntegral_spectralGen_threeHundredNinetySeven : IsIntegral ℤ (spectralGen 397) :=
  isIntegral_spectralGen prime_threeHundredNinetySeven

theorem isIntegral_spectralGen_threeHundredNinetySeven_Q : IsIntegral ℚ (spectralGen 397) :=
  isIntegral_spectralGen_ℚ prime_threeHundredNinetySeven

theorem isIntegral_and_degree_threeHundredNinetySeven :
    IsIntegral ℤ (spectralGen 397) ∧
      (minpoly ℚ (spectralGen 397)).natDegree = 198 :=
  ⟨isIntegral_spectralGen_threeHundredNinetySeven, degree_threeHundredNinetySeven⟩

theorem threeHundredNinetySeven_pack :
    IsIntegral ℤ (spectralGen 397) ∧
      (minpoly ℚ (spectralGen 397)).natDegree = 198 :=
  isIntegral_and_degree_threeHundredNinetySeven

end Brockian.CosTraceNormThreeHundredNinetySeven
