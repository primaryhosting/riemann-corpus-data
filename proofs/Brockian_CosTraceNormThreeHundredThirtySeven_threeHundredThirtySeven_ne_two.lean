/-
  Brockian/CosTraceNormThreeHundredThirtySeven.lean — spectral generator at p = 337.

  [ℚ(2 cos 2π/337):ℚ] = 168 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredThirtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredThirtySeven : Nat.Prime 337 := by decide

theorem threeHundredThirtySeven_ne_two : (337 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredThirtySeven : (minpoly ℚ (spectralGen 337)).natDegree = 168 :=
  real_subfield_degree prime_threeHundredThirtySeven threeHundredThirtySeven_ne_two

theorem isIntegral_spectralGen_threeHundredThirtySeven : IsIntegral ℤ (spectralGen 337) :=
  isIntegral_spectralGen prime_threeHundredThirtySeven

theorem isIntegral_spectralGen_threeHundredThirtySeven_Q : IsIntegral ℚ (spectralGen 337) :=
  isIntegral_spectralGen_ℚ prime_threeHundredThirtySeven

theorem isIntegral_and_degree_threeHundredThirtySeven :
    IsIntegral ℤ (spectralGen 337) ∧
      (minpoly ℚ (spectralGen 337)).natDegree = 168 :=
  ⟨isIntegral_spectralGen_threeHundredThirtySeven, degree_threeHundredThirtySeven⟩

theorem threeHundredThirtySeven_pack :
    IsIntegral ℤ (spectralGen 337) ∧
      (minpoly ℚ (spectralGen 337)).natDegree = 168 :=
  isIntegral_and_degree_threeHundredThirtySeven

end Brockian.CosTraceNormThreeHundredThirtySeven
