/-
  Brockian/CosTraceNormThreeHundredFortySeven.lean — spectral generator at p = 347.

  [ℚ(2 cos 2π/347):ℚ] = 173 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredFortySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredFortySeven : Nat.Prime 347 := by decide

theorem threeHundredFortySeven_ne_two : (347 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredFortySeven : (minpoly ℚ (spectralGen 347)).natDegree = 173 :=
  real_subfield_degree prime_threeHundredFortySeven threeHundredFortySeven_ne_two

theorem isIntegral_spectralGen_threeHundredFortySeven : IsIntegral ℤ (spectralGen 347) :=
  isIntegral_spectralGen prime_threeHundredFortySeven

theorem isIntegral_spectralGen_threeHundredFortySeven_Q : IsIntegral ℚ (spectralGen 347) :=
  isIntegral_spectralGen_ℚ prime_threeHundredFortySeven

theorem isIntegral_and_degree_threeHundredFortySeven :
    IsIntegral ℤ (spectralGen 347) ∧
      (minpoly ℚ (spectralGen 347)).natDegree = 173 :=
  ⟨isIntegral_spectralGen_threeHundredFortySeven, degree_threeHundredFortySeven⟩

theorem threeHundredFortySeven_pack :
    IsIntegral ℤ (spectralGen 347) ∧
      (minpoly ℚ (spectralGen 347)).natDegree = 173 :=
  isIntegral_and_degree_threeHundredFortySeven

end Brockian.CosTraceNormThreeHundredFortySeven
