/-
  Brockian/CosTraceNormFiveHundredEightySeven.lean — spectral generator at p = 587.

  [ℚ(2 cos 2π/587):ℚ] = 293 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredEightySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredEightySeven : Nat.Prime 587 := by decide

theorem fiveHundredEightySeven_ne_two : (587 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredEightySeven : (minpoly ℚ (spectralGen 587)).natDegree = 293 :=
  real_subfield_degree prime_fiveHundredEightySeven fiveHundredEightySeven_ne_two

theorem isIntegral_spectralGen_fiveHundredEightySeven : IsIntegral ℤ (spectralGen 587) :=
  isIntegral_spectralGen prime_fiveHundredEightySeven

theorem isIntegral_spectralGen_fiveHundredEightySeven_Q : IsIntegral ℚ (spectralGen 587) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredEightySeven

theorem isIntegral_and_degree_fiveHundredEightySeven :
    IsIntegral ℤ (spectralGen 587) ∧
      (minpoly ℚ (spectralGen 587)).natDegree = 293 :=
  ⟨isIntegral_spectralGen_fiveHundredEightySeven, degree_fiveHundredEightySeven⟩

theorem fiveHundredEightySeven_pack :
    IsIntegral ℤ (spectralGen 587) ∧
      (minpoly ℚ (spectralGen 587)).natDegree = 293 :=
  isIntegral_and_degree_fiveHundredEightySeven

end Brockian.CosTraceNormFiveHundredEightySeven
