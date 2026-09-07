/-
  Brockian/CosTraceNormFourHundredEightySeven.lean — spectral generator at p = 487.

  [ℚ(2 cos 2π/487):ℚ] = 243 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredEightySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredEightySeven : Nat.Prime 487 := by decide

theorem fourHundredEightySeven_ne_two : (487 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredEightySeven : (minpoly ℚ (spectralGen 487)).natDegree = 243 :=
  real_subfield_degree prime_fourHundredEightySeven fourHundredEightySeven_ne_two

theorem isIntegral_spectralGen_fourHundredEightySeven : IsIntegral ℤ (spectralGen 487) :=
  isIntegral_spectralGen prime_fourHundredEightySeven

theorem isIntegral_spectralGen_fourHundredEightySeven_Q : IsIntegral ℚ (spectralGen 487) :=
  isIntegral_spectralGen_ℚ prime_fourHundredEightySeven

theorem isIntegral_and_degree_fourHundredEightySeven :
    IsIntegral ℤ (spectralGen 487) ∧
      (minpoly ℚ (spectralGen 487)).natDegree = 243 :=
  ⟨isIntegral_spectralGen_fourHundredEightySeven, degree_fourHundredEightySeven⟩

theorem fourHundredEightySeven_pack :
    IsIntegral ℤ (spectralGen 487) ∧
      (minpoly ℚ (spectralGen 487)).natDegree = 243 :=
  isIntegral_and_degree_fourHundredEightySeven

end Brockian.CosTraceNormFourHundredEightySeven
