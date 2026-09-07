/-
  Brockian/CosTraceNormFourHundredFortyNine.lean — spectral generator at p = 449.

  [ℚ(2 cos 2π/449):ℚ] = 224 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredFortyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredFortyNine : Nat.Prime 449 := by decide

theorem fourHundredFortyNine_ne_two : (449 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredFortyNine : (minpoly ℚ (spectralGen 449)).natDegree = 224 :=
  real_subfield_degree prime_fourHundredFortyNine fourHundredFortyNine_ne_two

theorem isIntegral_spectralGen_fourHundredFortyNine : IsIntegral ℤ (spectralGen 449) :=
  isIntegral_spectralGen prime_fourHundredFortyNine

theorem isIntegral_spectralGen_fourHundredFortyNine_Q : IsIntegral ℚ (spectralGen 449) :=
  isIntegral_spectralGen_ℚ prime_fourHundredFortyNine

theorem isIntegral_and_degree_fourHundredFortyNine :
    IsIntegral ℤ (spectralGen 449) ∧
      (minpoly ℚ (spectralGen 449)).natDegree = 224 :=
  ⟨isIntegral_spectralGen_fourHundredFortyNine, degree_fourHundredFortyNine⟩

theorem fourHundredFortyNine_pack :
    IsIntegral ℤ (spectralGen 449) ∧
      (minpoly ℚ (spectralGen 449)).natDegree = 224 :=
  isIntegral_and_degree_fourHundredFortyNine

end Brockian.CosTraceNormFourHundredFortyNine
