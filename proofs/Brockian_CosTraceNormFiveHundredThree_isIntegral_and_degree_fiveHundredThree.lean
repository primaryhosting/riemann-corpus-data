/-
  Brockian/CosTraceNormFiveHundredThree.lean — spectral generator at p = 503.

  [ℚ(2 cos 2π/503):ℚ] = 251 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredThree : Nat.Prime 503 := by decide

theorem fiveHundredThree_ne_two : (503 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredThree : (minpoly ℚ (spectralGen 503)).natDegree = 251 :=
  real_subfield_degree prime_fiveHundredThree fiveHundredThree_ne_two

theorem isIntegral_spectralGen_fiveHundredThree : IsIntegral ℤ (spectralGen 503) :=
  isIntegral_spectralGen prime_fiveHundredThree

theorem isIntegral_spectralGen_fiveHundredThree_Q : IsIntegral ℚ (spectralGen 503) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredThree

theorem isIntegral_and_degree_fiveHundredThree :
    IsIntegral ℤ (spectralGen 503) ∧
      (minpoly ℚ (spectralGen 503)).natDegree = 251 :=
  ⟨isIntegral_spectralGen_fiveHundredThree, degree_fiveHundredThree⟩

theorem fiveHundredThree_pack :
    IsIntegral ℤ (spectralGen 503) ∧
      (minpoly ℚ (spectralGen 503)).natDegree = 251 :=
  isIntegral_and_degree_fiveHundredThree

end Brockian.CosTraceNormFiveHundredThree
