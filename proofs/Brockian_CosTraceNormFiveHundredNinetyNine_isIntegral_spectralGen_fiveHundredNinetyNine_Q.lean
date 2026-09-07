/-
  Brockian/CosTraceNormFiveHundredNinetyNine.lean — spectral generator at p = 599.

  [ℚ(2 cos 2π/599):ℚ] = 299 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredNinetyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredNinetyNine : Nat.Prime 599 := by decide

theorem fiveHundredNinetyNine_ne_two : (599 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredNinetyNine : (minpoly ℚ (spectralGen 599)).natDegree = 299 :=
  real_subfield_degree prime_fiveHundredNinetyNine fiveHundredNinetyNine_ne_two

theorem isIntegral_spectralGen_fiveHundredNinetyNine : IsIntegral ℤ (spectralGen 599) :=
  isIntegral_spectralGen prime_fiveHundredNinetyNine

theorem isIntegral_spectralGen_fiveHundredNinetyNine_Q : IsIntegral ℚ (spectralGen 599) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredNinetyNine

theorem isIntegral_and_degree_fiveHundredNinetyNine :
    IsIntegral ℤ (spectralGen 599) ∧
      (minpoly ℚ (spectralGen 599)).natDegree = 299 :=
  ⟨isIntegral_spectralGen_fiveHundredNinetyNine, degree_fiveHundredNinetyNine⟩

theorem fiveHundredNinetyNine_pack :
    IsIntegral ℤ (spectralGen 599) ∧
      (minpoly ℚ (spectralGen 599)).natDegree = 299 :=
  isIntegral_and_degree_fiveHundredNinetyNine

end Brockian.CosTraceNormFiveHundredNinetyNine
