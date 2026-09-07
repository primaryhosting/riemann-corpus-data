/-
  Brockian/CosTraceNormSixHundredFiftyNine.lean — spectral generator at p = 659.

  [ℚ(2 cos 2π/659):ℚ] = 329 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredFiftyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredFiftyNine : Nat.Prime 659 := by decide

theorem sixHundredFiftyNine_ne_two : (659 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredFiftyNine : (minpoly ℚ (spectralGen 659)).natDegree = 329 :=
  real_subfield_degree prime_sixHundredFiftyNine sixHundredFiftyNine_ne_two

theorem isIntegral_spectralGen_sixHundredFiftyNine : IsIntegral ℤ (spectralGen 659) :=
  isIntegral_spectralGen prime_sixHundredFiftyNine

theorem isIntegral_spectralGen_sixHundredFiftyNine_Q : IsIntegral ℚ (spectralGen 659) :=
  isIntegral_spectralGen_ℚ prime_sixHundredFiftyNine

theorem isIntegral_and_degree_sixHundredFiftyNine :
    IsIntegral ℤ (spectralGen 659) ∧
      (minpoly ℚ (spectralGen 659)).natDegree = 329 :=
  ⟨isIntegral_spectralGen_sixHundredFiftyNine, degree_sixHundredFiftyNine⟩

theorem sixHundredFiftyNine_pack :
    IsIntegral ℤ (spectralGen 659) ∧
      (minpoly ℚ (spectralGen 659)).natDegree = 329 :=
  isIntegral_and_degree_sixHundredFiftyNine

end Brockian.CosTraceNormSixHundredFiftyNine
