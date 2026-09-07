/-
  Brockian/CosTraceNormSixHundredFortyOne.lean — spectral generator at p = 641.

  [ℚ(2 cos 2π/641):ℚ] = 320 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredFortyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredFortyOne : Nat.Prime 641 := by decide

theorem sixHundredFortyOne_ne_two : (641 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredFortyOne : (minpoly ℚ (spectralGen 641)).natDegree = 320 :=
  real_subfield_degree prime_sixHundredFortyOne sixHundredFortyOne_ne_two

theorem isIntegral_spectralGen_sixHundredFortyOne : IsIntegral ℤ (spectralGen 641) :=
  isIntegral_spectralGen prime_sixHundredFortyOne

theorem isIntegral_spectralGen_sixHundredFortyOne_Q : IsIntegral ℚ (spectralGen 641) :=
  isIntegral_spectralGen_ℚ prime_sixHundredFortyOne

theorem isIntegral_and_degree_sixHundredFortyOne :
    IsIntegral ℤ (spectralGen 641) ∧
      (minpoly ℚ (spectralGen 641)).natDegree = 320 :=
  ⟨isIntegral_spectralGen_sixHundredFortyOne, degree_sixHundredFortyOne⟩

theorem sixHundredFortyOne_pack :
    IsIntegral ℤ (spectralGen 641) ∧
      (minpoly ℚ (spectralGen 641)).natDegree = 320 :=
  isIntegral_and_degree_sixHundredFortyOne

end Brockian.CosTraceNormSixHundredFortyOne
