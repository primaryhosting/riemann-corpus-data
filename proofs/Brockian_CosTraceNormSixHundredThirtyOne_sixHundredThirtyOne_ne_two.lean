/-
  Brockian/CosTraceNormSixHundredThirtyOne.lean — spectral generator at p = 631.

  [ℚ(2 cos 2π/631):ℚ] = 315 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredThirtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredThirtyOne : Nat.Prime 631 := by decide

theorem sixHundredThirtyOne_ne_two : (631 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredThirtyOne : (minpoly ℚ (spectralGen 631)).natDegree = 315 :=
  real_subfield_degree prime_sixHundredThirtyOne sixHundredThirtyOne_ne_two

theorem isIntegral_spectralGen_sixHundredThirtyOne : IsIntegral ℤ (spectralGen 631) :=
  isIntegral_spectralGen prime_sixHundredThirtyOne

theorem isIntegral_spectralGen_sixHundredThirtyOne_Q : IsIntegral ℚ (spectralGen 631) :=
  isIntegral_spectralGen_ℚ prime_sixHundredThirtyOne

theorem isIntegral_and_degree_sixHundredThirtyOne :
    IsIntegral ℤ (spectralGen 631) ∧
      (minpoly ℚ (spectralGen 631)).natDegree = 315 :=
  ⟨isIntegral_spectralGen_sixHundredThirtyOne, degree_sixHundredThirtyOne⟩

theorem sixHundredThirtyOne_pack :
    IsIntegral ℤ (spectralGen 631) ∧
      (minpoly ℚ (spectralGen 631)).natDegree = 315 :=
  isIntegral_and_degree_sixHundredThirtyOne

end Brockian.CosTraceNormSixHundredThirtyOne
