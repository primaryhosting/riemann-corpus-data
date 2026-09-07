/-
  Brockian/CosTraceNormFourHundredNineteen.lean — spectral generator at p = 419.

  [ℚ(2 cos 2π/419):ℚ] = 209 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredNineteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredNineteen : Nat.Prime 419 := by decide

theorem fourHundredNineteen_ne_two : (419 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredNineteen : (minpoly ℚ (spectralGen 419)).natDegree = 209 :=
  real_subfield_degree prime_fourHundredNineteen fourHundredNineteen_ne_two

theorem isIntegral_spectralGen_fourHundredNineteen : IsIntegral ℤ (spectralGen 419) :=
  isIntegral_spectralGen prime_fourHundredNineteen

theorem isIntegral_spectralGen_fourHundredNineteen_Q : IsIntegral ℚ (spectralGen 419) :=
  isIntegral_spectralGen_ℚ prime_fourHundredNineteen

theorem isIntegral_and_degree_fourHundredNineteen :
    IsIntegral ℤ (spectralGen 419) ∧
      (minpoly ℚ (spectralGen 419)).natDegree = 209 :=
  ⟨isIntegral_spectralGen_fourHundredNineteen, degree_fourHundredNineteen⟩

theorem fourHundredNineteen_pack :
    IsIntegral ℤ (spectralGen 419) ∧
      (minpoly ℚ (spectralGen 419)).natDegree = 209 :=
  isIntegral_and_degree_fourHundredNineteen

end Brockian.CosTraceNormFourHundredNineteen
