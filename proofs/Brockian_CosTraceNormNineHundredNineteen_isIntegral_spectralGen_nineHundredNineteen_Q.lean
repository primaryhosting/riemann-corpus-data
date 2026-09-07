/-
  Brockian/CosTraceNormNineHundredNineteen.lean — spectral generator at p = 919.

  [ℚ(2 cos 2π/919):ℚ] = 459 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredNineteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredNineteen : Nat.Prime 919 := by decide

theorem nineHundredNineteen_ne_two : (919 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredNineteen : (minpoly ℚ (spectralGen 919)).natDegree = 459 :=
  real_subfield_degree prime_nineHundredNineteen nineHundredNineteen_ne_two

theorem isIntegral_spectralGen_nineHundredNineteen : IsIntegral ℤ (spectralGen 919) :=
  isIntegral_spectralGen prime_nineHundredNineteen

theorem isIntegral_spectralGen_nineHundredNineteen_Q : IsIntegral ℚ (spectralGen 919) :=
  isIntegral_spectralGen_ℚ prime_nineHundredNineteen

theorem isIntegral_and_degree_nineHundredNineteen :
    IsIntegral ℤ (spectralGen 919) ∧
      (minpoly ℚ (spectralGen 919)).natDegree = 459 :=
  ⟨isIntegral_spectralGen_nineHundredNineteen, degree_nineHundredNineteen⟩

theorem nineHundredNineteen_pack :
    IsIntegral ℤ (spectralGen 919) ∧
      (minpoly ℚ (spectralGen 919)).natDegree = 459 :=
  isIntegral_and_degree_nineHundredNineteen

end Brockian.CosTraceNormNineHundredNineteen
