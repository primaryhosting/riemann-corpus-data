/-
  Brockian/CosTraceNormSevenHundredThirtyThree.lean — spectral generator at p = 733.

  [ℚ(2 cos 2π/733):ℚ] = 366 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredThirtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredThirtyThree : Nat.Prime 733 := by decide

theorem sevenHundredThirtyThree_ne_two : (733 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredThirtyThree : (minpoly ℚ (spectralGen 733)).natDegree = 366 :=
  real_subfield_degree prime_sevenHundredThirtyThree sevenHundredThirtyThree_ne_two

theorem isIntegral_spectralGen_sevenHundredThirtyThree : IsIntegral ℤ (spectralGen 733) :=
  isIntegral_spectralGen prime_sevenHundredThirtyThree

theorem isIntegral_spectralGen_sevenHundredThirtyThree_Q : IsIntegral ℚ (spectralGen 733) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredThirtyThree

theorem isIntegral_and_degree_sevenHundredThirtyThree :
    IsIntegral ℤ (spectralGen 733) ∧
      (minpoly ℚ (spectralGen 733)).natDegree = 366 :=
  ⟨isIntegral_spectralGen_sevenHundredThirtyThree, degree_sevenHundredThirtyThree⟩

theorem sevenHundredThirtyThree_pack :
    IsIntegral ℤ (spectralGen 733) ∧
      (minpoly ℚ (spectralGen 733)).natDegree = 366 :=
  isIntegral_and_degree_sevenHundredThirtyThree

end Brockian.CosTraceNormSevenHundredThirtyThree
