/-
  Brockian/CosTraceNormFiveHundredNinetyThree.lean — spectral generator at p = 593.

  [ℚ(2 cos 2π/593):ℚ] = 296 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredNinetyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredNinetyThree : Nat.Prime 593 := by decide

theorem fiveHundredNinetyThree_ne_two : (593 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredNinetyThree : (minpoly ℚ (spectralGen 593)).natDegree = 296 :=
  real_subfield_degree prime_fiveHundredNinetyThree fiveHundredNinetyThree_ne_two

theorem isIntegral_spectralGen_fiveHundredNinetyThree : IsIntegral ℤ (spectralGen 593) :=
  isIntegral_spectralGen prime_fiveHundredNinetyThree

theorem isIntegral_spectralGen_fiveHundredNinetyThree_Q : IsIntegral ℚ (spectralGen 593) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredNinetyThree

theorem isIntegral_and_degree_fiveHundredNinetyThree :
    IsIntegral ℤ (spectralGen 593) ∧
      (minpoly ℚ (spectralGen 593)).natDegree = 296 :=
  ⟨isIntegral_spectralGen_fiveHundredNinetyThree, degree_fiveHundredNinetyThree⟩

theorem fiveHundredNinetyThree_pack :
    IsIntegral ℤ (spectralGen 593) ∧
      (minpoly ℚ (spectralGen 593)).natDegree = 296 :=
  isIntegral_and_degree_fiveHundredNinetyThree

end Brockian.CosTraceNormFiveHundredNinetyThree
