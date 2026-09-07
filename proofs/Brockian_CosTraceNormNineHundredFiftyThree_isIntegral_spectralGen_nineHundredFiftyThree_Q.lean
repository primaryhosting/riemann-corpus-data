/-
  Brockian/CosTraceNormNineHundredFiftyThree.lean — spectral generator at p = 953.

  [ℚ(2 cos 2π/953):ℚ] = 476 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredFiftyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredFiftyThree : Nat.Prime 953 := by decide

theorem nineHundredFiftyThree_ne_two : (953 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredFiftyThree : (minpoly ℚ (spectralGen 953)).natDegree = 476 :=
  real_subfield_degree prime_nineHundredFiftyThree nineHundredFiftyThree_ne_two

theorem isIntegral_spectralGen_nineHundredFiftyThree : IsIntegral ℤ (spectralGen 953) :=
  isIntegral_spectralGen prime_nineHundredFiftyThree

theorem isIntegral_spectralGen_nineHundredFiftyThree_Q : IsIntegral ℚ (spectralGen 953) :=
  isIntegral_spectralGen_ℚ prime_nineHundredFiftyThree

theorem isIntegral_and_degree_nineHundredFiftyThree :
    IsIntegral ℤ (spectralGen 953) ∧
      (minpoly ℚ (spectralGen 953)).natDegree = 476 :=
  ⟨isIntegral_spectralGen_nineHundredFiftyThree, degree_nineHundredFiftyThree⟩

theorem nineHundredFiftyThree_pack :
    IsIntegral ℤ (spectralGen 953) ∧
      (minpoly ℚ (spectralGen 953)).natDegree = 476 :=
  isIntegral_and_degree_nineHundredFiftyThree

end Brockian.CosTraceNormNineHundredFiftyThree
