/-
  Brockian/CosTraceNormSevenHundredFortyThree.lean — spectral generator at p = 743.

  [ℚ(2 cos 2π/743):ℚ] = 371 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredFortyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredFortyThree : Nat.Prime 743 := by decide

theorem sevenHundredFortyThree_ne_two : (743 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredFortyThree : (minpoly ℚ (spectralGen 743)).natDegree = 371 :=
  real_subfield_degree prime_sevenHundredFortyThree sevenHundredFortyThree_ne_two

theorem isIntegral_spectralGen_sevenHundredFortyThree : IsIntegral ℤ (spectralGen 743) :=
  isIntegral_spectralGen prime_sevenHundredFortyThree

theorem isIntegral_spectralGen_sevenHundredFortyThree_Q : IsIntegral ℚ (spectralGen 743) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredFortyThree

theorem isIntegral_and_degree_sevenHundredFortyThree :
    IsIntegral ℤ (spectralGen 743) ∧
      (minpoly ℚ (spectralGen 743)).natDegree = 371 :=
  ⟨isIntegral_spectralGen_sevenHundredFortyThree, degree_sevenHundredFortyThree⟩

theorem sevenHundredFortyThree_pack :
    IsIntegral ℤ (spectralGen 743) ∧
      (minpoly ℚ (spectralGen 743)).natDegree = 371 :=
  isIntegral_and_degree_sevenHundredFortyThree

end Brockian.CosTraceNormSevenHundredFortyThree
