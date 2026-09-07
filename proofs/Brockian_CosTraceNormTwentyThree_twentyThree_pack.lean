/-
  Brockian/CosTraceNormTwentyThree.lean — spectral generator at p = 23.

  [ℚ(2 cos 2π/23):ℚ] = 11 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormTwentyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twentyThree : Nat.Prime 23 := by decide

theorem twentyThree_ne_two : (23 : ℕ) ≠ 2 := by decide

theorem degree_twentyThree : (minpoly ℚ (spectralGen 23)).natDegree = 11 :=
  real_subfield_degree prime_twentyThree twentyThree_ne_two

theorem isIntegral_spectralGen_twentyThree : IsIntegral ℤ (spectralGen 23) :=
  isIntegral_spectralGen prime_twentyThree

theorem isIntegral_spectralGen_twentyThree_Q : IsIntegral ℚ (spectralGen 23) :=
  isIntegral_spectralGen_ℚ prime_twentyThree

theorem isIntegral_and_degree_twentyThree :
    IsIntegral ℤ (spectralGen 23) ∧
      (minpoly ℚ (spectralGen 23)).natDegree = 11 :=
  ⟨isIntegral_spectralGen_twentyThree, degree_twentyThree⟩

theorem twentyThree_pack :
    IsIntegral ℤ (spectralGen 23) ∧
      (minpoly ℚ (spectralGen 23)).natDegree = 11 :=
  isIntegral_and_degree_twentyThree

end Brockian.CosTraceNormTwentyThree
