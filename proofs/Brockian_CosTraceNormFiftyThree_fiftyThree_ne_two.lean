/-
  Brockian/CosTraceNormFiftyThree.lean — spectral generator at p = 53.

  [ℚ(2 cos 2π/53):ℚ] = 26 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormFiftyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiftyThree : Nat.Prime 53 := by decide

theorem fiftyThree_ne_two : (53 : ℕ) ≠ 2 := by decide

theorem degree_fiftyThree : (minpoly ℚ (spectralGen 53)).natDegree = 26 :=
  real_subfield_degree prime_fiftyThree fiftyThree_ne_two

theorem isIntegral_spectralGen_fiftyThree : IsIntegral ℤ (spectralGen 53) :=
  isIntegral_spectralGen prime_fiftyThree

theorem isIntegral_spectralGen_fiftyThree_Q : IsIntegral ℚ (spectralGen 53) :=
  isIntegral_spectralGen_ℚ prime_fiftyThree

theorem isIntegral_and_degree_fiftyThree :
    IsIntegral ℤ (spectralGen 53) ∧
      (minpoly ℚ (spectralGen 53)).natDegree = 26 :=
  ⟨isIntegral_spectralGen_fiftyThree, degree_fiftyThree⟩

theorem fiftyThree_pack :
    IsIntegral ℤ (spectralGen 53) ∧
      (minpoly ℚ (spectralGen 53)).natDegree = 26 :=
  isIntegral_and_degree_fiftyThree

end Brockian.CosTraceNormFiftyThree
