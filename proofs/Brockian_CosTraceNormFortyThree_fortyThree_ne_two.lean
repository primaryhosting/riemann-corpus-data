/-
  Brockian/CosTraceNormFortyThree.lean — spectral generator at p = 43.

  [ℚ(2 cos 2π/43):ℚ] = 21 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormFortyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fortyThree : Nat.Prime 43 := by decide

theorem fortyThree_ne_two : (43 : ℕ) ≠ 2 := by decide

theorem degree_fortyThree : (minpoly ℚ (spectralGen 43)).natDegree = 21 :=
  real_subfield_degree prime_fortyThree fortyThree_ne_two

theorem isIntegral_spectralGen_fortyThree : IsIntegral ℤ (spectralGen 43) :=
  isIntegral_spectralGen prime_fortyThree

theorem isIntegral_spectralGen_fortyThree_Q : IsIntegral ℚ (spectralGen 43) :=
  isIntegral_spectralGen_ℚ prime_fortyThree

theorem isIntegral_and_degree_fortyThree :
    IsIntegral ℤ (spectralGen 43) ∧
      (minpoly ℚ (spectralGen 43)).natDegree = 21 :=
  ⟨isIntegral_spectralGen_fortyThree, degree_fortyThree⟩

theorem fortyThree_pack :
    IsIntegral ℤ (spectralGen 43) ∧
      (minpoly ℚ (spectralGen 43)).natDegree = 21 :=
  isIntegral_and_degree_fortyThree

end Brockian.CosTraceNormFortyThree
