/-
  Brockian/CosTraceNormSeventyThree.lean — spectral generator at p = 73.

  [ℚ(2 cos 2π/73):ℚ] = 36 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormSeventyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_seventyThree : Nat.Prime 73 := by decide

theorem seventyThree_ne_two : (73 : ℕ) ≠ 2 := by decide

theorem degree_seventyThree : (minpoly ℚ (spectralGen 73)).natDegree = 36 :=
  real_subfield_degree prime_seventyThree seventyThree_ne_two

theorem isIntegral_spectralGen_seventyThree : IsIntegral ℤ (spectralGen 73) :=
  isIntegral_spectralGen prime_seventyThree

theorem isIntegral_spectralGen_seventyThree_Q : IsIntegral ℚ (spectralGen 73) :=
  isIntegral_spectralGen_ℚ prime_seventyThree

theorem isIntegral_and_degree_seventyThree :
    IsIntegral ℤ (spectralGen 73) ∧
      (minpoly ℚ (spectralGen 73)).natDegree = 36 :=
  ⟨isIntegral_spectralGen_seventyThree, degree_seventyThree⟩

theorem seventyThree_pack :
    IsIntegral ℤ (spectralGen 73) ∧
      (minpoly ℚ (spectralGen 73)).natDegree = 36 :=
  isIntegral_and_degree_seventyThree

end Brockian.CosTraceNormSeventyThree
