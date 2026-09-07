/-
  Brockian/CosTraceNormOneHundredThirteen.lean — spectral generator at p = 113.

  [ℚ(2 cos 2π/113):ℚ] = 56 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredThirteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredThirteen : Nat.Prime 113 := by decide

theorem oneHundredThirteen_ne_two : (113 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredThirteen : (minpoly ℚ (spectralGen 113)).natDegree = 56 :=
  real_subfield_degree prime_oneHundredThirteen oneHundredThirteen_ne_two

theorem isIntegral_spectralGen_oneHundredThirteen : IsIntegral ℤ (spectralGen 113) :=
  isIntegral_spectralGen prime_oneHundredThirteen

theorem isIntegral_spectralGen_oneHundredThirteen_Q : IsIntegral ℚ (spectralGen 113) :=
  isIntegral_spectralGen_ℚ prime_oneHundredThirteen

theorem isIntegral_and_degree_oneHundredThirteen :
    IsIntegral ℤ (spectralGen 113) ∧
      (minpoly ℚ (spectralGen 113)).natDegree = 56 :=
  ⟨isIntegral_spectralGen_oneHundredThirteen, degree_oneHundredThirteen⟩

theorem oneHundredThirteen_pack :
    IsIntegral ℤ (spectralGen 113) ∧
      (minpoly ℚ (spectralGen 113)).natDegree = 56 :=
  isIntegral_and_degree_oneHundredThirteen

end Brockian.CosTraceNormOneHundredThirteen
