/-
  Brockian/CosTraceNormSeventeen.lean — spectral generator at p = 17.

  [ℚ(2 cos 2π/17):ℚ] = 8 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormSeventeen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_seventeen : Nat.Prime 17 := by decide

theorem seventeen_ne_two : (17 : ℕ) ≠ 2 := by decide

theorem degree_seventeen : (minpoly ℚ (spectralGen 17)).natDegree = 8 :=
  real_subfield_degree prime_seventeen seventeen_ne_two

theorem isIntegral_spectralGen_seventeen : IsIntegral ℤ (spectralGen 17) :=
  isIntegral_spectralGen prime_seventeen

theorem isIntegral_spectralGen_seventeen_Q : IsIntegral ℚ (spectralGen 17) :=
  isIntegral_spectralGen_ℚ prime_seventeen

theorem isIntegral_and_degree_seventeen :
    IsIntegral ℤ (spectralGen 17) ∧
      (minpoly ℚ (spectralGen 17)).natDegree = 8 :=
  ⟨isIntegral_spectralGen_seventeen, degree_seventeen⟩

theorem seventeen_pack :
    IsIntegral ℤ (spectralGen 17) ∧
      (minpoly ℚ (spectralGen 17)).natDegree = 8 :=
  isIntegral_and_degree_seventeen

end Brockian.CosTraceNormSeventeen
