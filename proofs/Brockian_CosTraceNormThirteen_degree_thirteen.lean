/-
  Brockian/CosTraceNormThirteen.lean — spectral generator at p = 13 (solid pack).

  [ℚ(2 cos 2π/13):ℚ] = 6 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  No expanded minpoly coefficients claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormThirteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_thirteen : Nat.Prime 13 := by decide

theorem thirteen_ne_two : (13 : ℕ) ≠ 2 := by decide

theorem degree_thirteen : (minpoly ℚ (spectralGen 13)).natDegree = 6 :=
  real_subfield_degree prime_thirteen thirteen_ne_two

theorem isIntegral_spectralGen_thirteen : IsIntegral ℤ (spectralGen 13) :=
  isIntegral_spectralGen prime_thirteen

theorem isIntegral_spectralGen_thirteen_Q : IsIntegral ℚ (spectralGen 13) :=
  isIntegral_spectralGen_ℚ prime_thirteen

theorem isIntegral_and_degree_thirteen :
    IsIntegral ℤ (spectralGen 13) ∧
      (minpoly ℚ (spectralGen 13)).natDegree = 6 :=
  ⟨isIntegral_spectralGen_thirteen, degree_thirteen⟩

theorem thirteen_pack :
    IsIntegral ℤ (spectralGen 13) ∧
      (minpoly ℚ (spectralGen 13)).natDegree = 6 :=
  isIntegral_and_degree_thirteen

end Brockian.CosTraceNormThirteen
