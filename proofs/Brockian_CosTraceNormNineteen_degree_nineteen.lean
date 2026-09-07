/-
  Brockian/CosTraceNormNineteen.lean — spectral generator at p = 19.

  [ℚ(2 cos 2π/19):ℚ] = 9 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
  Grok lane (board): non-colliding with Claude GoldbachSelectionRule / PentagonMultiplicities.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormNineteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineteen : Nat.Prime 19 := by decide

theorem nineteen_ne_two : (19 : ℕ) ≠ 2 := by decide

theorem degree_nineteen : (minpoly ℚ (spectralGen 19)).natDegree = 9 :=
  real_subfield_degree prime_nineteen nineteen_ne_two

theorem isIntegral_spectralGen_nineteen : IsIntegral ℤ (spectralGen 19) :=
  isIntegral_spectralGen prime_nineteen

theorem isIntegral_spectralGen_nineteen_Q : IsIntegral ℚ (spectralGen 19) :=
  isIntegral_spectralGen_ℚ prime_nineteen

theorem isIntegral_and_degree_nineteen :
    IsIntegral ℤ (spectralGen 19) ∧
      (minpoly ℚ (spectralGen 19)).natDegree = 9 :=
  ⟨isIntegral_spectralGen_nineteen, degree_nineteen⟩

theorem nineteen_pack :
    IsIntegral ℤ (spectralGen 19) ∧
      (minpoly ℚ (spectralGen 19)).natDegree = 9 :=
  isIntegral_and_degree_nineteen

end Brockian.CosTraceNormNineteen
