/-
  Brockian/CosTraceNormSixHundredSeven.lean — spectral generator at p = 607.

  [ℚ(2 cos 2π/607):ℚ] = 303 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredSeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredSeven : Nat.Prime 607 := by decide

theorem sixHundredSeven_ne_two : (607 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredSeven : (minpoly ℚ (spectralGen 607)).natDegree = 303 :=
  real_subfield_degree prime_sixHundredSeven sixHundredSeven_ne_two

theorem isIntegral_spectralGen_sixHundredSeven : IsIntegral ℤ (spectralGen 607) :=
  isIntegral_spectralGen prime_sixHundredSeven

theorem isIntegral_spectralGen_sixHundredSeven_Q : IsIntegral ℚ (spectralGen 607) :=
  isIntegral_spectralGen_ℚ prime_sixHundredSeven

theorem isIntegral_and_degree_sixHundredSeven :
    IsIntegral ℤ (spectralGen 607) ∧
      (minpoly ℚ (spectralGen 607)).natDegree = 303 :=
  ⟨isIntegral_spectralGen_sixHundredSeven, degree_sixHundredSeven⟩

theorem sixHundredSeven_pack :
    IsIntegral ℤ (spectralGen 607) ∧
      (minpoly ℚ (spectralGen 607)).natDegree = 303 :=
  isIntegral_and_degree_sixHundredSeven

end Brockian.CosTraceNormSixHundredSeven
