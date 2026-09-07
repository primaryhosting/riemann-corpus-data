/-
  Brockian/CosTraceNormSevenHundredNinetySeven.lean — spectral generator at p = 797.

  [ℚ(2 cos 2π/797):ℚ] = 398 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredNinetySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredNinetySeven : Nat.Prime 797 := by decide

theorem sevenHundredNinetySeven_ne_two : (797 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredNinetySeven : (minpoly ℚ (spectralGen 797)).natDegree = 398 :=
  real_subfield_degree prime_sevenHundredNinetySeven sevenHundredNinetySeven_ne_two

theorem isIntegral_spectralGen_sevenHundredNinetySeven : IsIntegral ℤ (spectralGen 797) :=
  isIntegral_spectralGen prime_sevenHundredNinetySeven

theorem isIntegral_spectralGen_sevenHundredNinetySeven_Q : IsIntegral ℚ (spectralGen 797) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredNinetySeven

theorem isIntegral_and_degree_sevenHundredNinetySeven :
    IsIntegral ℤ (spectralGen 797) ∧
      (minpoly ℚ (spectralGen 797)).natDegree = 398 :=
  ⟨isIntegral_spectralGen_sevenHundredNinetySeven, degree_sevenHundredNinetySeven⟩

theorem sevenHundredNinetySeven_pack :
    IsIntegral ℤ (spectralGen 797) ∧
      (minpoly ℚ (spectralGen 797)).natDegree = 398 :=
  isIntegral_and_degree_sevenHundredNinetySeven

end Brockian.CosTraceNormSevenHundredNinetySeven
