/-
  Brockian/CosTraceNormNineHundredNinetySeven.lean — spectral generator at p = 997.

  [ℚ(2 cos 2π/997):ℚ] = 498 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredNinetySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredNinetySeven : Nat.Prime 997 := by decide

theorem nineHundredNinetySeven_ne_two : (997 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredNinetySeven : (minpoly ℚ (spectralGen 997)).natDegree = 498 :=
  real_subfield_degree prime_nineHundredNinetySeven nineHundredNinetySeven_ne_two

theorem isIntegral_spectralGen_nineHundredNinetySeven : IsIntegral ℤ (spectralGen 997) :=
  isIntegral_spectralGen prime_nineHundredNinetySeven

theorem isIntegral_spectralGen_nineHundredNinetySeven_Q : IsIntegral ℚ (spectralGen 997) :=
  isIntegral_spectralGen_ℚ prime_nineHundredNinetySeven

theorem isIntegral_and_degree_nineHundredNinetySeven :
    IsIntegral ℤ (spectralGen 997) ∧
      (minpoly ℚ (spectralGen 997)).natDegree = 498 :=
  ⟨isIntegral_spectralGen_nineHundredNinetySeven, degree_nineHundredNinetySeven⟩

theorem nineHundredNinetySeven_pack :
    IsIntegral ℤ (spectralGen 997) ∧
      (minpoly ℚ (spectralGen 997)).natDegree = 498 :=
  isIntegral_and_degree_nineHundredNinetySeven

end Brockian.CosTraceNormNineHundredNinetySeven
