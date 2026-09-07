/-
  Brockian/CosTraceNormOneHundredNinetySeven.lean — spectral generator at p = 197.

  [ℚ(2 cos 2π/197):ℚ] = 98 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredNinetySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredNinetySeven : Nat.Prime 197 := by decide

theorem oneHundredNinetySeven_ne_two : (197 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredNinetySeven : (minpoly ℚ (spectralGen 197)).natDegree = 98 :=
  real_subfield_degree prime_oneHundredNinetySeven oneHundredNinetySeven_ne_two

theorem isIntegral_spectralGen_oneHundredNinetySeven : IsIntegral ℤ (spectralGen 197) :=
  isIntegral_spectralGen prime_oneHundredNinetySeven

theorem isIntegral_spectralGen_oneHundredNinetySeven_Q : IsIntegral ℚ (spectralGen 197) :=
  isIntegral_spectralGen_ℚ prime_oneHundredNinetySeven

theorem isIntegral_and_degree_oneHundredNinetySeven :
    IsIntegral ℤ (spectralGen 197) ∧
      (minpoly ℚ (spectralGen 197)).natDegree = 98 :=
  ⟨isIntegral_spectralGen_oneHundredNinetySeven, degree_oneHundredNinetySeven⟩

theorem oneHundredNinetySeven_pack :
    IsIntegral ℤ (spectralGen 197) ∧
      (minpoly ℚ (spectralGen 197)).natDegree = 98 :=
  isIntegral_and_degree_oneHundredNinetySeven

end Brockian.CosTraceNormOneHundredNinetySeven
