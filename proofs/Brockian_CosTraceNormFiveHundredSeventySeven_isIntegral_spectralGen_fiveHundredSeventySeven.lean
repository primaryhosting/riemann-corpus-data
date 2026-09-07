/-
  Brockian/CosTraceNormFiveHundredSeventySeven.lean — spectral generator at p = 577.

  [ℚ(2 cos 2π/577):ℚ] = 288 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredSeventySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredSeventySeven : Nat.Prime 577 := by decide

theorem fiveHundredSeventySeven_ne_two : (577 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredSeventySeven : (minpoly ℚ (spectralGen 577)).natDegree = 288 :=
  real_subfield_degree prime_fiveHundredSeventySeven fiveHundredSeventySeven_ne_two

theorem isIntegral_spectralGen_fiveHundredSeventySeven : IsIntegral ℤ (spectralGen 577) :=
  isIntegral_spectralGen prime_fiveHundredSeventySeven

theorem isIntegral_spectralGen_fiveHundredSeventySeven_Q : IsIntegral ℚ (spectralGen 577) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredSeventySeven

theorem isIntegral_and_degree_fiveHundredSeventySeven :
    IsIntegral ℤ (spectralGen 577) ∧
      (minpoly ℚ (spectralGen 577)).natDegree = 288 :=
  ⟨isIntegral_spectralGen_fiveHundredSeventySeven, degree_fiveHundredSeventySeven⟩

theorem fiveHundredSeventySeven_pack :
    IsIntegral ℤ (spectralGen 577) ∧
      (minpoly ℚ (spectralGen 577)).natDegree = 288 :=
  isIntegral_and_degree_fiveHundredSeventySeven

end Brockian.CosTraceNormFiveHundredSeventySeven
