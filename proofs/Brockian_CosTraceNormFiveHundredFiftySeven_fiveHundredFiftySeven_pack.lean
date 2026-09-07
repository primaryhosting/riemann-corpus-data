/-
  Brockian/CosTraceNormFiveHundredFiftySeven.lean — spectral generator at p = 557.

  [ℚ(2 cos 2π/557):ℚ] = 278 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredFiftySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredFiftySeven : Nat.Prime 557 := by decide

theorem fiveHundredFiftySeven_ne_two : (557 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredFiftySeven : (minpoly ℚ (spectralGen 557)).natDegree = 278 :=
  real_subfield_degree prime_fiveHundredFiftySeven fiveHundredFiftySeven_ne_two

theorem isIntegral_spectralGen_fiveHundredFiftySeven : IsIntegral ℤ (spectralGen 557) :=
  isIntegral_spectralGen prime_fiveHundredFiftySeven

theorem isIntegral_spectralGen_fiveHundredFiftySeven_Q : IsIntegral ℚ (spectralGen 557) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredFiftySeven

theorem isIntegral_and_degree_fiveHundredFiftySeven :
    IsIntegral ℤ (spectralGen 557) ∧
      (minpoly ℚ (spectralGen 557)).natDegree = 278 :=
  ⟨isIntegral_spectralGen_fiveHundredFiftySeven, degree_fiveHundredFiftySeven⟩

theorem fiveHundredFiftySeven_pack :
    IsIntegral ℤ (spectralGen 557) ∧
      (minpoly ℚ (spectralGen 557)).natDegree = 278 :=
  isIntegral_and_degree_fiveHundredFiftySeven

end Brockian.CosTraceNormFiveHundredFiftySeven
