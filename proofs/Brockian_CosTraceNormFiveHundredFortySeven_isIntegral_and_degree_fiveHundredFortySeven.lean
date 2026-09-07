/-
  Brockian/CosTraceNormFiveHundredFortySeven.lean — spectral generator at p = 547.

  [ℚ(2 cos 2π/547):ℚ] = 273 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredFortySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredFortySeven : Nat.Prime 547 := by decide

theorem fiveHundredFortySeven_ne_two : (547 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredFortySeven : (minpoly ℚ (spectralGen 547)).natDegree = 273 :=
  real_subfield_degree prime_fiveHundredFortySeven fiveHundredFortySeven_ne_two

theorem isIntegral_spectralGen_fiveHundredFortySeven : IsIntegral ℤ (spectralGen 547) :=
  isIntegral_spectralGen prime_fiveHundredFortySeven

theorem isIntegral_spectralGen_fiveHundredFortySeven_Q : IsIntegral ℚ (spectralGen 547) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredFortySeven

theorem isIntegral_and_degree_fiveHundredFortySeven :
    IsIntegral ℤ (spectralGen 547) ∧
      (minpoly ℚ (spectralGen 547)).natDegree = 273 :=
  ⟨isIntegral_spectralGen_fiveHundredFortySeven, degree_fiveHundredFortySeven⟩

theorem fiveHundredFortySeven_pack :
    IsIntegral ℤ (spectralGen 547) ∧
      (minpoly ℚ (spectralGen 547)).natDegree = 273 :=
  isIntegral_and_degree_fiveHundredFortySeven

end Brockian.CosTraceNormFiveHundredFortySeven
