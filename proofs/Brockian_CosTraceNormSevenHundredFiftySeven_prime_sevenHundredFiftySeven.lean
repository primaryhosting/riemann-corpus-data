/-
  Brockian/CosTraceNormSevenHundredFiftySeven.lean — spectral generator at p = 757.

  [ℚ(2 cos 2π/757):ℚ] = 378 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredFiftySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredFiftySeven : Nat.Prime 757 := by decide

theorem sevenHundredFiftySeven_ne_two : (757 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredFiftySeven : (minpoly ℚ (spectralGen 757)).natDegree = 378 :=
  real_subfield_degree prime_sevenHundredFiftySeven sevenHundredFiftySeven_ne_two

theorem isIntegral_spectralGen_sevenHundredFiftySeven : IsIntegral ℤ (spectralGen 757) :=
  isIntegral_spectralGen prime_sevenHundredFiftySeven

theorem isIntegral_spectralGen_sevenHundredFiftySeven_Q : IsIntegral ℚ (spectralGen 757) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredFiftySeven

theorem isIntegral_and_degree_sevenHundredFiftySeven :
    IsIntegral ℤ (spectralGen 757) ∧
      (minpoly ℚ (spectralGen 757)).natDegree = 378 :=
  ⟨isIntegral_spectralGen_sevenHundredFiftySeven, degree_sevenHundredFiftySeven⟩

theorem sevenHundredFiftySeven_pack :
    IsIntegral ℤ (spectralGen 757) ∧
      (minpoly ℚ (spectralGen 757)).natDegree = 378 :=
  isIntegral_and_degree_sevenHundredFiftySeven

end Brockian.CosTraceNormSevenHundredFiftySeven
