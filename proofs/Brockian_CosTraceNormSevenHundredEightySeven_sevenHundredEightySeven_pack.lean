/-
  Brockian/CosTraceNormSevenHundredEightySeven.lean — spectral generator at p = 787.

  [ℚ(2 cos 2π/787):ℚ] = 393 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredEightySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredEightySeven : Nat.Prime 787 := by decide

theorem sevenHundredEightySeven_ne_two : (787 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredEightySeven : (minpoly ℚ (spectralGen 787)).natDegree = 393 :=
  real_subfield_degree prime_sevenHundredEightySeven sevenHundredEightySeven_ne_two

theorem isIntegral_spectralGen_sevenHundredEightySeven : IsIntegral ℤ (spectralGen 787) :=
  isIntegral_spectralGen prime_sevenHundredEightySeven

theorem isIntegral_spectralGen_sevenHundredEightySeven_Q : IsIntegral ℚ (spectralGen 787) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredEightySeven

theorem isIntegral_and_degree_sevenHundredEightySeven :
    IsIntegral ℤ (spectralGen 787) ∧
      (minpoly ℚ (spectralGen 787)).natDegree = 393 :=
  ⟨isIntegral_spectralGen_sevenHundredEightySeven, degree_sevenHundredEightySeven⟩

theorem sevenHundredEightySeven_pack :
    IsIntegral ℤ (spectralGen 787) ∧
      (minpoly ℚ (spectralGen 787)).natDegree = 393 :=
  isIntegral_and_degree_sevenHundredEightySeven

end Brockian.CosTraceNormSevenHundredEightySeven
