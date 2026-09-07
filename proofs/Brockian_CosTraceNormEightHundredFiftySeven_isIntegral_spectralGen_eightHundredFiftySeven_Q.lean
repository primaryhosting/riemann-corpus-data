/-
  Brockian/CosTraceNormEightHundredFiftySeven.lean — spectral generator at p = 857.

  [ℚ(2 cos 2π/857):ℚ] = 428 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredFiftySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredFiftySeven : Nat.Prime 857 := by decide

theorem eightHundredFiftySeven_ne_two : (857 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredFiftySeven : (minpoly ℚ (spectralGen 857)).natDegree = 428 :=
  real_subfield_degree prime_eightHundredFiftySeven eightHundredFiftySeven_ne_two

theorem isIntegral_spectralGen_eightHundredFiftySeven : IsIntegral ℤ (spectralGen 857) :=
  isIntegral_spectralGen prime_eightHundredFiftySeven

theorem isIntegral_spectralGen_eightHundredFiftySeven_Q : IsIntegral ℚ (spectralGen 857) :=
  isIntegral_spectralGen_ℚ prime_eightHundredFiftySeven

theorem isIntegral_and_degree_eightHundredFiftySeven :
    IsIntegral ℤ (spectralGen 857) ∧
      (minpoly ℚ (spectralGen 857)).natDegree = 428 :=
  ⟨isIntegral_spectralGen_eightHundredFiftySeven, degree_eightHundredFiftySeven⟩

theorem eightHundredFiftySeven_pack :
    IsIntegral ℤ (spectralGen 857) ∧
      (minpoly ℚ (spectralGen 857)).natDegree = 428 :=
  isIntegral_and_degree_eightHundredFiftySeven

end Brockian.CosTraceNormEightHundredFiftySeven
