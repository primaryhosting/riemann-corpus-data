/-
  Brockian/CosTraceNormTwoHundredFiftySeven.lean — spectral generator at p = 257.

  [ℚ(2 cos 2π/257):ℚ] = 128 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredFiftySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredFiftySeven : Nat.Prime 257 := by decide

theorem twoHundredFiftySeven_ne_two : (257 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredFiftySeven : (minpoly ℚ (spectralGen 257)).natDegree = 128 :=
  real_subfield_degree prime_twoHundredFiftySeven twoHundredFiftySeven_ne_two

theorem isIntegral_spectralGen_twoHundredFiftySeven : IsIntegral ℤ (spectralGen 257) :=
  isIntegral_spectralGen prime_twoHundredFiftySeven

theorem isIntegral_spectralGen_twoHundredFiftySeven_Q : IsIntegral ℚ (spectralGen 257) :=
  isIntegral_spectralGen_ℚ prime_twoHundredFiftySeven

theorem isIntegral_and_degree_twoHundredFiftySeven :
    IsIntegral ℤ (spectralGen 257) ∧
      (minpoly ℚ (spectralGen 257)).natDegree = 128 :=
  ⟨isIntegral_spectralGen_twoHundredFiftySeven, degree_twoHundredFiftySeven⟩

theorem twoHundredFiftySeven_pack :
    IsIntegral ℤ (spectralGen 257) ∧
      (minpoly ℚ (spectralGen 257)).natDegree = 128 :=
  isIntegral_and_degree_twoHundredFiftySeven

end Brockian.CosTraceNormTwoHundredFiftySeven
