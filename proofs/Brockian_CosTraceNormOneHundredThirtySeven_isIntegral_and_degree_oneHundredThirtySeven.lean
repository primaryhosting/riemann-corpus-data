/-
  Brockian/CosTraceNormOneHundredThirtySeven.lean — spectral generator at p = 137.

  [ℚ(2 cos 2π/137):ℚ] = 68 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredThirtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredThirtySeven : Nat.Prime 137 := by decide

theorem oneHundredThirtySeven_ne_two : (137 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredThirtySeven : (minpoly ℚ (spectralGen 137)).natDegree = 68 :=
  real_subfield_degree prime_oneHundredThirtySeven oneHundredThirtySeven_ne_two

theorem isIntegral_spectralGen_oneHundredThirtySeven : IsIntegral ℤ (spectralGen 137) :=
  isIntegral_spectralGen prime_oneHundredThirtySeven

theorem isIntegral_spectralGen_oneHundredThirtySeven_Q : IsIntegral ℚ (spectralGen 137) :=
  isIntegral_spectralGen_ℚ prime_oneHundredThirtySeven

theorem isIntegral_and_degree_oneHundredThirtySeven :
    IsIntegral ℤ (spectralGen 137) ∧
      (minpoly ℚ (spectralGen 137)).natDegree = 68 :=
  ⟨isIntegral_spectralGen_oneHundredThirtySeven, degree_oneHundredThirtySeven⟩

theorem oneHundredThirtySeven_pack :
    IsIntegral ℤ (spectralGen 137) ∧
      (minpoly ℚ (spectralGen 137)).natDegree = 68 :=
  isIntegral_and_degree_oneHundredThirtySeven

end Brockian.CosTraceNormOneHundredThirtySeven
