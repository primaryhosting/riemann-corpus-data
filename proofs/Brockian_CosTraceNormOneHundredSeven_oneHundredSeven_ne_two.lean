/-
  Brockian/CosTraceNormOneHundredSeven.lean — spectral generator at p = 107.

  [ℚ(2 cos 2π/107):ℚ] = 53 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredSeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredSeven : Nat.Prime 107 := by decide

theorem oneHundredSeven_ne_two : (107 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredSeven : (minpoly ℚ (spectralGen 107)).natDegree = 53 :=
  real_subfield_degree prime_oneHundredSeven oneHundredSeven_ne_two

theorem isIntegral_spectralGen_oneHundredSeven : IsIntegral ℤ (spectralGen 107) :=
  isIntegral_spectralGen prime_oneHundredSeven

theorem isIntegral_spectralGen_oneHundredSeven_Q : IsIntegral ℚ (spectralGen 107) :=
  isIntegral_spectralGen_ℚ prime_oneHundredSeven

theorem isIntegral_and_degree_oneHundredSeven :
    IsIntegral ℤ (spectralGen 107) ∧
      (minpoly ℚ (spectralGen 107)).natDegree = 53 :=
  ⟨isIntegral_spectralGen_oneHundredSeven, degree_oneHundredSeven⟩

theorem oneHundredSeven_pack :
    IsIntegral ℤ (spectralGen 107) ∧
      (minpoly ℚ (spectralGen 107)).natDegree = 53 :=
  isIntegral_and_degree_oneHundredSeven

end Brockian.CosTraceNormOneHundredSeven
