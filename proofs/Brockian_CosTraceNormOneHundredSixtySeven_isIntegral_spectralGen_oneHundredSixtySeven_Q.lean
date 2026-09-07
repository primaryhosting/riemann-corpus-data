/-
  Brockian/CosTraceNormOneHundredSixtySeven.lean — spectral generator at p = 167.

  [ℚ(2 cos 2π/167):ℚ] = 83 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredSixtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredSixtySeven : Nat.Prime 167 := by decide

theorem oneHundredSixtySeven_ne_two : (167 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredSixtySeven : (minpoly ℚ (spectralGen 167)).natDegree = 83 :=
  real_subfield_degree prime_oneHundredSixtySeven oneHundredSixtySeven_ne_two

theorem isIntegral_spectralGen_oneHundredSixtySeven : IsIntegral ℤ (spectralGen 167) :=
  isIntegral_spectralGen prime_oneHundredSixtySeven

theorem isIntegral_spectralGen_oneHundredSixtySeven_Q : IsIntegral ℚ (spectralGen 167) :=
  isIntegral_spectralGen_ℚ prime_oneHundredSixtySeven

theorem isIntegral_and_degree_oneHundredSixtySeven :
    IsIntegral ℤ (spectralGen 167) ∧
      (minpoly ℚ (spectralGen 167)).natDegree = 83 :=
  ⟨isIntegral_spectralGen_oneHundredSixtySeven, degree_oneHundredSixtySeven⟩

theorem oneHundredSixtySeven_pack :
    IsIntegral ℤ (spectralGen 167) ∧
      (minpoly ℚ (spectralGen 167)).natDegree = 83 :=
  isIntegral_and_degree_oneHundredSixtySeven

end Brockian.CosTraceNormOneHundredSixtySeven
