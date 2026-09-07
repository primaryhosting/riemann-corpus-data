/-
  Brockian/CosTraceNormOneHundredTwentySeven.lean — spectral generator at p = 127.

  [ℚ(2 cos 2π/127):ℚ] = 63 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredTwentySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredTwentySeven : Nat.Prime 127 := by decide

theorem oneHundredTwentySeven_ne_two : (127 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredTwentySeven : (minpoly ℚ (spectralGen 127)).natDegree = 63 :=
  real_subfield_degree prime_oneHundredTwentySeven oneHundredTwentySeven_ne_two

theorem isIntegral_spectralGen_oneHundredTwentySeven : IsIntegral ℤ (spectralGen 127) :=
  isIntegral_spectralGen prime_oneHundredTwentySeven

theorem isIntegral_spectralGen_oneHundredTwentySeven_Q : IsIntegral ℚ (spectralGen 127) :=
  isIntegral_spectralGen_ℚ prime_oneHundredTwentySeven

theorem isIntegral_and_degree_oneHundredTwentySeven :
    IsIntegral ℤ (spectralGen 127) ∧
      (minpoly ℚ (spectralGen 127)).natDegree = 63 :=
  ⟨isIntegral_spectralGen_oneHundredTwentySeven, degree_oneHundredTwentySeven⟩

theorem oneHundredTwentySeven_pack :
    IsIntegral ℤ (spectralGen 127) ∧
      (minpoly ℚ (spectralGen 127)).natDegree = 63 :=
  isIntegral_and_degree_oneHundredTwentySeven

end Brockian.CosTraceNormOneHundredTwentySeven
