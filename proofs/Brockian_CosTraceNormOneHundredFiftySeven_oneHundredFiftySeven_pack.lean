/-
  Brockian/CosTraceNormOneHundredFiftySeven.lean — spectral generator at p = 157.

  [ℚ(2 cos 2π/157):ℚ] = 78 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredFiftySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredFiftySeven : Nat.Prime 157 := by decide

theorem oneHundredFiftySeven_ne_two : (157 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredFiftySeven : (minpoly ℚ (spectralGen 157)).natDegree = 78 :=
  real_subfield_degree prime_oneHundredFiftySeven oneHundredFiftySeven_ne_two

theorem isIntegral_spectralGen_oneHundredFiftySeven : IsIntegral ℤ (spectralGen 157) :=
  isIntegral_spectralGen prime_oneHundredFiftySeven

theorem isIntegral_spectralGen_oneHundredFiftySeven_Q : IsIntegral ℚ (spectralGen 157) :=
  isIntegral_spectralGen_ℚ prime_oneHundredFiftySeven

theorem isIntegral_and_degree_oneHundredFiftySeven :
    IsIntegral ℤ (spectralGen 157) ∧
      (minpoly ℚ (spectralGen 157)).natDegree = 78 :=
  ⟨isIntegral_spectralGen_oneHundredFiftySeven, degree_oneHundredFiftySeven⟩

theorem oneHundredFiftySeven_pack :
    IsIntegral ℤ (spectralGen 157) ∧
      (minpoly ℚ (spectralGen 157)).natDegree = 78 :=
  isIntegral_and_degree_oneHundredFiftySeven

end Brockian.CosTraceNormOneHundredFiftySeven
