/-
  Brockian/CosTraceNormSixtySeven.lean — spectral generator at p = 67.

  [ℚ(2 cos 2π/67):ℚ] = 33 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormSixtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixtySeven : Nat.Prime 67 := by decide

theorem sixtySeven_ne_two : (67 : ℕ) ≠ 2 := by decide

theorem degree_sixtySeven : (minpoly ℚ (spectralGen 67)).natDegree = 33 :=
  real_subfield_degree prime_sixtySeven sixtySeven_ne_two

theorem isIntegral_spectralGen_sixtySeven : IsIntegral ℤ (spectralGen 67) :=
  isIntegral_spectralGen prime_sixtySeven

theorem isIntegral_spectralGen_sixtySeven_Q : IsIntegral ℚ (spectralGen 67) :=
  isIntegral_spectralGen_ℚ prime_sixtySeven

theorem isIntegral_and_degree_sixtySeven :
    IsIntegral ℤ (spectralGen 67) ∧
      (minpoly ℚ (spectralGen 67)).natDegree = 33 :=
  ⟨isIntegral_spectralGen_sixtySeven, degree_sixtySeven⟩

theorem sixtySeven_pack :
    IsIntegral ℤ (spectralGen 67) ∧
      (minpoly ℚ (spectralGen 67)).natDegree = 33 :=
  isIntegral_and_degree_sixtySeven

end Brockian.CosTraceNormSixtySeven
