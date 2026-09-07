/-
  Brockian/CosTraceNormThirtySeven.lean — spectral generator at p = 37.

  [ℚ(2 cos 2π/37):ℚ] = 18 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormThirtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_thirtySeven : Nat.Prime 37 := by decide

theorem thirtySeven_ne_two : (37 : ℕ) ≠ 2 := by decide

theorem degree_thirtySeven : (minpoly ℚ (spectralGen 37)).natDegree = 18 :=
  real_subfield_degree prime_thirtySeven thirtySeven_ne_two

theorem isIntegral_spectralGen_thirtySeven : IsIntegral ℤ (spectralGen 37) :=
  isIntegral_spectralGen prime_thirtySeven

theorem isIntegral_spectralGen_thirtySeven_Q : IsIntegral ℚ (spectralGen 37) :=
  isIntegral_spectralGen_ℚ prime_thirtySeven

theorem isIntegral_and_degree_thirtySeven :
    IsIntegral ℤ (spectralGen 37) ∧
      (minpoly ℚ (spectralGen 37)).natDegree = 18 :=
  ⟨isIntegral_spectralGen_thirtySeven, degree_thirtySeven⟩

theorem thirtySeven_pack :
    IsIntegral ℤ (spectralGen 37) ∧
      (minpoly ℚ (spectralGen 37)).natDegree = 18 :=
  isIntegral_and_degree_thirtySeven

end Brockian.CosTraceNormThirtySeven
