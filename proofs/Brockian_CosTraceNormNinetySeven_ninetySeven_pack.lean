/-
  Brockian/CosTraceNormNinetySeven.lean — spectral generator at p = 97.

  [ℚ(2 cos 2π/97):ℚ] = 48 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormNinetySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_ninetySeven : Nat.Prime 97 := by decide

theorem ninetySeven_ne_two : (97 : ℕ) ≠ 2 := by decide

theorem degree_ninetySeven : (minpoly ℚ (spectralGen 97)).natDegree = 48 :=
  real_subfield_degree prime_ninetySeven ninetySeven_ne_two

theorem isIntegral_spectralGen_ninetySeven : IsIntegral ℤ (spectralGen 97) :=
  isIntegral_spectralGen prime_ninetySeven

theorem isIntegral_spectralGen_ninetySeven_Q : IsIntegral ℚ (spectralGen 97) :=
  isIntegral_spectralGen_ℚ prime_ninetySeven

theorem isIntegral_and_degree_ninetySeven :
    IsIntegral ℤ (spectralGen 97) ∧
      (minpoly ℚ (spectralGen 97)).natDegree = 48 :=
  ⟨isIntegral_spectralGen_ninetySeven, degree_ninetySeven⟩

theorem ninetySeven_pack :
    IsIntegral ℤ (spectralGen 97) ∧
      (minpoly ℚ (spectralGen 97)).natDegree = 48 :=
  isIntegral_and_degree_ninetySeven

end Brockian.CosTraceNormNinetySeven
