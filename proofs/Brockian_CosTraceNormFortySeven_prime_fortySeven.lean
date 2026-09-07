/-
  Brockian/CosTraceNormFortySeven.lean — spectral generator at p = 47.

  [ℚ(2 cos 2π/47):ℚ] = 23 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormFortySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fortySeven : Nat.Prime 47 := by decide

theorem fortySeven_ne_two : (47 : ℕ) ≠ 2 := by decide

theorem degree_fortySeven : (minpoly ℚ (spectralGen 47)).natDegree = 23 :=
  real_subfield_degree prime_fortySeven fortySeven_ne_two

theorem isIntegral_spectralGen_fortySeven : IsIntegral ℤ (spectralGen 47) :=
  isIntegral_spectralGen prime_fortySeven

theorem isIntegral_spectralGen_fortySeven_Q : IsIntegral ℚ (spectralGen 47) :=
  isIntegral_spectralGen_ℚ prime_fortySeven

theorem isIntegral_and_degree_fortySeven :
    IsIntegral ℤ (spectralGen 47) ∧
      (minpoly ℚ (spectralGen 47)).natDegree = 23 :=
  ⟨isIntegral_spectralGen_fortySeven, degree_fortySeven⟩

theorem fortySeven_pack :
    IsIntegral ℤ (spectralGen 47) ∧
      (minpoly ℚ (spectralGen 47)).natDegree = 23 :=
  isIntegral_and_degree_fortySeven

end Brockian.CosTraceNormFortySeven
