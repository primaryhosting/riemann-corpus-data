/-
  Brockian/CosTraceNormTwoHundredEleven.lean — spectral generator at p = 211.

  [ℚ(2 cos 2π/211):ℚ] = 105 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredEleven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredEleven : Nat.Prime 211 := by decide

theorem twoHundredEleven_ne_two : (211 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredEleven : (minpoly ℚ (spectralGen 211)).natDegree = 105 :=
  real_subfield_degree prime_twoHundredEleven twoHundredEleven_ne_two

theorem isIntegral_spectralGen_twoHundredEleven : IsIntegral ℤ (spectralGen 211) :=
  isIntegral_spectralGen prime_twoHundredEleven

theorem isIntegral_spectralGen_twoHundredEleven_Q : IsIntegral ℚ (spectralGen 211) :=
  isIntegral_spectralGen_ℚ prime_twoHundredEleven

theorem isIntegral_and_degree_twoHundredEleven :
    IsIntegral ℤ (spectralGen 211) ∧
      (minpoly ℚ (spectralGen 211)).natDegree = 105 :=
  ⟨isIntegral_spectralGen_twoHundredEleven, degree_twoHundredEleven⟩

theorem twoHundredEleven_pack :
    IsIntegral ℤ (spectralGen 211) ∧
      (minpoly ℚ (spectralGen 211)).natDegree = 105 :=
  isIntegral_and_degree_twoHundredEleven

end Brockian.CosTraceNormTwoHundredEleven
