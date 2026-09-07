/-
  Brockian/CosTraceNormNineHundredThirtySeven.lean — spectral generator at p = 937.

  [ℚ(2 cos 2π/937):ℚ] = 468 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredThirtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredThirtySeven : Nat.Prime 937 := by decide

theorem nineHundredThirtySeven_ne_two : (937 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredThirtySeven : (minpoly ℚ (spectralGen 937)).natDegree = 468 :=
  real_subfield_degree prime_nineHundredThirtySeven nineHundredThirtySeven_ne_two

theorem isIntegral_spectralGen_nineHundredThirtySeven : IsIntegral ℤ (spectralGen 937) :=
  isIntegral_spectralGen prime_nineHundredThirtySeven

theorem isIntegral_spectralGen_nineHundredThirtySeven_Q : IsIntegral ℚ (spectralGen 937) :=
  isIntegral_spectralGen_ℚ prime_nineHundredThirtySeven

theorem isIntegral_and_degree_nineHundredThirtySeven :
    IsIntegral ℤ (spectralGen 937) ∧
      (minpoly ℚ (spectralGen 937)).natDegree = 468 :=
  ⟨isIntegral_spectralGen_nineHundredThirtySeven, degree_nineHundredThirtySeven⟩

theorem nineHundredThirtySeven_pack :
    IsIntegral ℤ (spectralGen 937) ∧
      (minpoly ℚ (spectralGen 937)).natDegree = 468 :=
  isIntegral_and_degree_nineHundredThirtySeven

end Brockian.CosTraceNormNineHundredThirtySeven
