/-
  Brockian/CosTraceNormNineHundredFortySeven.lean — spectral generator at p = 947.

  [ℚ(2 cos 2π/947):ℚ] = 473 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredFortySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredFortySeven : Nat.Prime 947 := by decide

theorem nineHundredFortySeven_ne_two : (947 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredFortySeven : (minpoly ℚ (spectralGen 947)).natDegree = 473 :=
  real_subfield_degree prime_nineHundredFortySeven nineHundredFortySeven_ne_two

theorem isIntegral_spectralGen_nineHundredFortySeven : IsIntegral ℤ (spectralGen 947) :=
  isIntegral_spectralGen prime_nineHundredFortySeven

theorem isIntegral_spectralGen_nineHundredFortySeven_Q : IsIntegral ℚ (spectralGen 947) :=
  isIntegral_spectralGen_ℚ prime_nineHundredFortySeven

theorem isIntegral_and_degree_nineHundredFortySeven :
    IsIntegral ℤ (spectralGen 947) ∧
      (minpoly ℚ (spectralGen 947)).natDegree = 473 :=
  ⟨isIntegral_spectralGen_nineHundredFortySeven, degree_nineHundredFortySeven⟩

theorem nineHundredFortySeven_pack :
    IsIntegral ℤ (spectralGen 947) ∧
      (minpoly ℚ (spectralGen 947)).natDegree = 473 :=
  isIntegral_and_degree_nineHundredFortySeven

end Brockian.CosTraceNormNineHundredFortySeven
