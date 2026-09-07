/-
  Brockian/CosTraceNormNineHundredSeventySeven.lean — spectral generator at p = 977.

  [ℚ(2 cos 2π/977):ℚ] = 488 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredSeventySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredSeventySeven : Nat.Prime 977 := by decide

theorem nineHundredSeventySeven_ne_two : (977 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredSeventySeven : (minpoly ℚ (spectralGen 977)).natDegree = 488 :=
  real_subfield_degree prime_nineHundredSeventySeven nineHundredSeventySeven_ne_two

theorem isIntegral_spectralGen_nineHundredSeventySeven : IsIntegral ℤ (spectralGen 977) :=
  isIntegral_spectralGen prime_nineHundredSeventySeven

theorem isIntegral_spectralGen_nineHundredSeventySeven_Q : IsIntegral ℚ (spectralGen 977) :=
  isIntegral_spectralGen_ℚ prime_nineHundredSeventySeven

theorem isIntegral_and_degree_nineHundredSeventySeven :
    IsIntegral ℤ (spectralGen 977) ∧
      (minpoly ℚ (spectralGen 977)).natDegree = 488 :=
  ⟨isIntegral_spectralGen_nineHundredSeventySeven, degree_nineHundredSeventySeven⟩

theorem nineHundredSeventySeven_pack :
    IsIntegral ℤ (spectralGen 977) ∧
      (minpoly ℚ (spectralGen 977)).natDegree = 488 :=
  isIntegral_and_degree_nineHundredSeventySeven

end Brockian.CosTraceNormNineHundredSeventySeven
