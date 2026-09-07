/-
  Brockian/CosTraceNormTwoHundredSeventySeven.lean — spectral generator at p = 277.

  [ℚ(2 cos 2π/277):ℚ] = 138 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredSeventySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredSeventySeven : Nat.Prime 277 := by decide

theorem twoHundredSeventySeven_ne_two : (277 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredSeventySeven : (minpoly ℚ (spectralGen 277)).natDegree = 138 :=
  real_subfield_degree prime_twoHundredSeventySeven twoHundredSeventySeven_ne_two

theorem isIntegral_spectralGen_twoHundredSeventySeven : IsIntegral ℤ (spectralGen 277) :=
  isIntegral_spectralGen prime_twoHundredSeventySeven

theorem isIntegral_spectralGen_twoHundredSeventySeven_Q : IsIntegral ℚ (spectralGen 277) :=
  isIntegral_spectralGen_ℚ prime_twoHundredSeventySeven

theorem isIntegral_and_degree_twoHundredSeventySeven :
    IsIntegral ℤ (spectralGen 277) ∧
      (minpoly ℚ (spectralGen 277)).natDegree = 138 :=
  ⟨isIntegral_spectralGen_twoHundredSeventySeven, degree_twoHundredSeventySeven⟩

theorem twoHundredSeventySeven_pack :
    IsIntegral ℤ (spectralGen 277) ∧
      (minpoly ℚ (spectralGen 277)).natDegree = 138 :=
  isIntegral_and_degree_twoHundredSeventySeven

end Brockian.CosTraceNormTwoHundredSeventySeven
