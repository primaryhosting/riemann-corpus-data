/-
  Brockian/CosTraceNormSixHundredSeventySeven.lean — spectral generator at p = 677.

  [ℚ(2 cos 2π/677):ℚ] = 338 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredSeventySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredSeventySeven : Nat.Prime 677 := by decide

theorem sixHundredSeventySeven_ne_two : (677 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredSeventySeven : (minpoly ℚ (spectralGen 677)).natDegree = 338 :=
  real_subfield_degree prime_sixHundredSeventySeven sixHundredSeventySeven_ne_two

theorem isIntegral_spectralGen_sixHundredSeventySeven : IsIntegral ℤ (spectralGen 677) :=
  isIntegral_spectralGen prime_sixHundredSeventySeven

theorem isIntegral_spectralGen_sixHundredSeventySeven_Q : IsIntegral ℚ (spectralGen 677) :=
  isIntegral_spectralGen_ℚ prime_sixHundredSeventySeven

theorem isIntegral_and_degree_sixHundredSeventySeven :
    IsIntegral ℤ (spectralGen 677) ∧
      (minpoly ℚ (spectralGen 677)).natDegree = 338 :=
  ⟨isIntegral_spectralGen_sixHundredSeventySeven, degree_sixHundredSeventySeven⟩

theorem sixHundredSeventySeven_pack :
    IsIntegral ℤ (spectralGen 677) ∧
      (minpoly ℚ (spectralGen 677)).natDegree = 338 :=
  isIntegral_and_degree_sixHundredSeventySeven

end Brockian.CosTraceNormSixHundredSeventySeven
