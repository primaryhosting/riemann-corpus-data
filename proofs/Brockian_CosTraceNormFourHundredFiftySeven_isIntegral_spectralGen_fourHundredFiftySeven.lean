/-
  Brockian/CosTraceNormFourHundredFiftySeven.lean — spectral generator at p = 457.

  [ℚ(2 cos 2π/457):ℚ] = 228 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredFiftySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredFiftySeven : Nat.Prime 457 := by decide

theorem fourHundredFiftySeven_ne_two : (457 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredFiftySeven : (minpoly ℚ (spectralGen 457)).natDegree = 228 :=
  real_subfield_degree prime_fourHundredFiftySeven fourHundredFiftySeven_ne_two

theorem isIntegral_spectralGen_fourHundredFiftySeven : IsIntegral ℤ (spectralGen 457) :=
  isIntegral_spectralGen prime_fourHundredFiftySeven

theorem isIntegral_spectralGen_fourHundredFiftySeven_Q : IsIntegral ℚ (spectralGen 457) :=
  isIntegral_spectralGen_ℚ prime_fourHundredFiftySeven

theorem isIntegral_and_degree_fourHundredFiftySeven :
    IsIntegral ℤ (spectralGen 457) ∧
      (minpoly ℚ (spectralGen 457)).natDegree = 228 :=
  ⟨isIntegral_spectralGen_fourHundredFiftySeven, degree_fourHundredFiftySeven⟩

theorem fourHundredFiftySeven_pack :
    IsIntegral ℤ (spectralGen 457) ∧
      (minpoly ℚ (spectralGen 457)).natDegree = 228 :=
  isIntegral_and_degree_fourHundredFiftySeven

end Brockian.CosTraceNormFourHundredFiftySeven
