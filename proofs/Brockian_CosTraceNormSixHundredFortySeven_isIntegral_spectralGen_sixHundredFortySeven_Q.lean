/-
  Brockian/CosTraceNormSixHundredFortySeven.lean — spectral generator at p = 647.

  [ℚ(2 cos 2π/647):ℚ] = 323 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredFortySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredFortySeven : Nat.Prime 647 := by decide

theorem sixHundredFortySeven_ne_two : (647 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredFortySeven : (minpoly ℚ (spectralGen 647)).natDegree = 323 :=
  real_subfield_degree prime_sixHundredFortySeven sixHundredFortySeven_ne_two

theorem isIntegral_spectralGen_sixHundredFortySeven : IsIntegral ℤ (spectralGen 647) :=
  isIntegral_spectralGen prime_sixHundredFortySeven

theorem isIntegral_spectralGen_sixHundredFortySeven_Q : IsIntegral ℚ (spectralGen 647) :=
  isIntegral_spectralGen_ℚ prime_sixHundredFortySeven

theorem isIntegral_and_degree_sixHundredFortySeven :
    IsIntegral ℤ (spectralGen 647) ∧
      (minpoly ℚ (spectralGen 647)).natDegree = 323 :=
  ⟨isIntegral_spectralGen_sixHundredFortySeven, degree_sixHundredFortySeven⟩

theorem sixHundredFortySeven_pack :
    IsIntegral ℤ (spectralGen 647) ∧
      (minpoly ℚ (spectralGen 647)).natDegree = 323 :=
  isIntegral_and_degree_sixHundredFortySeven

end Brockian.CosTraceNormSixHundredFortySeven
