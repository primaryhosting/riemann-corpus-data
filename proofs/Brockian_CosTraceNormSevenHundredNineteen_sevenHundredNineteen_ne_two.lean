/-
  Brockian/CosTraceNormSevenHundredNineteen.lean — spectral generator at p = 719.

  [ℚ(2 cos 2π/719):ℚ] = 359 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredNineteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredNineteen : Nat.Prime 719 := by decide

theorem sevenHundredNineteen_ne_two : (719 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredNineteen : (minpoly ℚ (spectralGen 719)).natDegree = 359 :=
  real_subfield_degree prime_sevenHundredNineteen sevenHundredNineteen_ne_two

theorem isIntegral_spectralGen_sevenHundredNineteen : IsIntegral ℤ (spectralGen 719) :=
  isIntegral_spectralGen prime_sevenHundredNineteen

theorem isIntegral_spectralGen_sevenHundredNineteen_Q : IsIntegral ℚ (spectralGen 719) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredNineteen

theorem isIntegral_and_degree_sevenHundredNineteen :
    IsIntegral ℤ (spectralGen 719) ∧
      (minpoly ℚ (spectralGen 719)).natDegree = 359 :=
  ⟨isIntegral_spectralGen_sevenHundredNineteen, degree_sevenHundredNineteen⟩

theorem sevenHundredNineteen_pack :
    IsIntegral ℤ (spectralGen 719) ∧
      (minpoly ℚ (spectralGen 719)).natDegree = 359 :=
  isIntegral_and_degree_sevenHundredNineteen

end Brockian.CosTraceNormSevenHundredNineteen
