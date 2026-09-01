import Mathlib
/-!
# Batch 12 — cyclotomic-5 and golden-ratio identities (Brockian five). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Polynomial Real

set_option autoImplicit false

/- In the Mathlib version used here, `goldConj` is called `Real.goldenConj`; the local
notation below lets the statements below be written exactly as given, while referring to
Mathlib's definition. -/
local notation "goldConj" => Real.goldenConj

theorem golden_eq : goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
theorem goldConj_eq : goldConj = (1 - Real.sqrt 5) / 2 := rfl
theorem golden_add_conj : goldenRatio + goldConj = 1 := Real.goldenRatio_add_goldenConj
theorem golden_mul_conj : goldenRatio * goldConj = -1 := Real.goldenRatio_mul_goldenConj
theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
theorem cyclotomic_five :
    Polynomial.cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [cyclotomic_prime]
  simp [Finset.sum_range_succ]
  ring
theorem one_lt_golden : 1 < goldenRatio := Real.one_lt_goldenRatio
end BrockianQuantum

