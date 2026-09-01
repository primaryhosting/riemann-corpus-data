import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

/-- A chemical reaction with stoichiometric matrix `A` (rows indexed by chemical elements,
columns indexed by chemical species, entry `A i j` = number of atoms of element `i` in one
molecule of species `j`, counted with sign for reactants/products) *balances* if one can assign
strictly positive amounts `x j` to the species so that every element is conserved,
i.e. `A.mulVec x = 0`. -/
def Balances {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ j, 0 < x j) ∧ A.mulVec x = 0

/-- Any finite family of rationals admits a common positive integer denominator:
there is `d > 0` such that `d * x j` is an integer for every `j`. -/
theorem exists_common_denom {n : ℕ} (x : Fin n → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, ∃ z : ℤ, (d : ℚ) * x j = (z : ℚ) := by
  refine ⟨∏ j, (x j).den, Finset.prod_pos fun j _ => (x j).pos, fun j => ?_⟩
  obtain ⟨c, hc⟩ : ((x j).den : ℤ) ∣ ((∏ k, (x k).den : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.2 (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  refine ⟨(x j).num * c, ?_⟩
  have hxd : x j * ((x j).den : ℚ) = ((x j).num : ℚ) := Rat.mul_den_eq_num (x j)
  have hc' : ((∏ k, (x k).den : ℕ) : ℚ) = ((x j).den : ℚ) * (c : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hc
  rw [hc']
  push_cast
  rw [mul_assoc, mul_comm ((c : ℚ)) (x j), ← mul_assoc, mul_comm ((x j).den : ℚ) (x j), hxd]

/-- **Balance nullspace theorem.**  A chemical reaction balances (i.e. its stoichiometric
matrix has a strictly positive *rational* null vector) if and only if its stoichiometric matrix
has a strictly positive *integer* null vector. -/
theorem balance_nullspace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    Balances A ↔ ∃ z : Fin n → ℤ, (∀ j, 0 < z j) ∧ A.mulVec (fun j => (z j : ℚ)) = 0 := by
  constructor
  · rintro ⟨x, hxpos, hAx⟩
    obtain ⟨d, hd, hint⟩ := exists_common_denom x
    choose z hz using hint
    refine ⟨z, fun j => ?_, ?_⟩
    · have : (0 : ℚ) < (z j : ℚ) := by
        rw [← hz j]
        exact mul_pos (by exact_mod_cast hd) (hxpos j)
      exact_mod_cast this
    · have hfun : (fun j => ((z j : ℚ))) = (d : ℚ) • x := by
        funext j; simp [Pi.smul_apply, smul_eq_mul, ← hz j]
      rw [hfun, Matrix.mulVec_smul, hAx, smul_zero]
  · rintro ⟨z, hzpos, hAz⟩
    refine ⟨fun j => (z j : ℚ), fun j => ?_, hAz⟩
    show (0 : ℚ) < (z j : ℚ)
    exact_mod_cast hzpos j

/-- Sanity check: the reaction `2 H₂ + O₂ → 2 H₂O` balances.  Columns are the species
`H₂, O₂, H₂O` (products carry a minus sign) and rows are the elements `H, O`. -/
example : Balances !![(2 : ℚ), 0, -2; 0, 2, -1] := by
  refine ⟨![2, 1, 2], ?_, ?_⟩
  · decide +kernel
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Chem

