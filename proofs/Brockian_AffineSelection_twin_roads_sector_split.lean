import Mathlib

set_option autoImplicit false

namespace Brockian.AffineSelection

instance primeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- An affine map εx + a on ZMod p with ε = ±1. -/
def affine (ε : Units ℤ) (a : ZMod 5) : ZMod 5 → ZMod 5 := fun x => (ε : ℤ) • x + a
-- (5 specialized here; the general-p versions below quantify over p.)

/-! ## The general theorem: selection count for any odd prime -/

/-- The selection set: nonzero x whose image is nonzero. -/
def selSet (p : ℕ) [Fact p.Prime] (ε : ℤ) (a : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun x => x ≠ 0 ∧ ε • x + a ≠ 0)

/-- AS-1 (target): THE AFFINE SELECTION RULE. For an odd prime p and
ε = ±1: the count is p − 1 when f(0) = 0 (i.e. a = 0: f permutes the
units) and p − 2 otherwise (exactly one nonzero point is lost). -/
theorem affine_selection_card (p : ℕ) [hp : Fact p.Prime] (hodd : p ≠ 2)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (a : ZMod p) :
    (selSet p ε a).card = if a = 0 then p - 1 else p - 2 := by
  split_ifs with ha
  · -- Case a = 0
    subst ha
    have : selSet p ε 0 = Finset.univ.erase 0 := by
      ext x
      simp [selSet, Finset.mem_erase]
      rcases hε with rfl | rfl <;> simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  · -- Case a ≠ 0
    have hε_ne : (ε : ZMod p) = 1 ∨ (ε : ZMod p) = -1 := by
      rcases hε with rfl | rfl <;> simp
    have hε_unit : (ε : ZMod p) ≠ 0 := by rcases hε_ne with h | h <;> simp_all
    let x₀ := -(ε : ZMod p) • a
    have hx₀_ne : x₀ ≠ 0 := by simp [x₀]; rcases hε_ne with h | h <;> simp_all
    have hx₀_solve : ε • x₀ + a = 0 := by
      simp only [x₀]
      cases hε with
      | inl h => simp [h]
      | inr h => simp [h]
    have hε_smul : ∀ y : ZMod p, ε • y = (ε : ZMod p) * y := fun y => by simp [zsmul_eq_mul]
    have hx₀_solve' : (ε : ZMod p) * x₀ + a = 0 := by
      simp only [x₀]
      cases hε with
      | inl h => simp [h]
      | inr h => simp [h]
    have hset : selSet p ε a = Finset.univ.erase 0 \ {x₀} := by
      ext x
      simp only [selSet, Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, Finset.mem_singleton,
        Finset.mem_sdiff, true_and]
      rw [hε_smul]
      have key : (ε : ZMod p) * x + a = 0 ↔ x = x₀ := ⟨fun h => by
        have h1 : (ε : ZMod p) * x = (ε : ZMod p) * x₀ := by
          have := hx₀_solve'; simp_all [add_eq_zero_iff_eq_neg]
        exact mul_left_cancel₀ hε_unit h1, fun h => by
        rw [h]; exact hx₀_solve'⟩
      simp [key]
    rw [hset]
    have hx₀_in : x₀ ∈ Finset.univ.erase 0 := Finset.mem_erase.mpr ⟨hx₀_ne, Finset.mem_univ x₀⟩
    rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr hx₀_in)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Finset.card_singleton, ZMod.card]; omega

/-- AS-2 (target): translation reading — gap constraints. For a gap g,
the residues x with x and x + g both nonzero mod p number p − 1 if
p ∣ g, else p − 2. (ε = 1, a = g.) -/
theorem gap_selection (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (g : ZMod p) :
    (selSet p 1 g).card = if g = 0 then p - 1 else p - 2 := by
  exact affine_selection_card p hodd 1 (Or.inl rfl) g

/-- AS-3 (target): reflection reading — Goldbach constraints. For an
even sum c, the residues x with x and c − x both nonzero mod p number
p − 1 if p ∣ c, else p − 2. (ε = −1, a = c.) -/
theorem goldbach_selection (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (c : ZMod p) :
    (selSet p (-1) c).card = if c = 0 then p - 1 else p - 2 := by
  exact affine_selection_card p hodd (-1) (Or.inr rfl) c

/-! ## The pentagonal specialization: the 4-vs-3 dichotomy -/

/-- AS-4 (target, decidable): at p = 5, the Goldbach selection count is
4 when 5 ∣ c and 3 otherwise — the exact finite origin of the 4/3
local factor. -/
theorem pentagonal_goldbach :
    (∀ c : ZMod 5, c = 0 → (selSet 5 (-1) c).card = 4) ∧
    (∀ c : ZMod 5, c ≠ 0 → (selSet 5 (-1) c).card = 3) := by
  decide
/-! ## The quadratic refinement (AS-QR-1) -/

open scoped BigOperators

/-- The quadratic character is its own inverse. -/
lemma quadraticChar_inv_self {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    (quadraticChar F)⁻¹ = quadraticChar F := by
  apply MulChar.ext
  intro a
  rw [MulChar.inv_apply']
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hai : ((a : F)⁻¹) ≠ 0 := inv_ne_zero ha
  have hm : quadraticChar F ((a : F)⁻¹) * quadraticChar F (a : F) = 1 := by
    rw [← map_mul]
    simp [ha]
  rcases quadraticChar_dichotomy ha with h | h <;>
    rcases quadraticChar_dichotomy hai with hi | hi
  · exact hi.trans h.symm
  · rw [h, hi] at hm
    norm_num at hm
  · rw [h, hi] at hm
    norm_num at hm
  · exact hi.trans h.symm

/-- The self-Jacobi sum of the nontrivial quadratic character. -/
lemma quadraticChar_jacobi_self {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) :
    jacobiSum (quadraticChar F) (quadraticChar F) = -quadraticChar F (-1) := by
  have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hchar)
  simpa only [quadraticChar_inv_self] using h
/-- AS-QR-2 (target, decidable): the mod-5 sector split of the twin
roads — 1→3 and 2→4 cross sectors, 4→1 stays in the QR sector. -/
theorem twin_roads_sector_split :
    quadraticChar (ZMod 5) 1 * quadraticChar (ZMod 5) 3 = -1 ∧
    quadraticChar (ZMod 5) 2 * quadraticChar (ZMod 5) 4 = -1 ∧
    quadraticChar (ZMod 5) 4 * quadraticChar (ZMod 5) 1 = 1 := by
  decide

end Brockian.AffineSelection
