import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/
private lemma exp_eq_stdAddChar (p : ℕ) [NeZero p] (k : ZMod p) :
    Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ))
      = ZMod.stdAddChar (k ^ 2) := by
  simp [ZMod.stdAddChar]
  rw [ZMod.toCircle_apply]
  rw [Complex.exp_eq_exp_iff_exists_int]
  have h : (k ^ 2).val ≡ k.val ^ 2 [MOD p] := by
    simp [Nat.ModEq]
    have h2 : ((k.val ^ 2) : ZMod p) = k ^ 2 := by simp
    have h3 : (k ^ 2).val = ((k.val : ZMod p) ^ 2).val := by rw [h2]
    have h4 : ((k.val : ZMod p) ^ 2).val = ((k.val ^ 2 : ℕ) : ZMod p).val := by
      rw [← Nat.cast_pow]
    rw [h3, h4, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_refl p)]
  have h' : (p : ℤ) ∣ (k.val ^ 2 - (k ^ 2).val) := h.dvd
  obtain ⟨n, hn⟩ := h'
  use n
  have hk : (k.val : ℤ) ^ 2 = (k ^ 2).val + p * n := by linarith
  have hk' : (k.val : ℂ) ^ 2 = (k ^ 2).val + p * (n : ℂ) := by exact_mod_cast hk
  have hk'' : k.cast ^ 2 = (k ^ 2).val + p * (n : ℂ) := by
    have : k.cast = (k.val : ℂ) := by simp only [ZMod.natCast_val]
    rw [this]
    exact hk'
  rw [hk'']
  field_simp [NeZero.ne p]

/-- Complex conjugation of the standard additive character. -/
private lemma conj_stdAddChar (p : ℕ) [NeZero p] [Fact p.Prime] (x : ZMod p) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simp [ZMod.stdAddChar, ZMod.toCircle, AddCircle.toCircle_addChar]
  -- goal: (starRingEnd ℂ) ↑(ZMod.toAddCircle x).toCircle = ↑(-ZMod.toAddCircle x).toCircle
  trans (↑(AddCircle.toCircle (ZMod.toAddCircle x)))⁻¹
  · -- Use that conj(z) = z⁻¹ for |z| = 1
    have hnorm : ‖(AddCircle.toCircle (ZMod.toAddCircle x) : ℂ)‖ = 1 := by simp
    -- conj(z) = z⁻¹ for |z| = 1
    have h1 : (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ) * (starRingEnd ℂ) (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have h2 : (starRingEnd ℂ) (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ) = (AddCircle.toCircle (ZMod.toAddCircle x) : ℂ)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h1
    exact h2
  · rw [AddCircle.toCircle_neg]
    rfl

/-- For an odd prime `p`, multiplication by `2` is injective on `ZMod p`. -/
private lemma two_mul_eq_zero_iff (p : ℕ) [Fact p.Prime] (hp : Odd p) (m : ZMod p) :
    2 * m = 0 ↔ m = 0 := by
  have hp2 : p ≠ 2 := by rintro rfl; rcases hp with ⟨k, hk⟩; omega
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h2
    · exact h'
  · rintro rfl; ring

/-- Orthogonality: the shifted character sums to `p` at `m = 0` and to `0` otherwise. -/
private lemma sum_shift (p : ℕ) [Fact p.Prime] (hp : Odd p) (m : ZMod p) :
    ∑ l : ZMod p, (ZMod.stdAddChar (2 * m * l) : ℂ) = if m = 0 then (p : ℂ) else 0 := by
  classical
  have key := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) (2 * m)
    (ZMod.isPrimitive_stdAddChar p)
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hcomm : ∀ l : ZMod p, l * (2 * m) = 2 * m * l := fun l => mul_comm _ _
  simp_rw [hcomm] at key
  by_cases hm : m = 0
  · rw [key, hcard, if_pos (by simp [hm]), if_pos hm]
  · have h2m : 2 * m ≠ 0 := fun h => hm ((two_mul_eq_zero_iff p hp m).mp h)
    rw [key, if_neg h2m, if_neg hm, Nat.cast_zero]

/-- Expanding `S * conj S` and reindexing `k = l + m`. -/
private lemma sum_mul_conj_sum (p : ℕ) [Fact p.Prime] :
    (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) *
        (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ))
      = ∑ m : ZMod p, (ZMod.stdAddChar (m ^ 2) : ℂ) * ∑ l : ZMod p, (ZMod.stdAddChar (2 * m * l) : ℂ) := by
  -- First, simplify the conjugate of the sum
  have h1 : (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) =
            ∑ k : ZMod p, (ZMod.stdAddChar (-(k ^ 2)) : ℂ) := by
    rw [map_sum]
    congr 1
    ext k
    exact conj_stdAddChar p (k ^ 2)
  rw [h1]
  -- Now we have a product of two sums, convert to double sum
  rw [Finset.sum_mul_sum]
  -- Combine the character values using the homomorphism property
  have h2 : ∀ i j : ZMod p, ZMod.stdAddChar (i ^ 2) * ZMod.stdAddChar (-j ^ 2) =
            ZMod.stdAddChar (i ^ 2 - j ^ 2) := by
    intro i j
    rw [sub_eq_add_neg]
    have h := (AddChar.toAddMonoidHom ZMod.stdAddChar).map_add (i ^ 2) (-j ^ 2)
    simp only [AddChar.toAddMonoidHom_apply] at h
    exact (congrArg Additive.toMul h).symm
  -- Rewrite using h2
  simp_rw [h2]
  -- Reindex: let m = x - x_1, so x = m + x_1
  -- x² - x_1² = (m + x_1)² - x_1² = m² + 2mx_1
  have reindex : ∀ x x_1 : ZMod p, x ^ 2 - x_1 ^ 2 = (x - x_1) ^ 2 + 2 * (x - x_1) * x_1 := by
    intro x x_1; ring
  simp_rw [reindex]
  -- Swap sums: ∑ x, ∑ x_1 → ∑ x_1, ∑ x
  rw [Finset.sum_comm]
  -- Now: ∑ x_1, ∑ x, stdAddChar((x - x_1)² + 2*(x - x_1)*x_1)
  -- Reindex inner sum: let m = x - x_1
  have reindex_inner : ∀ x_1 : ZMod p, ∑ x : ZMod p, ZMod.stdAddChar ((x - x_1) ^ 2 + 2 * (x - x_1) * x_1) =
      ∑ m : ZMod p, ZMod.stdAddChar (m ^ 2 + 2 * m * x_1) := by
    intro x_1
    rw [← Equiv.sum_comp (Equiv.addRight x_1)]
    simp [Equiv.addRight]
  simp_rw [reindex_inner]
  -- Now: ∑ x_1, ∑ m, stdAddChar(m² + 2*m*x_1)
  have h3 : ∀ m x_1 : ZMod p, ZMod.stdAddChar (m ^ 2 + 2 * m * x_1) =
            ZMod.stdAddChar (m ^ 2) * ZMod.stdAddChar (2 * m * x_1) := by
    intro m x_1
    have h := (AddChar.toAddMonoidHom ZMod.stdAddChar).map_add (m ^ 2) (2 * m * x_1)
    simp only [AddChar.toAddMonoidHom_apply] at h
    exact congrArg Additive.toMul h
  simp_rw [h3]
  -- Swap sums: now outer is m, inner is x_1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]

/-- The squared modulus of the quadratic Gauss sum equals `p`. -/
private lemma gauss_sum_mul_conj (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) *
        (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) = (p : ℂ) := by
  rw [sum_mul_conj_sum]
  simp_rw [sum_shift p hp]
  simp

/-- The quadratic Gauss sum has magnitude √p: for an odd prime p,
    |∑_{k ∈ ℤ/p} exp(2πi k²/p)|² = p.

    (`Complex.abs` no longer exists in current Mathlib; the norm `‖·‖` on `ℂ` is the
    same function.) -/
theorem gauss_sum_abs_sq (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ‖∑ k : ZMod p,
      Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ))‖ ^ 2 = (p : ℝ) := by
  -- First, rewrite the sum using exp_eq_stdAddChar
  have h_sum_eq : ∑ k : ZMod p, Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ)) =
      ∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ) := by
    apply Finset.sum_congr rfl
    intro k _
    exact exp_eq_stdAddChar p k
  -- Rewrite the goal using h_sum_eq
  rw [h_sum_eq]
  -- Use the fact that ‖z‖² = z * conj(z) for complex numbers
  have h_norm_sq : ((‖∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) * (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) := by
    rw [Complex.sq_norm, mul_comm]
    exact mod_cast Complex.normSq_eq_conj_mul_self
  have h_cast : ((‖∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)‖ ^ 2 : ℝ) : ℂ) = (p : ℂ) := by
    rw [h_norm_sq, gauss_sum_mul_conj p hp]
  exact mod_cast h_cast

end Brockian.MsGaussSum

