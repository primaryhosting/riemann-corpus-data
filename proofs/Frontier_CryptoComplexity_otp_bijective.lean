import Mathlib
namespace Frontier.CryptoComplexity
open Function

/-- The one-time pad map `k ↦ m ^^^ k` is a bijection, since it is an involution. -/
theorem otp_bijective (n : ℕ) (m : BitVec n) : Bijective (fun k : BitVec n => m ^^^ k) := by
  refine Function.Involutive.bijective (fun k => ?_)
  show m ^^^ (m ^^^ k) = k
  rw [← BitVec.xor_assoc]
  simp

/-- Pigeonhole: a map into a strictly smaller finite type cannot be injective. -/
theorem hash_collision {A B : Type*} [Fintype A] [Fintype B]
    (h : Fintype.card B < Fintype.card A) (f : A → B) : ¬ Injective f := fun hf =>
  absurd (Fintype.card_le_of_injective f hf) (not_le.mpr h)

/-- There are `2 ^ (2 ^ n)` Boolean functions on `n` bits. -/
theorem boolean_function_count (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  simp

end Frontier.CryptoComplexity

