import Mathlib
namespace C2.NT4

/-- The order of a unit in `ZMod p` divides `p - 1`, the cardinality of `(ZMod p)ˣ`. -/
theorem order_dvd_card (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : orderOf a ∣ (p - 1) := by
  rw [← ZMod.card_units p]
  exact orderOf_dvd_card

/-- The multiplicative group of `ZMod p` is cyclic, so it has a generator of order `p - 1`. -/
theorem exists_primitive_root (p : ℕ) [Fact p.Prime] : ∃ g : (ZMod p)ˣ, orderOf g = p - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  exact ⟨g, by rwa [Nat.card_eq_fintype_card, ZMod.card_units p] at hg⟩

/-- Fermat's little theorem, stated for units of `ZMod p`. -/
theorem fermat_little_units (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← ZMod.card_units p]
  exact pow_card_eq_one

end C2.NT4

