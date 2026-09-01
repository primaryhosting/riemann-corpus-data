import Mathlib
namespace Brockian.GaussWilson
/-- Gauss's generalization of Wilson's theorem: the product of the units of ℤ/nℤ equals −1
    when n has a primitive root (n = 1,2,4,p^k,2p^k) and +1 otherwise. Here the clean universal
    fact: the product of all units of ℤ/nℤ is its own inverse, i.e. squares to 1. -/
theorem prod_units_sq_eq_one (n : ℕ) [NeZero n] :
    (∏ u : (ZMod n)ˣ, u) ^ 2 = 1 := by
  -- The map `u ↦ u⁻¹` is a bijection of the (finite, commutative) group of units,
  -- so the product of all units equals its own inverse.
  have h : (∏ u : (ZMod n)ˣ, u) = (∏ u : (ZMod n)ˣ, u)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact (Fintype.prod_equiv (Equiv.inv (ZMod n)ˣ) _ _ (fun _ => rfl)).symm
  rw [sq]
  nth_rewrite 2 [h]
  simp
end Brockian.GaussWilson

