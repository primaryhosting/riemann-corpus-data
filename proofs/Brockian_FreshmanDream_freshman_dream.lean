import Mathlib
namespace Brockian.FreshmanDream
/-- The "freshman's dream" modulo a prime: (a+b)^p ≡ a^p + b^p (mod p). -/
theorem freshman_dream (p a b : ℕ) (hp : p.Prime) :
    (a + b) ^ p ≡ a ^ p + b ^ p [MOD p] := by
  haveI := Fact.mk hp
  have h : (((a + b) ^ p : ℕ) : ZMod p) = ((a ^ p + b ^ p : ℕ) : ZMod p) := by
    push_cast
    exact add_pow_char _ _ _
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
end Brockian.FreshmanDream

