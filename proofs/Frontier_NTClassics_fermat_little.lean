import Mathlib
namespace Frontier.NTClassics

theorem fermat_little (p : ℕ) (hp : p.Prime) (a : ℤ) : a^p ≡ a [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : ((a ^ p : ℤ) : ZMod p) = ((a : ℤ) : ZMod p) := by
    push_cast
    exact ZMod.pow_card (a : ZMod p)
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h

theorem wilson (p : ℕ) (hp : p.Prime) : ((p-1).factorial : ZMod p) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ZMod.wilsons_lemma p

theorem infinite_primes_3_mod_4 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have h := Nat.infinite_setOf_prime_and_modEq (q := 4) (a := 3) (by norm_num) (by decide)
  convert h using 3

end Frontier.NTClassics

