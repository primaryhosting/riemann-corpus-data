import Mathlib
namespace Brockian.MsThue

/-- Pigeonhole step: there are more than `n` pairs `(i, j)` with `0 ≤ i, j ≤ √n`, so two
    distinct such pairs give the same value of `i - a * j` in `ZMod n`. -/
private lemma thue_pigeonhole (n a : ℕ) (hn : 1 < n) :
    ∃ p q : Fin (Nat.sqrt n + 1) × Fin (Nat.sqrt n + 1), p ≠ q ∧
      ((p.1 : ZMod n) - a * (p.2 : ZMod n) = (q.1 : ZMod n) - a * (q.2 : ZMod n)) := by
  -- The number of pairs is `(√n + 1)^2 > n`, the number of values in `ZMod n`.
  haveI : NeZero n := ⟨by omega⟩
  have hcard :
      Fintype.card (ZMod n) < Fintype.card (Fin (Nat.sqrt n + 1) × Fin (Nat.sqrt n + 1)) := by
    simpa [ZMod.card] using Nat.lt_succ_sqrt n
  exact Fintype.exists_ne_map_eq_of_card_lt
    (fun p => (p.1 : ZMod n) - a * (p.2 : ZMod n)) hcard

/-- Thue's lemma: for n > 1 and any a, there exist x, y not both zero with |x|,|y| ≤ √n and
    x ≡ a·y (mod n). -/
theorem thue_lemma (n a : ℕ) (hn : 1 < n) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ Nat.sqrt n ∧ y.natAbs ≤ Nat.sqrt n ∧
      (n : ℤ) ∣ (x - a * y) := by
  obtain ⟨p, q, hpq, h⟩ := thue_pigeonhole n a hn
  refine ⟨(p.1 : ℤ) - (q.1 : ℤ), (p.2 : ℤ) - (q.2 : ℤ), ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    apply hpq
    have e1 : (p.1 : ℕ) = (q.1 : ℕ) := by exact_mod_cast sub_eq_zero.mp h1
    have e2 : (p.2 : ℕ) = (q.2 : ℕ) := by exact_mod_cast sub_eq_zero.mp h2
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · have h1 : (p.1 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp p.1.isLt
    have h2 : (q.1 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp q.1.isLt
    omega
  · have h1 : (p.2 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp p.2.isLt
    have h2 : (q.2 : ℕ) ≤ Nat.sqrt n := Nat.lt_succ_iff.mp q.2.isLt
    omega
  · have : (((((p.1 : ℤ) - (q.1 : ℤ)) - a * ((p.2 : ℤ) - (q.2 : ℤ))) : ℤ) : ZMod n) = 0 := by
      push_cast
      linear_combination h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp this

end Brockian.MsThue

