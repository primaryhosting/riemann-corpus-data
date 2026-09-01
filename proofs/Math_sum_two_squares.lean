import Mathlib

/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Squares are `0` or `1` mod `4`. -/
private lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have h : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hn : (n % 4) <;> simp [h]

/-- **Fermat's two-square theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 [MOD 4]`.

The hard direction (existence) is `Nat.Prime.sq_add_sq` from Mathlib; the easy direction
follows since squares are `0` or `1` modulo `4`. -/
theorem sum_two_squares {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact Or.inl h2
    · right
      have ha := sq_mod_four a
      have hb := sq_mod_four b
      have : (a ^ 2 + b ^ 2) % 4 % 2 = 1 := by omega
      omega
  · rintro (rfl | h1)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      exact Nat.Prime.sq_add_sq (by omega)

end Math

