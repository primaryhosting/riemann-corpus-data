import Mathlib

def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def Hyperperfect (k n : ℕ) : Prop := 0 < n ∧ k * sigma1 n = (k + 1) * n + (k - 1)

/-- A `k`-hyperperfect number (for `k ≥ 1`) is either `1` or at least `3`;
the only case to rule out is `n = 2`, where `sigma1 2 = 3` gives `3k = 3k + 1`.
(The hypothesis `1 ≤ k` is part of the requested statement but is not needed.) -/
theorem hyperperfect_pos_of_hyperperfect {k n : ℕ} (hk : 1 ≤ k)
    (h : Hyperperfect k n) : n = 1 ∨ 3 ≤ n := by
  obtain ⟨hn, he⟩ := h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · left; rfl
    · exfalso
      have h2 : sigma1 2 = 3 := by decide
      rw [h2] at he
      omega
  · right; exact h3

