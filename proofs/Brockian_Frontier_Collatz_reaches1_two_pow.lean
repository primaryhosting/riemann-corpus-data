import Mathlib

namespace Brockian.Frontier.Collatz

/-! # A frontier moonshot, honestly scoped: the Collatz conjecture

The Collatz (3n+1) conjecture is open.  We do NOT claim to prove it.  We state it as
a target and bank the pieces that genuinely verify: an *infinite* family that
provably reaches 1 (every power of two), and a concrete hard-trajectory witness.
The open core is marked as a `def : Prop`, never as a theorem. -/

/-- One Collatz step. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` reaches 1 under iteration of `step`. -/
def Reaches1 (n : ℕ) : Prop := ∃ k, step^[k] n = 1

/-- **The Collatz conjecture — OPEN.**  Stated as a target, not proved here. -/
def CollatzConjecture : Prop := ∀ n, 1 ≤ n → Reaches1 n

/-! ## Verified pieces -/

/-- A power of two takes one halving step down to the next. -/
theorem step_two_pow (k : ℕ) : step (2 ^ (k + 1)) = 2 ^ k := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have heven : (2 ^ (k + 1)) % 2 = 0 := by rw [h2]; omega
  rw [step, if_pos heven, h2]
  omega

/-- **An infinite verified family.**  Every power of two reaches 1 — in exactly its
exponent many steps.  This is a genuine (non-finite) sub-result of Collatz. -/
theorem iterate_two_pow (k : ℕ) : step^[k] (2 ^ k) = 1 := by
  induction k with
  | zero => simp [step]
  | succ k ih =>
      rw [Function.iterate_succ_apply, step_two_pow, ih]

/-- Consequently every power of two satisfies Collatz. -/
theorem reaches1_two_pow (k : ℕ) : Reaches1 (2 ^ k) := ⟨k, iterate_two_pow k⟩

-- A concrete hard-trajectory witness: 27 famously climbs above 9000 before
-- descending, reaching 1 after 111 steps.
set_option maxRecDepth 4000 in
theorem reaches1_27 : Reaches1 27 := ⟨111, by decide⟩

end Brockian.Frontier.Collatz
