/-
  Brockian/Erdos236Lemmas.lean — referee-side machine check for the paper
  "A Prime–Dyadic Correlation Hypothesis and a Conditional Resolution of
   Erdős Problem #236".

  We formalize the paper's UNCONDITIONAL Lemma 2.2 (trivial upper bound)
  `f(n) ≤ ⌊log₂ n⌋ + 1`, using the paper's own definition of `f`.
  Nothing here is conditional on PDCH/BPRH or the FourierIdentity.

  Verified @ lean-4.32.0 (Mathlib). No sorry / admit / axiom.
-/
import Mathlib

namespace Brockian.Erdos236

/-- Erdős #236 representation-count function, verbatim from the paper's Lean
snippet: `f n` counts `k ≥ 0` with `2^k ≤ n` and `n − 2^k` prime. -/
def f (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun k => 2 ^ k ≤ n ∧ Nat.Prime (n - 2 ^ k))).card

/-- **Lemma 2.2 (Trivial upper bound), unconditional.**
For `n ≥ 2`, `f n ≤ Nat.log 2 n + 1` (i.e. `⌊log₂ n⌋ + 1`).

The whole content is: any `k` with `2^k ≤ n` satisfies `k ≤ ⌊log₂ n⌋`, and
each such `k` is counted at most once, so the count is at most the number of
admissible exponents. -/
theorem f_le_log (n : ℕ) (hn : 2 ≤ n) : f n ≤ Nat.log 2 n + 1 := by
  have hn0 : n ≠ 0 := by omega
  -- The filtered exponent set embeds into {0, 1, …, ⌊log₂ n⌋}.
  have hsub :
      (Finset.range (n + 1)).filter
          (fun k => 2 ^ k ≤ n ∧ Nat.Prime (n - 2 ^ k))
        ⊆ Finset.range (Nat.log 2 n + 1) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨_, hk2, _⟩ := hk
    rw [Finset.mem_range]
    have hle : k ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by norm_num) hk2
    omega
  calc
    f n ≤ (Finset.range (Nat.log 2 n + 1)).card := Finset.card_le_card hsub
    _ = Nat.log 2 n + 1 := Finset.card_range _

end Brockian.Erdos236
