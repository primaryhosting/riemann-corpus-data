import Mathlib
namespace Brockian.MsDerangement
/-- Closed form for derangements: Dₙ = n!·∑_{k=0}^{n} (−1)ᵏ/k!.

(Statement adjusted only in that Mathlib's function is `numDerangements`, in the root
namespace, rather than `Nat.numDerangements`.) -/
theorem derangement_closed (n : ℕ) :
    (numDerangements n : ℚ)
      = (n.factorial : ℚ) * ∑ k ∈ Finset.range (n + 1), (-1) ^ k / (k.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hq : (numDerangements (n + 1) : ℚ) = (n + 1) * (numDerangements n : ℚ) - (-1) ^ n := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (numDerangements_succ n)
    have hf : ((n + 1).factorial : ℚ) = (n + 1) * (n.factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfne : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [Finset.sum_range_succ, mul_add, hf, mul_assoc, ← ih, hq]
    field_simp
    ring

end Brockian.MsDerangement

