import Mathlib
namespace Brockian.Niven
/-- Niven's theorem: if θ = qπ for rational q and cos θ is rational, then cos θ ∈ {0, ±1/2, ±1}. -/
theorem niven_cos (q r : ℚ) (h : Real.cos (q * Real.pi) = (r : ℝ)) :
    Real.cos (q * Real.pi) = 0 ∨ Real.cos (q * Real.pi) = 1 ∨ Real.cos (q * Real.pi) = -1
      ∨ Real.cos (q * Real.pi) = 1 / 2 ∨ Real.cos (q * Real.pi) = -(1 / 2) := by
  have key := niven (θ := (q : ℝ) * Real.pi) ⟨q, rfl⟩ ⟨r, h⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at key
  rcases key with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> norm_num
end Brockian.Niven

