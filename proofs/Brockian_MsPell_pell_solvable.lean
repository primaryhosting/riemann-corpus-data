import Mathlib
namespace Brockian.MsPell
/-- Pell's equation is solvable: for a non-square positive d, x² − d·y² = 1 has a solution
    with y > 0. -/
theorem pell_solvable (d : ℕ) (hd : 0 < d) (hnsq : ¬ IsSquare d) :
    ∃ x y : ℤ, 0 < y ∧ x ^ 2 - (d : ℤ) * y ^ 2 = 1 := by
  obtain ⟨x, y, h, hy⟩ := Pell.exists_of_not_isSquare (d := (d : ℤ))
    (by exact_mod_cast hd)
    (by simpa using (Int.isSquare_natCast_iff (n := d)).not.2 hnsq)
  exact ⟨x, |y|, abs_pos.2 hy, by rw [sq_abs]; exact h⟩
end Brockian.MsPell

