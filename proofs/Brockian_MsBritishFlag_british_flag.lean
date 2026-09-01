import Mathlib
namespace Brockian.MsBritishFlag
/-- The British flag theorem: for a point P and a rectangle with corners A, A+u, A+u+v, A+v
    where u ⟂ v, dist(P,A)² + dist(P, A+u+v)² = dist(P, A+u)² + dist(P, A+v)². -/
theorem british_flag {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P A u v : E) (h : inner ℝ u v = (0 : ℝ)) :
    dist P A ^ 2 + dist P (A + u + v) ^ 2 = dist P (A + u) ^ 2 + dist P (A + v) ^ 2 := by
  simp only [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  have e1 : P - (A + u + v) = (P - A) - u - v := by abel
  have e2 : P - (A + u) = (P - A) - u := by abel
  have e3 : P - (A + v) = (P - A) - v := by abel
  rw [e1, e2, e3]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm u v, h]
  ring_nf
end Brockian.MsBritishFlag

