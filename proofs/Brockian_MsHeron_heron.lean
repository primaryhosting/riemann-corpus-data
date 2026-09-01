import Mathlib
namespace Brockian.MsHeron

/- The original statement below is stated for `A B C : ℝ × ℝ`.  In Mathlib the product
   type `ℝ × ℝ` carries the *sup* metric, i.e. `dist X Y = max |X.1 - Y.1| |X.2 - Y.2|`,
   not the Euclidean metric, so as literally stated the identity is false (e.g. for
   `A = (0,0)`, `B = (1,0)`, `C = (0,1)` one gets `16·area² = 4` but the right-hand side
   evaluates to `2+2+2-1-1-1 = 3`).  It is preserved here, commented out, and replaced
   below by the same statement over `EuclideanSpace ℝ (Fin 2)`, where `dist` is the
   Euclidean distance intended by the informal description.

theorem heron' (A B C : ℝ × ℝ) :
    let a := dist B C; let b := dist C A; let c := dist A B
    let area := |(B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)| / 2
    16 * area ^ 2 = 2*a^2*b^2 + 2*b^2*c^2 + 2*c^2*a^2 - a^4 - b^4 - c^4
-/

/-- Heron's formula (algebraic form): 16·Area² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴, where
    a,b,c are the (Euclidean) side lengths and Area = ½|det(B−A, C−A)| for
    A,B,C in the Euclidean plane. -/
theorem heron (A B C : EuclideanSpace ℝ (Fin 2)) :
    let a := dist B C; let b := dist C A; let c := dist A B
    let area := |(B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)| / 2
    16 * area ^ 2 = 2*a^2*b^2 + 2*b^2*c^2 + 2*c^2*a^2 - a^4 - b^4 - c^4 := by
  intro a b c area
  have key : ∀ X Y : EuclideanSpace ℝ (Fin 2),
      dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
    intro X Y
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt]
    · simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    · positivity
  have ha : a ^ 2 = (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := key B C
  have hb : b ^ 2 = (C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2 := key C A
  have hc : c ^ 2 = (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := key A B
  have harea : area ^ 2
      = ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)) ^ 2 / 4 := by
    simp only [area, div_pow, sq_abs]; norm_num
  have h4 : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := by intro x; ring
  rw [h4, h4, h4, ha, hb, hc, harea]
  ring

end Brockian.MsHeron

