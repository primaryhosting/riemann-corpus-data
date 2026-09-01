import Mathlib
/-!
# Braid-group relation algebra + Temperley–Lieb at the golden loop value (anyonic braiding).
Bare `import Mathlib`; uses Mathlib's `goldenRatio`. No non-core/Archive namespaces or invented
lemmas. TRUE; formalization of known braid/anyon algebra, not new physics.
-/
namespace BrockianQuantum
open Matrix Real

/-- **Braid relations are conjugation-invariant.** If braid generators `a, b` satisfy the braid
relation `aba = bab`, so do their conjugates `g a g⁻¹, g b g⁻¹` (a basis change of the anyonic
representation). -/
theorem braid_relation_conj {n : ℕ} (a b g : Matrix (Fin n) (Fin n) ℂ) [Invertible g]
    (h : a * b * a = b * a * b) :
    (g * a * ⅟ g) * (g * b * ⅟ g) * (g * a * ⅟ g)
      = (g * b * ⅟ g) * (g * a * ⅟ g) * (g * b * ⅟ g) := by
  -- Telescope the inner `⅟g * g = 1` factors: conjugation is multiplicative.
  have key : ∀ x y z : Matrix (Fin n) (Fin n) ℂ,
      (g * x * ⅟ g) * (g * y * ⅟ g) * (g * z * ⅟ g) = g * (x * y * z) * ⅟ g := by
    intro x y z
    simp only [Matrix.mul_assoc, Matrix.invOf_mul_cancel_left]
  rw [key, key, h]

/-- **Temperley–Lieb loop relation** at the Fibonacci loop value `δ = φ`: for any idempotent `P`
(`P² = P`), the generator `e := φ • P` satisfies `e² = φ • e` (equivalently `e² = δ e`). -/
theorem temperley_lieb_loop {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) :
    (goldenRatio • P) * (goldenRatio • P) = goldenRatio • (goldenRatio • P) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, hP]

end BrockianQuantum

