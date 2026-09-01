import Mathlib

namespace Brockian.MsNapoleon

/-!
# Napoleon's theorem (complex form)

The original statement in this file was

```
theorem napoleon (a b c : ℂ) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    let g₁ := (b + c + (c - b) * (-ω)) / 3
    let g₂ := (c + a + (a - c) * (-ω)) / 3
    let g₃ := (a + b + (b - a) * (-ω)) / 3
    g₁ + ω * g₂ + ω ^ 2 * g₃ = 0
```

which is **false**: the three expressions there are not the centroids of the erected
equilateral triangles, because the apex of the outward equilateral triangle on the side
`bc` is `b + (c - b) * (-ω)` (rotation of `c` about `b` by `-π/3`, since `-ω = e^{-iπ/3}`
for `ω = e^{2πi/3}`), not the bare vector `(c - b) * (-ω)`; the base point `b` was dropped.
Indeed one computes

  `(b + c + (c-b)*(-ω))/3 + ω*(c + a + (a-c)*(-ω))/3 + ω^2*(a + b + (b-a)*(-ω))/3`
    `= -(ω^2*a + b + ω*c)/3`,

which is `-ω^2/3 ≠ 0` for `a = 1, b = c = 0` (see `napoleon_original_false` below).

The corrected statement, with the same mathematical content (Napoleon's theorem), uses the
genuine centroids `gᵢ = (vertex + vertex + apex) / 3` and is proved below.
-/

/-- The apex of the outward equilateral triangle erected on the segment from `p` to `q`:
the rotation of `q` about `p` by `-π/3`, as `-ω = e^{-iπ/3}` when `ω = e^{2πi/3}`. -/
def apex (ω p q : ℂ) : ℂ := p + (q - p) * (-ω)

/-- Napoleon's theorem (complex form): the centroids of the outward equilateral triangles
erected on the sides of any triangle `a, b, c ∈ ℂ` themselves form an equilateral triangle.
With `ω` a primitive cube root of unity (`ω ^ 2 + ω + 1 = 0`), the three centroids
`g₁, g₂, g₃` satisfy the standard equilaterality criterion `g₁ + ω * g₂ + ω ^ 2 * g₃ = 0`. -/
theorem napoleon (a b c : ℂ) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    let g₁ := (b + c + apex ω b c) / 3
    let g₂ := (c + a + apex ω c a) / 3
    let g₃ := (a + b + apex ω a b) / 3
    g₁ + ω * g₂ + ω ^ 2 * g₃ = 0 := by
  simp only [apex]
  linear_combination ((a * ω - b * ω + 2 * b + c) / 3) * hω

/-- A primitive cube root of unity exists in `ℂ`. -/
theorem exists_primitive_cube_root : ∃ ω : ℂ, ω ^ 2 + ω + 1 = 0 := by
  refine ⟨⟨-1 / 2, Real.sqrt 3 / 2⟩, ?_⟩
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]

/-- The originally stated identity is false. -/
theorem napoleon_original_false :
    ¬ ∀ (a b c ω : ℂ), ω ^ 2 + ω + 1 = 0 →
      (b + c + (c - b) * (-ω)) / 3 + ω * ((c + a + (a - c) * (-ω)) / 3)
        + ω ^ 2 * ((a + b + (b - a) * (-ω)) / 3) = 0 := by
  intro h
  obtain ⟨ω, hω⟩ := exists_primitive_cube_root
  have h1 := h 1 0 0 ω hω
  have hsq : ω ^ 2 = 0 := by linear_combination -3 * h1 + ω * hω
  have hω0 : ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  rw [hω0] at hω
  norm_num at hω

end Brockian.MsNapoleon

