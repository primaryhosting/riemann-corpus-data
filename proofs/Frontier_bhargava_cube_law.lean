/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Bhargava cubes and their three pairs of `2 × 2` slices

A *Bhargava cube* is an element of `ℤ² ⊗ ℤ² ⊗ ℤ²`, i.e. an eight-tuple of integers
`(a, b, c, d, e, f, g, h)` placed at the vertices of a cube:

```
        e ------- f
       /|        /|
      a ------- b |
      | g ------|-h
      |/        |/
      c ------- d
```

Cutting the cube by planes orthogonal to each of the three coordinate directions produces
three pairs of `2 × 2` integer matrices

* `(M₁, N₁) = ((a b; c d), (e f; g h))`  (front/back),
* `(M₂, N₂) = ((a c; e g), (b d; f h))`  (left/right),
* `(M₃, N₃) = ((a e; b f), (c g; d h))`  (top/bottom),

and each pair yields the binary quadratic form `Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`.
-/

/-- The binary quadratic form `Q (x, y) = -det (M x - N y)` attached to a pair of `2 × 2`
integer matrices `M = (m₁₁ m₁₂; m₂₁ m₂₂)` and `N = (n₁₁ n₁₂; n₂₁ n₂₂)`. -/
def sliceForm (m₁₁ m₁₂ m₂₁ m₂₂ n₁₁ n₁₂ n₂₁ n₂₂ x y : ℤ) : ℤ :=
  -((m₁₁ * x - n₁₁ * y) * (m₂₂ * x - n₂₂ * y) - (m₁₂ * x - n₁₂ * y) * (m₂₁ * x - n₂₁ * y))

/-- The first quadratic form `Q₁` of the Bhargava cube `(a, b, c, d, e, f, g, h)`,
coming from the front/back slicing `(M₁, N₁) = ((a b; c d), (e f; g h))`. -/
def Q₁ (a b c d e f g h : ℤ) : ℤ → ℤ → ℤ := sliceForm a b c d e f g h

/-- The second quadratic form `Q₂` of the Bhargava cube `(a, b, c, d, e, f, g, h)`,
coming from the left/right slicing `(M₂, N₂) = ((a c; e g), (b d; f h))`. -/
def Q₂ (a b c d e f g h : ℤ) : ℤ → ℤ → ℤ := sliceForm a c e g b d f h

/-- The third quadratic form `Q₃` of the Bhargava cube `(a, b, c, d, e, f, g, h)`,
coming from the top/bottom slicing `(M₃, N₃) = ((a e; b f), (c g; d h))`. -/
def Q₃ (a b c d e f g h : ℤ) : ℤ → ℤ → ℤ := sliceForm a e b f c g d h

/-- The discriminant `B ^ 2 - 4 * A * C` of a binary quadratic form
`Q (x, y) = A * x ^ 2 + B * x * y + C * y ^ 2`, extracted from `Q` by evaluation:
`A = Q 1 0`, `C = Q 0 1` and `B = Q 1 1 - Q 1 0 - Q 0 1`. -/
def disc (Q : ℤ → ℤ → ℤ) : ℤ := (Q 1 1 - Q 1 0 - Q 0 1) ^ 2 - 4 * Q 1 0 * Q 0 1

/-!
## The Bhargava cube law

`bhargava_cube_law` below packages the base case of Bhargava's cube law:

1. **(Common discriminant.)** For every cube, the three slice forms `Q₁, Q₂, Q₃` have the
   same discriminant.  This is what makes the cube law a statement inside a single form
   class group.

2. **(Concordant / Dirichlet cube.)** The explicit cube `(0, A, 1, 0, C, -B, 0, -m)` has

   * `Q₁ = A x² + B x y + C m y²`,
   * `Q₂ = C x² + B x y + A m y²`,
   * `Q₃ = A C x² - B x y + m y²`,

   the classical *concordant* triple of forms of common discriminant `B² - 4 A C m`.
   (Taking `A = C = 1`, `B = 0`, `m = n` gives the identity cube, all of whose three
   forms are the principal form `x² + n y²` of discriminant `-4 n`.)

3. **(Gauss composition.)** For that cube the Gauss/Dirichlet composition identity holds:
   `Q₁` composed with `Q₂` is the *opposite* form `Q₃ (x, -y)` of `Q₃`, witnessed by the
   explicit integral bilinear substitution
   `(x₁, y₁, x₂, y₂) ↦ (x₁ x₂ - m y₁ y₂, A x₁ y₂ + C y₁ x₂ + B y₁ y₂)`.
   In other words `Q₁ · Q₂ · Q₃ = 1` in the class group, which is exactly Bhargava's
   cube law, and it recovers Gauss composition of binary quadratic forms.
-/

/-- **Bhargava's cube law (base case).**

Bhargava's cube gives a composition law on (triples of) binary quadratic forms recovering
Gauss composition.  Concretely:

* the three slice forms of an arbitrary integral cube share a common discriminant;
* the concordant cube `(0, A, 1, 0, C, -B, 0, -m)` slices into the classical triple
  `A x² + B x y + C m y²`, `C x² + B x y + A m y²`, `A C x² - B x y + m y²`;
* the product of the first two forms is represented by the opposite of the third under an
  explicit integral bilinear substitution — i.e. `Q₁ ∘ Q₂ = Q₃⁻¹`, so `Q₁ Q₂ Q₃ = 1`,
  which is precisely Gauss composition. -/
theorem bhargava_cube_law :
    (∀ a b c d e f g h : ℤ,
        disc (Q₁ a b c d e f g h) = disc (Q₂ a b c d e f g h) ∧
          disc (Q₂ a b c d e f g h) = disc (Q₃ a b c d e f g h)) ∧
      (∀ A B C m : ℤ,
          (∀ x y : ℤ, Q₁ 0 A 1 0 C (-B) 0 (-m) x y = A * x ^ 2 + B * x * y + C * m * y ^ 2) ∧
            (∀ x y : ℤ, Q₂ 0 A 1 0 C (-B) 0 (-m) x y = C * x ^ 2 + B * x * y + A * m * y ^ 2) ∧
              (∀ x y : ℤ,
                  Q₃ 0 A 1 0 C (-B) 0 (-m) x y = A * C * x ^ 2 - B * x * y + m * y ^ 2) ∧
                disc (Q₁ 0 A 1 0 C (-B) 0 (-m)) = B ^ 2 - 4 * (A * C * m)) ∧
        (∀ A B C m x₁ y₁ x₂ y₂ : ℤ,
            (A * x₁ ^ 2 + B * x₁ * y₁ + C * m * y₁ ^ 2) *
                (C * x₂ ^ 2 + B * x₂ * y₂ + A * m * y₂ ^ 2) =
              Q₃ 0 A 1 0 C (-B) 0 (-m) (x₁ * x₂ - m * y₁ * y₂)
                (-(A * x₁ * y₂ + C * y₁ * x₂ + B * y₁ * y₂))) := by
  refine ⟨fun a b c d e f g h => ⟨?_, ?_⟩, fun A B C m => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [disc, Q₁, Q₂, sliceForm]; ring
  · simp only [disc, Q₂, Q₃, sliceForm]; ring
  · intro x y; simp only [Q₁, sliceForm]; ring
  · intro x y; simp only [Q₂, sliceForm]; ring
  · intro x y; simp only [Q₃, sliceForm]; ring
  · simp only [disc, Q₁, sliceForm]; ring
  · intro A B C m x₁ y₁ x₂ y₂; simp only [Q₃, sliceForm]; ring

end Frontier

