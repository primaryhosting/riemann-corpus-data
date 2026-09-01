/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A Bhargava cube: a `2 × 2 × 2` array of integers.  We label the eight entries as in
Bhargava's *Higher composition laws I*: the front face is `a b / c d` and the back face is
`e f / g h`. -/
structure Cube where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ
  deriving DecidableEq

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure QF where
  A : ℤ
  B : ℤ
  C : ℤ
  deriving DecidableEq

namespace QF

/-- Evaluation of a binary quadratic form. -/
def eval (q : QF) (x y : ℤ) : ℤ := q.A * x ^ 2 + q.B * x * y + q.C * y ^ 2

/-- The discriminant `B² - 4AC`. -/
def disc (q : QF) : ℤ := q.B ^ 2 - 4 * q.A * q.C

/-- The opposite (inverse) form `A x² - B x y + C y²`; it represents the inverse class. -/
def op (q : QF) : QF := ⟨q.A, -q.B, q.C⟩

@[simp] lemma op_eval (q : QF) (x y : ℤ) : q.op.eval x y = q.eval x (-y) := by
  simp [eval, op]

end QF

namespace Cube

/-! ### The three pairs of `2 × 2` matrices obtained by slicing the cube -/

/-- First slicing, front face. -/
def M₁ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.b; K.c, K.d]
/-- First slicing, back face. -/
def N₁ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.e, K.f; K.g, K.h]
/-- Second slicing, first slice. -/
def M₂ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.c; K.e, K.g]
/-- Second slicing, second slice. -/
def N₂ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.b, K.d; K.f, K.h]
/-- Third slicing, first slice. -/
def M₃ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.e; K.b, K.f]
/-- Third slicing, second slice. -/
def N₃ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.c, K.g; K.d, K.h]

/-- The first form of the cube, `Q₁(x,y) = -det(M₁ x + N₁ y)`. -/
def Q₁ (K : Cube) : QF :=
  ⟨-(K.a * K.d - K.b * K.c),
   -(K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f),
   -(K.e * K.h - K.f * K.g)⟩

/-- The second form of the cube, `Q₂(x,y) = -det(M₂ x + N₂ y)`. -/
def Q₂ (K : Cube) : QF :=
  ⟨-(K.a * K.g - K.c * K.e),
   -(K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e),
   -(K.b * K.h - K.d * K.f)⟩

/-- The third form of the cube, `Q₃(x,y) = -det(M₃ x + N₃ y)`. -/
def Q₃ (K : Cube) : QF :=
  ⟨-(K.a * K.f - K.b * K.e),
   -(K.a * K.h + K.c * K.f - K.d * K.e - K.b * K.g),
   -(K.c * K.h - K.d * K.g)⟩

lemma Q₁_eq_neg_det (K : Cube) (x y : ℤ) :
    K.Q₁.eval x y = -(x • K.M₁ + y • K.N₁).det := by
  simp [QF.eval, Q₁, M₁, N₁, Matrix.det_fin_two]
  ring

lemma Q₂_eq_neg_det (K : Cube) (x y : ℤ) :
    K.Q₂.eval x y = -(x • K.M₂ + y • K.N₂).det := by
  simp [QF.eval, Q₂, M₂, N₂, Matrix.det_fin_two]
  ring

lemma Q₃_eq_neg_det (K : Cube) (x y : ℤ) :
    K.Q₃.eval x y = -(x • K.M₃ + y • K.N₃).det := by
  simp [QF.eval, Q₃, M₃, N₃, Matrix.det_fin_two]
  ring

end Cube

/-- The concordant cube attached to a Dirichlet pair of forms with parameters
`A₁, A₂, B, C`: its three slicings produce `A₁x² + Bxy + A₂Cy²`, `A₂x² + Bxy + A₁Cy²` and the
opposite of `A₁A₂x² + Bxy + Cy²`. -/
def concordantCube (A₁ A₂ B C : ℤ) : Cube :=
  ⟨0, A₁, 1, 0, A₂, B, 0, -C⟩

/-- **The three binary quadratic forms of a Bhargava cube all have the same discriminant.** -/
theorem disc_eq (K : Cube) : K.Q₁.disc = K.Q₂.disc ∧ K.Q₂.disc = K.Q₃.disc := by
  constructor <;> · simp only [QF.disc, Cube.Q₁, Cube.Q₂, Cube.Q₃]; ring

/-- **Gauss composition (Dirichlet's identity) for the concordant cube.** -/
theorem concordant_compose (A₁ A₂ B C x₁ y₁ x₂ y₂ : ℤ) :
    (QF.mk A₁ B (A₂ * C)).eval x₁ y₁ * (QF.mk A₂ B (A₁ * C)).eval x₂ y₂ =
      (QF.mk (A₁ * A₂) B C).eval (x₁ * x₂ - C * y₁ * y₂)
        (A₁ * x₁ * y₂ + A₂ * x₂ * y₁ + B * y₁ * y₂) := by
  simp only [QF.eval]
  ring

/--
**Bhargava's cube law (base case).**

For every Bhargava cube the three binary quadratic forms `Q₁, Q₂, Q₃` obtained from the three
slicings have the same discriminant; and for the concordant cube `concordantCube A₁ A₂ B C` the
three forms are exactly `A₁x² + Bxy + A₂Cy²`, `A₂x² + Bxy + A₁Cy²` and the opposite of
`A₁A₂x² + Bxy + Cy²`, and the product of the first two forms is represented by that third form
through an explicit pair of bilinear substitutions — i.e. `Q₁ ∘ Q₂ ∘ Q₃` is the principal class,
which is Gauss composition in Dirichlet's classical form.
-/
theorem bhargava_cube_law :
    (∀ K : Cube, K.Q₁.disc = K.Q₂.disc ∧ K.Q₂.disc = K.Q₃.disc) ∧
    (∀ A₁ A₂ B C : ℤ,
      (concordantCube A₁ A₂ B C).Q₁ = ⟨A₁, B, A₂ * C⟩ ∧
      (concordantCube A₁ A₂ B C).Q₂ = ⟨A₂, B, A₁ * C⟩ ∧
      (concordantCube A₁ A₂ B C).Q₃.op = ⟨A₁ * A₂, B, C⟩ ∧
      ∀ x₁ y₁ x₂ y₂ : ℤ,
        (concordantCube A₁ A₂ B C).Q₁.eval x₁ y₁ *
            (concordantCube A₁ A₂ B C).Q₂.eval x₂ y₂ =
          (concordantCube A₁ A₂ B C).Q₃.op.eval (x₁ * x₂ - C * y₁ * y₂)
            (A₁ * x₁ * y₂ + A₂ * x₂ * y₁ + B * y₁ * y₂)) := by
  refine ⟨disc_eq, fun A₁ A₂ B C => ?_⟩
  have h₁ : (concordantCube A₁ A₂ B C).Q₁ = ⟨A₁, B, A₂ * C⟩ := by
    simp [concordantCube, Cube.Q₁]
  have h₂ : (concordantCube A₁ A₂ B C).Q₂ = ⟨A₂, B, A₁ * C⟩ := by
    simp [concordantCube, Cube.Q₂]
  have h₃ : (concordantCube A₁ A₂ B C).Q₃.op = ⟨A₁ * A₂, B, C⟩ := by
    simp [concordantCube, Cube.Q₃, QF.op]
  refine ⟨h₁, h₂, h₃, fun x₁ y₁ x₂ y₂ => ?_⟩
  rw [h₁, h₂, h₃]
  exact concordant_compose A₁ A₂ B C x₁ y₁ x₂ y₂

end Frontier

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

