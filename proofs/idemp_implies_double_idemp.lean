import Mathlib

class Magma (α : Type*) where
  op : α → α → α

infixl:65 " ◇ " => Magma.op

/-- If x ◇ x = x (idempotent) for all x, then (x ◇ x) ◇ (x ◇ x) = x for all x. -/
theorem idemp_implies_double_idemp {α : Type*} [Magma α]
    (h : ∀ x : α, x ◇ x = x) :
    ∀ x : α, (x ◇ x) ◇ (x ◇ x) = x := by
  intro x
  exact (h (x ◇ x)).trans (h x)

/-- If x ◇ y = x (left projection) for all x y, then x ◇ (y ◇ x) = x for all x y. -/
theorem proj_left_implies_absorb {α : Type*} [Magma α]
    (h : ∀ x y : α, x ◇ y = x) :
    ∀ x y : α, x ◇ (y ◇ x) = x := by
  intro x y
  exact h x (y ◇ x)

/-- If x ◇ y = y (right projection) for all x y, then (x ◇ y) ◇ (x ◇ y) = y for all x y. -/
theorem proj_right_implies_idemp_val {α : Type*} [Magma α]
    (h : ∀ x y : α, x ◇ y = y) :
    ∀ x y : α, (x ◇ y) ◇ (x ◇ y) = y := by
  intro x y
  exact (h (x ◇ y) (x ◇ y)).trans (h x y)

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

