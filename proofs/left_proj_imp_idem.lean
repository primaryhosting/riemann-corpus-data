import Mathlib

/-!
# Equational Implications over Magmas

This file proves a collection of equational implications for magmas — algebraic
structures with a single binary operation `◇` (`Magma.op`).

Every proof uses only: `intro`, `exact`, `calc`, `have`, `congrArg`, `.symm`, `.trans`.
-/

class Magma (α : Type*) where
  op : α → α → α

infixl:65 " ◇ " => Magma.op

variable {G : Type*} [Magma G]

-----------------------------------------------------------------------
-- 1. Left projection ⟹ idempotent
--    x ◇ y = x  ⟹  x ◇ x = x
-----------------------------------------------------------------------
theorem left_proj_imp_idem
    (h : ∀ x y : G, x ◇ y = x) : ∀ x : G, x ◇ x = x := by
  intro x
  exact h x x

-----------------------------------------------------------------------
-- 2. Right projection ⟹ idempotent
--    x ◇ y = y  ⟹  x ◇ x = x
-----------------------------------------------------------------------
theorem right_proj_imp_idem
    (h : ∀ x y : G, x ◇ y = y) : ∀ x : G, x ◇ x = x := by
  intro x
  exact h x x

-----------------------------------------------------------------------
-- 3. Left projection ⟹ left self‑absorption
--    x ◇ y = x  ⟹  x ◇ (x ◇ y) = x ◇ y
-----------------------------------------------------------------------
theorem left_proj_imp_left_absorb
    (h : ∀ x y : G, x ◇ y = x) : ∀ x y : G, x ◇ (x ◇ y) = x ◇ y := by
  intro x y
  exact (h x (x ◇ y)).trans (h x y).symm

-----------------------------------------------------------------------
-- 4. Right projection ⟹ right self‑absorption
--    x ◇ y = y  ⟹  (x ◇ y) ◇ y = x ◇ y
-----------------------------------------------------------------------
theorem right_proj_imp_right_absorb
    (h : ∀ x y : G, x ◇ y = y) : ∀ x y : G, (x ◇ y) ◇ y = x ◇ y := by
  intro x y
  exact (h (x ◇ y) y).trans (h x y).symm

-----------------------------------------------------------------------
-- 5. Idempotent + associative ⟹ left self‑absorption
--    x ◇ x = x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)  ⟹  x ◇ (x ◇ y) = x ◇ y
-----------------------------------------------------------------------
theorem idem_assoc_imp_left_absorb
    (h_idem : ∀ x : G, x ◇ x = x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y : G, x ◇ (x ◇ y) = x ◇ y := by
  intro x y
  exact (h_assoc x x y).symm.trans (congrArg (· ◇ y) (h_idem x))

-----------------------------------------------------------------------
-- 6. Idempotent + associative ⟹ right self‑absorption
--    x ◇ x = x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)  ⟹  (x ◇ y) ◇ y = x ◇ y
-----------------------------------------------------------------------
theorem idem_assoc_imp_right_absorb
    (h_idem : ∀ x : G, x ◇ x = x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y : G, (x ◇ y) ◇ y = x ◇ y := by
  intro x y
  exact (h_assoc x y y).trans (congrArg (x ◇ ·) (h_idem y))

-----------------------------------------------------------------------
-- 7. Left projection + right projection ⟹ all elements equal
--    x ◇ y = x ∧ x ◇ y = y  ⟹  x = y
-----------------------------------------------------------------------
theorem left_right_proj_imp_eq
    (h1 : ∀ x y : G, x ◇ y = x)
    (h2 : ∀ x y : G, x ◇ y = y) :
    ∀ x y : G, x = y := by
  intro x y
  exact (h1 x y).symm.trans (h2 x y)

-----------------------------------------------------------------------
-- 8. Idempotent ⟹ double‑idempotent
--    x ◇ x = x  ⟹  (x ◇ x) ◇ (x ◇ x) = x
-----------------------------------------------------------------------
theorem idem_imp_double_idem
    (h : ∀ x : G, x ◇ x = x) : ∀ x : G, (x ◇ x) ◇ (x ◇ x) = x := by
  intro x
  exact (h (x ◇ x)).trans (h x)

-----------------------------------------------------------------------
-- 9. Idempotent ⟹ left congruence cancellation
--    x ◇ x = x  ⟹  (x ◇ x) ◇ y = x ◇ y
-----------------------------------------------------------------------
theorem idem_imp_left_cong
    (h : ∀ x : G, x ◇ x = x) : ∀ x y : G, (x ◇ x) ◇ y = x ◇ y := by
  intro x y
  exact congrArg (· ◇ y) (h x)

-----------------------------------------------------------------------
-- 10. Idempotent ⟹ right congruence cancellation
--     x ◇ x = x  ⟹  x ◇ (y ◇ y) = x ◇ y
-----------------------------------------------------------------------
theorem idem_imp_right_cong
    (h : ∀ x : G, x ◇ x = x) : ∀ x y : G, x ◇ (y ◇ y) = x ◇ y := by
  intro x y
  exact congrArg (x ◇ ·) (h y)

-----------------------------------------------------------------------
-- 11. Commutative + left projection ⟹ right projection
--     x ◇ y = y ◇ x ∧ x ◇ y = x  ⟹  x ◇ y = y
-----------------------------------------------------------------------
theorem comm_left_proj_imp_right_proj
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_left : ∀ x y : G, x ◇ y = x) :
    ∀ x y : G, x ◇ y = y := by
  intro x y
  exact (h_comm x y).trans (h_left y x)

-----------------------------------------------------------------------
-- 12. Commutative + associative ⟹ left‑commutativity
--     x ◇ y = y ◇ x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)
--     ⟹  x ◇ (y ◇ z) = y ◇ (x ◇ z)
-----------------------------------------------------------------------
theorem comm_assoc_imp_left_comm
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y z : G, x ◇ (y ◇ z) = y ◇ (x ◇ z) := by
  intro x y z
  calc x ◇ (y ◇ z)
      _ = (x ◇ y) ◇ z := (h_assoc x y z).symm
      _ = (y ◇ x) ◇ z := congrArg (· ◇ z) (h_comm x y)
      _ = y ◇ (x ◇ z) := h_assoc y x z

-----------------------------------------------------------------------
-- 13. Commutative + associative + idempotent ⟹ medial absorption
--     x ◇ y = y ◇ x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z) ∧ x ◇ x = x
--     ⟹  (x ◇ y) ◇ x = x ◇ y
-----------------------------------------------------------------------
theorem comm_assoc_idem_imp_medial_absorb
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z))
    (h_idem : ∀ x : G, x ◇ x = x) :
    ∀ x y : G, (x ◇ y) ◇ x = x ◇ y := by
  intro x y
  calc (x ◇ y) ◇ x
      _ = x ◇ (y ◇ x) := h_assoc x y x
      _ = x ◇ (x ◇ y) := congrArg (x ◇ ·) (h_comm y x)
      _ = (x ◇ x) ◇ y := (h_assoc x x y).symm
      _ = x ◇ y        := congrArg (· ◇ y) (h_idem x)

-----------------------------------------------------------------------
-- 14. Associative ⟹ power‑associativity identity
--     (x ◇ y) ◇ z = x ◇ (y ◇ z)
--     ⟹  ((x ◇ y) ◇ z) ◇ w = x ◇ (y ◇ (z ◇ w))
-----------------------------------------------------------------------
theorem assoc_imp_gen_assoc
    (h : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y z w : G, ((x ◇ y) ◇ z) ◇ w = x ◇ (y ◇ (z ◇ w)) := by
  intro x y z w
  calc ((x ◇ y) ◇ z) ◇ w
      _ = (x ◇ y) ◇ (z ◇ w) := h (x ◇ y) z w
      _ = x ◇ (y ◇ (z ◇ w)) := h x y (z ◇ w)

-----------------------------------------------------------------------
-- 15. Commutative + associative ⟹ right‑commutativity
--     x ◇ y = y ◇ x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)
--     ⟹  (x ◇ y) ◇ z = (x ◇ z) ◇ y
-----------------------------------------------------------------------
theorem comm_assoc_imp_right_comm
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y z : G, (x ◇ y) ◇ z = (x ◇ z) ◇ y := by
  intro x y z
  calc (x ◇ y) ◇ z
      _ = x ◇ (y ◇ z) := h_assoc x y z
      _ = x ◇ (z ◇ y) := congrArg (x ◇ ·) (h_comm y z)
      _ = (x ◇ z) ◇ y := (h_assoc x z y).symm

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

