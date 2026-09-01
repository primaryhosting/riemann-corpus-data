import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/

theorem imp_A1 (h : ∀ x y : G, x * y = x) :
    ∀ x : G, x * x = x := by
  intro x; exact h x x

theorem imp_A2 (h : ∀ x y : G, x * y = x) :
    ∀ x y : G, (x * y) * y = x * y := by
  intro x y; exact h (x * y) y

theorem imp_A3 (h : ∀ x y : G, x * y = x) :
    ∀ x y : G, x * (x * y) = x * y := by
  intro x y; exact (h x (x * y)).trans (h x y).symm

theorem imp_A4 (h : ∀ x y : G, x * y = x) :
    ∀ x y z : G, (x * y) * z = x := by
  intro x y z; exact (h (x * y) z).trans (h x y)

theorem imp_A5 (h : ∀ x y : G, x * y = x) :
    ∀ x y z : G, x * (y * z) = x := by
  intro x y z; exact h x (y * z)

theorem imp_A6 (h : ∀ x y : G, x * y = x) :
    ∀ x y z : G, (x * y) * z = x * (y * z) := by
  intro x y z
  exact ((h (x * y) z).trans (h x y)).trans (h x (y * z)).symm

theorem imp_A7 (h : ∀ x y : G, x * y = x) :
    ∀ x y z : G, x * y = x * z := by
  intro x y z; exact (h x y).trans (h x z).symm

/-! ## Section B: From right projection (∀ x y, x * y = y) — 7 theorems -/

theorem imp_B1 (h : ∀ x y : G, x * y = y) :
    ∀ x : G, x * x = x := by
  intro x; exact h x x

theorem imp_B2 (h : ∀ x y : G, x * y = y) :
    ∀ x y : G, x * (x * y) = x * y := by
  intro x y; exact h x (x * y)

theorem imp_B3 (h : ∀ x y : G, x * y = y) :
    ∀ x y : G, (x * y) * y = x * y := by
  intro x y; exact (h (x * y) y).trans (h x y).symm

theorem imp_B4 (h : ∀ x y : G, x * y = y) :
    ∀ x y z : G, x * (y * z) = z := by
  intro x y z; exact (h x (y * z)).trans (h y z)

theorem imp_B5 (h : ∀ x y : G, x * y = y) :
    ∀ x y z : G, (x * y) * z = z := by
  intro x y z; exact h (x * y) z

theorem imp_B6 (h : ∀ x y : G, x * y = y) :
    ∀ x y z : G, (x * y) * z = x * (y * z) := by
  intro x y z
  exact (h (x * y) z).trans ((h x (y * z)).trans (h y z)).symm

theorem imp_B7 (h : ∀ x y : G, x * y = y) :
    ∀ x y z : G, x * z = y * z := by
  intro x y z; exact (h x z).trans (h y z).symm

/-! ## Section C: From commutativity (∀ x y, x * y = y * x) — 5 theorems -/

theorem imp_C1 (h : ∀ x y : G, x * y = y * x) :
    ∀ x y : G, x * (y * x) = x * (x * y) := by
  intro x y; exact congrArg (x * ·) (h y x)

theorem imp_C2 (h : ∀ x y : G, x * y = y * x) :
    ∀ x y : G, (x * y) * x = x * (x * y) := by
  intro x y; exact h (x * y) x

theorem imp_C3 (h : ∀ x y : G, x * y = y * x) :
    ∀ x y : G, (x * y) * y = y * (x * y) := by
  intro x y; exact h (x * y) y

theorem imp_C4 (h : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, (x * y) * z = (y * x) * z := by
  intro x y z; exact congrArg (· * z) (h x y)

theorem imp_C5 (h : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, x * (y * z) = x * (z * y) := by
  intro x y z; exact congrArg (x * ·) (h y z)

/-! ## Section D: From associativity (∀ x y z, (x * y) * z = x * (y * z)) — 5 theorems -/

theorem imp_D1 (h : ∀ x y z : G, (x * y) * z = x * (y * z)) :
    ∀ x y z w : G, ((x * y) * z) * w = (x * y) * (z * w) := by
  intro x y z w; exact h (x * y) z w

theorem imp_D2 (h : ∀ x y z : G, (x * y) * z = x * (y * z)) :
    ∀ x y z w : G, ((x * y) * z) * w = x * (y * (z * w)) := by
  intro x y z w; exact (h (x * y) z w).trans (h x y (z * w))

theorem imp_D3 (h : ∀ x y z : G, (x * y) * z = x * (y * z)) :
    ∀ x y z w : G, (x * y) * (z * w) = x * (y * (z * w)) := by
  intro x y z w; exact h x y (z * w)

theorem imp_D4 (h : ∀ x y z : G, (x * y) * z = x * (y * z)) :
    ∀ x y z w : G, ((x * y) * z) * w = x * ((y * z) * w) := by
  intro x y z w
  exact (congrArg (· * w) (h x y z)).trans (h x (y * z) w)

theorem imp_D5 (h : ∀ x y z : G, (x * y) * z = x * (y * z)) :
    ∀ x y z w : G, x * (y * (z * w)) = x * ((y * z) * w) := by
  intro x y z w; exact congrArg (x * ·) (h y z w).symm

/-! ## Section E: From idempotency (∀ x, x * x = x) — 3 theorems -/

theorem imp_E1 (h : ∀ x : G, x * x = x) :
    ∀ x : G, (x * x) * (x * x) = x * x := by
  intro x; exact h (x * x)

theorem imp_E2 (h : ∀ x : G, x * x = x) :
    ∀ x : G, (x * x) * x = x * x := by
  intro x; exact congrArg (· * x) (h x)

theorem imp_E3 (h : ∀ x : G, x * x = x) :
    ∀ x : G, x * (x * x) = x * x := by
  intro x; exact congrArg (x * ·) (h x)

/-! ## Section F: From associativity + idempotency — 3 theorems -/

theorem imp_F1
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_i : ∀ x : G, x * x = x) :
    ∀ x y : G, x * (x * y) = x * y := by
  intro x y
  exact (h_a x x y).symm.trans (congrArg (· * y) (h_i x))

theorem imp_F2
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_i : ∀ x : G, x * x = x) :
    ∀ x y : G, (x * y) * y = x * y := by
  intro x y
  exact (h_a x y y).trans (congrArg (x * ·) (h_i y))

theorem imp_F3
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_i : ∀ x : G, x * x = x) :
    ∀ x : G, x * (x * x) = x := by
  intro x
  exact ((h_a x x x).symm.trans (congrArg (· * x) (h_i x))).trans (h_i x)

/-! ## Section G: From associativity + commutativity — 5 theorems -/

theorem imp_G1
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, x * (y * z) = y * (x * z) := by
  intro x y z
  exact ((h_a x y z).symm.trans (congrArg (· * z) (h_c x y))).trans (h_a y x z)

theorem imp_G2
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, (x * y) * z = (x * z) * y := by
  intro x y z
  exact (h_a x y z).trans ((congrArg (x * ·) (h_c y z)).trans (h_a x z y).symm)

theorem imp_G3
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, x * (y * z) = z * (y * x) := by
  intro x y z
  exact ((h_a x y z).symm.trans (h_c (x * y) z)).trans (congrArg (z * ·) (h_c x y))

theorem imp_G4
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z w : G, (x * y) * (z * w) = (x * z) * (y * w) := by
  intro x y z w
  calc (x * y) * (z * w)
      = x * (y * (z * w)) := h_a x y (z * w)
    _ = x * ((y * z) * w) := congrArg (x * ·) (h_a y z w).symm
    _ = x * ((z * y) * w) := congrArg (x * ·) (congrArg (· * w) (h_c y z))
    _ = x * (z * (y * w)) := congrArg (x * ·) (h_a z y w)
    _ = (x * z) * (y * w) := (h_a x z (y * w)).symm

theorem imp_G5
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, x * (y * z) = (z * x) * y := by
  intro x y z
  calc x * (y * z)
      = x * (z * y) := congrArg (x * ·) (h_c y z)
    _ = (x * z) * y := (h_a x z y).symm
    _ = (z * x) * y := congrArg (· * y) (h_c x z)

/-! ## Section H: From left self-idempotency (∀ x y, x * (x * y) = x * y) — 3 theorems -/

theorem imp_H1 (h : ∀ x y : G, x * (x * y) = x * y) :
    ∀ x y : G, x * (x * (x * y)) = x * y := by
  intro x y; exact (h x (x * y)).trans (h x y)

theorem imp_H2 (h : ∀ x y : G, x * (x * y) = x * y) :
    ∀ x : G, x * (x * x) = x * x := by
  intro x; exact h x x

theorem imp_H3 (h : ∀ x y : G, x * (x * y) = x * y) :
    ∀ x y z : G, (x * y) * ((x * y) * z) = (x * y) * z := by
  intro x y z; exact h (x * y) z

/-! ## Section I: From right self-idempotency (∀ x y, (x * y) * y = x * y) — 3 theorems -/

theorem imp_I1 (h : ∀ x y : G, (x * y) * y = x * y) :
    ∀ x y : G, ((x * y) * y) * y = x * y := by
  intro x y; exact (h (x * y) y).trans (h x y)

theorem imp_I2 (h : ∀ x y : G, (x * y) * y = x * y) :
    ∀ x : G, (x * x) * x = x * x := by
  intro x; exact h x x

theorem imp_I3 (h : ∀ x y : G, (x * y) * y = x * y) :
    ∀ x y z : G, ((x * y) * z) * z = (x * y) * z := by
  intro x y z; exact h (x * y) z

/-! ## Section J: Combined hypotheses — 3 theorems -/

theorem imp_J1
    (h_c : ∀ x y : G, x * y = y * x)
    (h_l : ∀ x y : G, x * (x * y) = x * y) :
    ∀ x y : G, (x * y) * y = x * y := by
  intro x y
  calc (x * y) * y
      = y * (x * y) := h_c (x * y) y
    _ = y * (y * x) := congrArg (y * ·) (h_c x y)
    _ = y * x       := h_l y x
    _ = x * y       := h_c y x

theorem imp_J2
    (h_c : ∀ x y : G, x * y = y * x)
    (h_r : ∀ x y : G, (x * y) * y = x * y) :
    ∀ x y : G, x * (x * y) = x * y := by
  intro x y
  calc x * (x * y)
      = (x * y) * x := h_c x (x * y)
    _ = (y * x) * x := congrArg (· * x) (h_c x y)
    _ = y * x       := h_r y x
    _ = x * y       := h_c y x

theorem imp_J3
    (h_l : ∀ x y : G, x * y = x)
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y : G, x * y = y := by
  intro x y; exact (h_c x y).trans (h_l y x)

