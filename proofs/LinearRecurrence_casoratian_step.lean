import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Invariants of second-order linear recurrences

This file develops two algebraic invariants shared by every recurrence

`x (n + 2) = p * x (n + 1) + q * x n`.

The results work over an arbitrary commutative ring, so they apply equally to
integer sequences, polynomial sequences, and recurrences modulo an integer.
-/

namespace LinearRecurrence

variable {R : Type*} [CommRing R]

/-- The discrete Wronskian (Casoratian) of two sequences. -/
def casoratian (x y : ℕ → R) (n : ℕ) : R :=
  x n * y (n + 1) - x (n + 1) * y n

/-- One step of a common second-order recurrence scales the Casoratian by `-q`. -/
theorem casoratian_step
    (p q : R) (x y : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n)
    (hy : ∀ n, y (n + 2) = p * y (n + 1) + q * y n)
    (n : ℕ) :
    casoratian x y (n + 1) = -q * casoratian x y n := by
  unfold casoratian
  rw [hx, hy]
  ring

/-- Closed form for the Casoratian of two solutions of the same recurrence. -/
theorem casoratian_eq_pow_mul
    (p q : R) (x y : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n)
    (hy : ∀ n, y (n + 2) = p * y (n + 1) + q * y n) :
    ∀ n, casoratian x y n = (-q) ^ n * casoratian x y 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [casoratian_step p q x y hx hy n, ih, pow_succ', mul_assoc]

/-- A quadratic expression naturally attached to a second-order recurrence. -/
def quadraticInvariant (p q : R) (x : ℕ → R) (n : ℕ) : R :=
  x (n + 1) ^ 2 - p * x n * x (n + 1) - q * x n ^ 2

/-- The quadratic invariant is also scaled by `-q` at each recurrence step. -/
theorem quadraticInvariant_step
    (p q : R) (x : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n)
    (n : ℕ) :
    quadraticInvariant p q x (n + 1) =
      -q * quadraticInvariant p q x n := by
  simp only [quadraticInvariant]
  rw [hx n]
  ring

/-- Closed form of the quadratic invariant. This subsumes Cassini-type identities. -/
theorem quadraticInvariant_eq_pow_mul
    (p q : R) (x : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) + q * x n) :
    ∀ n, quadraticInvariant p q x n =
      (-q) ^ n * quadraticInvariant p q x 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [quadraticInvariant_step p q x hx n, ih, pow_succ', mul_assoc]

/-- When `q = -1`, the quadratic expression is genuinely constant. -/
theorem quadraticInvariant_constant
    (p : R) (x : ℕ → R)
    (hx : ∀ n, x (n + 2) = p * x (n + 1) - x n) :
    ∀ n, quadraticInvariant p (-1) x n = quadraticInvariant p (-1) x 0 := by
  intro n
  have hrec : ∀ k, x (k + 2) = p * x (k + 1) + (-1) * x k := by
    intro k
    simpa [sub_eq_add_neg] using hx k
  rw [quadraticInvariant_eq_pow_mul p (-1) x hrec n]
  simp

end LinearRecurrence

