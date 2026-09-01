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

import Mathlib

/-!
# Boolean circuits (formulas) over natural-number-indexed variables

This file sets up the basic combinatorial machinery used in the formalisation of
Toda's theorem: Boolean formulas over variables indexed by `ℕ`, their size,
their variable bound, evaluation, and the *counting* operation
`cnt C m x` = number of witnesses `y ∈ {0,1}^m` making `C` true on input `x`.
-/

namespace CS

open Finset

/-- Boolean formulas over variables indexed by `ℕ`. -/
inductive Circ where
  | var (i : ℕ) : Circ
  | cst (b : Bool) : Circ
  | neg (a : Circ) : Circ
  | conj (a b : Circ) : Circ
  | disj (a b : Circ) : Circ
  | xorC (a b : Circ) : Circ
  deriving Inhabited

namespace Circ

/-- Evaluation of a formula under an assignment. -/
def eval (v : ℕ → Bool) : Circ → Bool
  | .var i => v i
  | .cst b => b
  | .neg a => !(a.eval v)
  | .conj a b => (a.eval v) && (b.eval v)
  | .disj a b => (a.eval v) || (b.eval v)
  | .xorC a b => xor (a.eval v) (b.eval v)

@[simp] theorem eval_var (v : ℕ → Bool) (i : ℕ) : (Circ.var i).eval v = v i := rfl
@[simp] theorem eval_cst (v : ℕ → Bool) (b : Bool) : (Circ.cst b).eval v = b := rfl
@[simp] theorem eval_neg (v : ℕ → Bool) (a : Circ) : (Circ.neg a).eval v = !(a.eval v) := rfl
@[simp] theorem eval_conj (v : ℕ → Bool) (a b : Circ) :
    (Circ.conj a b).eval v = ((a.eval v) && (b.eval v)) := rfl
@[simp] theorem eval_disj (v : ℕ → Bool) (a b : Circ) :
    (Circ.disj a b).eval v = ((a.eval v) || (b.eval v)) := rfl
@[simp] theorem eval_xorC (v : ℕ → Bool) (a b : Circ) :
    (Circ.xorC a b).eval v = xor (a.eval v) (b.eval v) := rfl

/-- Size (number of nodes) of a formula. -/
def size : Circ → ℕ
  | .var _ => 1
  | .cst _ => 1
  | .neg a => a.size + 1
  | .conj a b => a.size + b.size + 1
  | .disj a b => a.size + b.size + 1
  | .xorC a b => a.size + b.size + 1

/-- `bnd C` is a bound on the variable indices occurring in `C`: all variables
occurring are `< bnd C`. -/
def bnd : Circ → ℕ
  | .var i => i + 1
  | .cst _ => 0
  | .neg a => a.bnd
  | .conj a b => max a.bnd b.bnd
  | .disj a b => max a.bnd b.bnd
  | .xorC a b => max a.bnd b.bnd

theorem eval_congr {C : Circ} {v w : ℕ → Bool} (h : ∀ i < C.bnd, v i = w i) :
    C.eval v = C.eval w := by
  induction C with
  | var i => exact h i (Nat.lt_succ_self i)
  | cst b => rfl
  | neg a ih => simp [eval, ih h]
  | conj a b iha ihb =>
      simp only [eval]
      rw [iha (fun i hi => h i (lt_of_lt_of_le hi (le_max_left _ _))),
          ihb (fun i hi => h i (lt_of_lt_of_le hi (le_max_right _ _)))]
  | disj a b iha ihb =>
      simp only [eval]
      rw [iha (fun i hi => h i (lt_of_lt_of_le hi (le_max_left _ _))),
          ihb (fun i hi => h i (lt_of_lt_of_le hi (le_max_right _ _)))]
  | xorC a b iha ihb =>
      simp only [eval]
      rw [iha (fun i hi => h i (lt_of_lt_of_le hi (le_max_left _ _))),
          ihb (fun i hi => h i (lt_of_lt_of_le hi (le_max_right _ _)))]

/-- `shift n d C` shifts every variable index `≥ n` up by `d`. -/
def shift (n d : ℕ) : Circ → Circ
  | .var i => .var (if i < n then i else i + d)
  | .cst b => .cst b
  | .neg a => .neg (shift n d a)
  | .conj a b => .conj (shift n d a) (shift n d b)
  | .disj a b => .disj (shift n d a) (shift n d b)
  | .xorC a b => .xorC (shift n d a) (shift n d b)

@[simp] theorem size_shift (n d : ℕ) (C : Circ) : (shift n d C).size = C.size := by
  induction C with
  | var i => rfl
  | cst b => rfl
  | neg a ih => simp [shift, size, ih]
  | conj a b iha ihb => simp [shift, size, iha, ihb]
  | disj a b iha ihb => simp [shift, size, iha, ihb]
  | xorC a b iha ihb => simp [shift, size, iha, ihb]

theorem eval_shift (n d : ℕ) (C : Circ) (v : ℕ → Bool) :
    (shift n d C).eval v = C.eval (fun i => if i < n then v i else v (i + d)) := by
  induction C with
  | var i => by_cases h : i < n <;> simp [shift, eval, h]
  | cst b => rfl
  | neg a ih => simp [shift, eval, ih]
  | conj a b iha ihb => simp [shift, eval, iha, ihb]
  | disj a b iha ihb => simp [shift, eval, iha, ihb]
  | xorC a b iha ihb => simp [shift, eval, iha, ihb]

theorem bnd_shift {n d m : ℕ} {C : Circ} (h : C.bnd ≤ n + m) :
    (shift n d C).bnd ≤ n + d + m := by
  induction C with
  | var i =>
      simp only [bnd] at h
      by_cases hi : i < n
      · simp only [shift, if_pos hi, bnd]; omega
      · simp only [shift, if_neg hi, bnd]; omega
  | cst b => simp [shift, bnd]
  | neg a ih => exact ih h
  | conj a b iha ihb =>
      simp only [bnd, max_le_iff] at h
      simp only [shift, bnd, max_le_iff]
      exact ⟨iha h.1, ihb h.2⟩
  | disj a b iha ihb =>
      simp only [bnd, max_le_iff] at h
      simp only [shift, bnd, max_le_iff]
      exact ⟨iha h.1, ihb h.2⟩
  | xorC a b iha ihb =>
      simp only [bnd, max_le_iff] at h
      simp only [shift, bnd, max_le_iff]
      exact ⟨iha h.1, ihb h.2⟩

end Circ

/-- The assignment determined by an input string `x` (variables `0, …, |x|-1`)
together with a witness `y ∈ {0,1}^m` (variables `|x|, …, |x|+m-1`).
Out-of-range variables get the value `false`. -/
def asg (x : List Bool) {m : ℕ} (y : Fin m → Bool) (i : ℕ) : Bool :=
  if i < x.length then x.getD i false
  else if h : i - x.length < m then y ⟨i - x.length, h⟩ else false

/-- Number of witnesses `y ∈ {0,1}^m` accepted by `C` on input `x`. -/
def cnt (C : Circ) (m : ℕ) (x : List Bool) : ℕ :=
  ∑ y : Fin m → Bool, (if C.eval (asg x y) then 1 else 0)

theorem cnt_le (C : Circ) (m : ℕ) (x : List Bool) : cnt C m x ≤ 2 ^ m := by
  classical
  have h : cnt C m x ≤ ∑ _y : Fin m → Bool, 1 := by
    apply Finset.sum_le_sum
    intro y _
    split <;> simp
  simpa [Fintype.card_fun] using h

end CS

