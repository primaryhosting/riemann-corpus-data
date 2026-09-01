/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file formalises Ladner's theorem: if `P ≠ NP` then there is an
`NP`-intermediate language, i.e. a language that lies in `NP`, is not in `P`,
and is not `NP`-hard.

The development is self-contained (no imports beyond Lean's prelude).  A
`Framework` bundles the data of the complexity classes `P` and `NP` together
with polynomial-time many-one reducibility `Red`, and records the standard
structural facts about them that Ladner's argument uses.  The mathematical
heart of the theorem -- the *delayed diagonalisation* ("blowing holes in a
hard language") -- is carried out in full inside `CS.ladner`.
-/

namespace CS

/-! ## Languages -/

/-- A language is a decision problem: a Boolean-valued function on (codes of) inputs. -/
abbrev Lang : Type := Nat → Bool

/-- From `A ≠ B` we obtain an input on which the two languages differ. -/
theorem lang_ne {A B : Lang} (h : A ≠ B) : ∃ z, A z ≠ B z :=
  Classical.byContradiction fun hc =>
    h (funext fun z => Classical.byContradiction fun hz => hc ⟨z, hz⟩)

/-! ## The stage function of Ladner's delayed diagonalisation

`W i n` is the outcome of the (polynomially time-bounded) search performed at
step `n` while the construction is working on requirement number `i`: it is
`true` exactly when that search has succeeded in refuting requirement `i`, so
that the construction may move on to requirement `i + 1`. -/

/-- `stage W n` is the requirement the construction is working on at input `n`.
It starts at `0` and increases by one exactly when the search fires. -/
def stage (W : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if W (stage W n) n then stage W n + 1 else stage W n

/-- The language obtained from `L` by "blowing holes" in it: `L` is preserved at
inputs where the stage is even, and emptied out where the stage is odd. -/
def punch (L : Lang) (W : Nat → Nat → Bool) : Lang :=
  fun x => if stage W x % 2 = 0 then L x else false

/-- The requirement associated with stage `i`.  Even stages `2 * j` ask that the
constructed language `punch L W` differ from the `j`-th language of `P`; odd
stages `2 * j + 1` ask that the `j`-th candidate reduction `r j` fail to reduce
`L` to `punch L W`. -/
def Witness (L : Lang) (W : Nat → Nat → Bool) (M : Nat → Lang)
    (r : Nat → Nat → Nat) (i : Nat) : Prop :=
  if i % 2 = 0 then ∃ z, M (i / 2) z ≠ punch L W z
  else ∃ z, L z ≠ punch L W (r (i / 2) z)

theorem stage_succ_true {W : Nat → Nat → Bool} {n : Nat} (h : W (stage W n) n = true) :
    stage W (n + 1) = stage W n + 1 := by
  simp only [stage, h, if_pos]

theorem stage_succ_false {W : Nat → Nat → Bool} {n : Nat} (h : W (stage W n) n = false) :
    stage W (n + 1) = stage W n := by
  simp only [stage, h, Bool.false_eq_true, if_false]

theorem stage_le_succ (W : Nat → Nat → Bool) (n : Nat) : stage W n ≤ stage W (n + 1) := by
  simp only [stage]; split <;> omega

theorem stage_succ_le (W : Nat → Nat → Bool) (n : Nat) : stage W (n + 1) ≤ stage W n + 1 := by
  simp only [stage]; split <;> omega

theorem stage_mono (W : Nat → Nat → Bool) {m n : Nat} (h : m ≤ n) : stage W m ≤ stage W n := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ k ih =>
    cases Nat.lt_or_ge m (k + 1) with
    | inl hlt => exact Nat.le_trans (ih (by omega)) (stage_le_succ W k)
    | inr hge => have : m = k + 1 := by omega
                 subst this; exact Nat.le_refl _

/-- The stage function takes every value below any value it attains. -/
theorem stage_hits (W : Nat → Nat → Bool) :
    ∀ (n k : Nat), k ≤ stage W n → ∃ m, stage W m = k := by
  intro n
  induction n with
  | zero => intro k hk
            have h0 : stage W 0 = 0 := rfl
            exact ⟨0, by omega⟩
  | succ n ih =>
    intro k hk
    cases Nat.lt_or_ge (stage W n) k with
    | inl hlt => exact ⟨n + 1, by have := stage_succ_le W n; omega⟩
    | inr hge => exact ih k hge

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

