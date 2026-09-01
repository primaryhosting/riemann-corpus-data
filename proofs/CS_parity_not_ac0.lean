/-
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## The Boolean cube and `ZMod 3`-valued functions on it -/

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Functions from the Boolean cube to the field `ZMod 3`. -/
abbrev CFun (n : ℕ) := Cube n → ZMod 3

/-- The `±1` encoding of a bit inside `ZMod 3`. -/
def sgn (b : Bool) : ZMod 3 := if b then -1 else 1

/-- The `0/1` encoding of a bit inside `ZMod 3`. -/
def bval (b : Bool) : ZMod 3 := if b then 1 else 0

/-- The monomial `∏_{i ∈ S} x_i` in the `±1` encoding, viewed as a function on the cube. -/
def mon {n : ℕ} (S : Finset (Fin n)) : CFun n := fun x => ∏ i ∈ S, sgn (x i)

/-- The finite set of monomials of degree at most `D`. -/
def monFinset (n D : ℕ) : Finset (CFun n) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).image mon

/-- The space of functions on the cube computed by `ZMod 3`-polynomials of degree at most `D`
(in the `±1` encoding). -/
def degLE (n D : ℕ) : Submodule (ZMod 3) (CFun n) :=
  Submodule.span (ZMod 3) (monFinset n D : Set (CFun n))

/-- Parity of a Boolean input. -/
def parity {n : ℕ} (x : Cube n) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

/-! ## Circuits -/

/-- A gate of an unbounded fan-in Boolean circuit. Inputs are referred to by gate index. -/
inductive Gate (n : ℕ) where
  | var : Fin n → Gate n
  | neg : ℕ → Gate n
  | conj : Finset ℕ → Gate n
  | disj : Finset ℕ → Gate n
  deriving Inhabited

/-- The set of gate indices feeding into a gate. -/
def Gate.inputs {n : ℕ} : Gate n → Finset ℕ
  | .var _ => ∅
  | .neg j => {j}
  | .conj s => s
  | .disj s => s

/-- Well-formedness up to gate `out`: every gate only reads strictly earlier gates. -/
def WF {n : ℕ} (c : ℕ → Gate n) (out : ℕ) : Prop :=
  ∀ g ≤ out, ∀ j ∈ (c g).inputs, j < g

/-- Fuel-based evaluation of the gates of a circuit. References to gates that are not strictly
earlier are ignored (they cannot occur in a well-formed circuit). -/
def valAux {n : ℕ} (c : ℕ → Gate n) (x : Cube n) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, g =>
    match c g with
    | .var i => x i
    | .neg j => if j < g then !(valAux c x fuel j) else false
    | .conj s => decide (∀ j ∈ s, j < g → valAux c x fuel j = true)
    | .disj s => decide (∃ j ∈ s, j < g ∧ valAux c x fuel j = true)

/-- Value of gate `g` of the circuit `c` on input `x`. -/
def val {n : ℕ} (c : ℕ → Gate n) (x : Cube n) (g : ℕ) : Bool := valAux c x (g + 1) g

/-- Fuel-based computation of the AND/OR-depth of the gates of a circuit. -/
def depAux {n : ℕ} (c : ℕ → Gate n) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, g =>
    match c g with
    | .var _ => 0
    | .neg j => if j < g then depAux c fuel j else 0
    | .conj s => 1 + (s.filter (fun j => j < g)).sup (fun j => depAux c fuel j)
    | .disj s => 1 + (s.filter (fun j => j < g)).sup (fun j => depAux c fuel j)

/-- The AND/OR-depth of gate `g`: negations and variables are free. -/
def dep {n : ℕ} (c : ℕ → Gate n) (g : ℕ) : ℕ := depAux c (g + 1) g

/-- The circuit `c` with output gate `out` computes parity on `n` bits. -/
def ComputesParity (n : ℕ) (c : ℕ → Gate n) (out : ℕ) : Prop :=
  ∀ x : Cube n, val c x out = parity x

/-- `PARITY ∈ AC⁰`: there are a constant depth bound `d` and an exponent `k` such that for
every `n` there is a circuit of size at most `n ^ k + k` and depth at most `d` computing
`PARITY` on `n` bits. -/
def ParityInAC0 : Prop :=
  ∃ d k : ℕ, ∀ n : ℕ, ∃ (c : ℕ → Gate n) (out : ℕ),
    WF c out ∧ out + 1 ≤ n ^ k + k ∧ dep c out ≤ d ∧ ComputesParity n c out

end CS

