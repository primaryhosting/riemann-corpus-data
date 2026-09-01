import RequestProject.Model

/-!
# Basic properties of runs

The three facts we need about the machine model:

* a run of length `t` queries at most `t` strings;
* all queried strings are short (bounded by the initial register sizes plus the running time);
* the outcome of a run only depends on the oracle's values on the queried strings.
-/

namespace CS

theorem exec_zero (A : Oracle) (P : List Instr) (c : Config) : exec A P 0 c = (none, []) := by
  rw [exec]

/-- A run of length `fuel` makes at most `fuel` queries. -/
theorem queries_length_le (A : Oracle) (P : List Instr) :
    ∀ (fuel : ℕ) (c : Config), (exec A P fuel c).2.length ≤ fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    match fuel with
    | 0 => intro c; simp [exec_zero]
    | f + 1 =>
      intro c
      rw [exec]
      split
      case h_1 => simp
      case h_2 => simp
      case h_3 => exact (ih f (by omega) _).trans (by omega)
      case h_4 => split <;> exact (ih f (by omega) _).trans (by omega)
      case h_5 => exact (ih f (by omega) _).trans (by omega)
      case h_6 =>
        split
        · simp
        · exact (ih _ (by omega) _).trans (by omega)
      case h_7 =>
        rename_i r jY jN _
        simp only [List.length_cons]
        have := ih f (by omega) (Config.mk (if A (c.regs r) then jY else jN) c.regs)
        omega

end CS

import Mathlib

/-!
# A machine model for relativized polynomial time

This file sets up a small, self-contained model of oracle computation used to state and
prove the Baker–Gill–Solovay theorem.

A *machine* is a finite list of instructions operating on countably many string registers
(`ℕ → List Bool`), together with a starting program counter.  Instructions can append one
bit to a register, destructively pop the leading bit of a register (branching on its value),
append a copy of one register to another, clear a register, or query the oracle on the
contents of a register.

Costs are charged so that the total number of bits ever written is at most the number of
time steps used: appending a bit costs `1`, and appending a copy of a register of length `ℓ`
costs `ℓ + 1`.

On input `x` with certificate `y` and *padding parameter* `p` the machine starts with
`R0 = x`, `R1 = y`, `R2 = 1^p` and all other registers empty.  Giving the machine a
polynomially long block of `1`s for free is a harmless convention (a real machine could
write it down in polynomial time) which spares us from programming multiplication loops.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of binary strings, presented as a (possibly noncomputable) predicate. -/
abbrev Oracle := Str → Bool

/-- Machine instructions. -/
inductive Instr where
  /-- Append bit `b` to register `r`, then go to `next`. -/
  | push (r : ℕ) (b : Bool) (next : ℕ)
  /-- Remove the first bit of register `r`; jump to `jT`/`jF` according to the bit, or to
  `jE` if the register is empty. -/
  | pop (r : ℕ) (jT jF jE : ℕ)
  /-- Append a copy of register `src` to register `dst`, then go to `next`. -/
  | copy (src dst next : ℕ)
  /-- Empty register `r`, then go to `next`. -/
  | clear (r next : ℕ)
  /-- Query the oracle on the contents of register `r`; jump to `jY` or `jN`. -/
  | query (r jY jN : ℕ)
  /-- Halt with answer `b`. -/
  | halt (b : Bool)
  deriving DecidableEq

namespace Instr

/-- Numerical code of an instruction, used to get an `Encodable` structure. -/
def toCode : Instr → ℕ × ℕ × ℕ × ℕ × ℕ
  | .push r b next => (0, r, b.toNat, next, 0)
  | .pop r jT jF jE => (1, r, jT, jF, jE)
  | .copy s d n => (2, s, d, n, 0)
  | .clear r n => (3, r, n, 0, 0)
  | .query r jY jN => (4, r, jY, jN, 0)
  | .halt b => (5, b.toNat, 0, 0, 0)

/-- Partial inverse of `Instr.toCode`. -/
def ofCode : ℕ × ℕ × ℕ × ℕ × ℕ → Option Instr
  | (0, r, b, next, _) => some (.push r (decide (b = 1)) next)
  | (1, r, jT, jF, jE) => some (.pop r jT jF jE)
  | (2, s, d, n, _) => some (.copy s d n)
  | (3, r, n, _, _) => some (.clear r n)
  | (4, r, jY, jN, _) => some (.query r jY jN)
  | (5, b, _, _, _) => some (.halt (decide (b = 1)))
  | _ => none

theorem ofCode_toCode (i : Instr) : ofCode (toCode i) = some i := by
  cases i with
  | push r b next => cases b <;> rfl
  | halt b => cases b <;> rfl
  | _ => rfl

end Instr

instance : Encodable Instr := Encodable.ofLeftInjection Instr.toCode Instr.ofCode Instr.ofCode_toCode

/-- A machine: a program together with a starting instruction address. -/
structure Machine where
  prog : List Instr
  start : ℕ
  deriving DecidableEq

instance : Encodable Machine :=
  Encodable.ofLeftInjection (fun M => (M.prog, M.start)) (fun p => some ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance : Inhabited Machine := ⟨⟨[], 0⟩⟩

/-- A configuration: program counter plus the contents of all registers. -/
structure Config where
  pc : ℕ
  regs : ℕ → Str

/-- Run the program `P` with oracle `A` for at most `fuel` time units starting from `c`.
Returns the answer (`none` if the machine ran out of fuel) together with the list of strings
queried along the way. -/
def exec (A : Oracle) (P : List Instr) : ℕ → Config → Option Bool × List Str
  | 0, _ => (none, [])
  | fuel + 1, c =>
    match P[c.pc]? with
    | none => (some false, [])
    | some (.halt b) => (some b, [])
    | some (.push r b next) =>
        exec A P fuel ⟨next, Function.update c.regs r (c.regs r ++ [b])⟩
    | some (.pop r jT jF jE) =>
        match c.regs r with
        | [] => exec A P fuel ⟨jE, c.regs⟩
        | b :: rest => exec A P fuel ⟨if b then jT else jF, Function.update c.regs r rest⟩
    | some (.clear r next) => exec A P fuel ⟨next, Function.update c.regs r []⟩
    | some (.copy src dst next) =>
        if fuel + 1 < (c.regs src).length + 1 then (none, [])
        else exec A P (fuel + 1 - ((c.regs src).length + 1))
              ⟨next, Function.update c.regs dst (c.regs dst ++ c.regs src)⟩
    | some (.query r jY jN) =>
        let res := exec A P fuel ⟨if A (c.regs r) then jY else jN, c.regs⟩
        (res.1, c.regs r :: res.2)
  termination_by fuel _ => fuel
  decreasing_by
    all_goals omega

/-- The answer produced by a run. -/
def runA (A : Oracle) (P : List Instr) (fuel : ℕ) (c : Config) : Option Bool :=
  (exec A P fuel c).1

/-- The list of strings queried during a run. -/
def queries (A : Oracle) (P : List Instr) (fuel : ℕ) (c : Config) : List Str :=
  (exec A P fuel c).2

/-- Initial configuration on input `x`, certificate `y` and padding `1^p`. -/
def initC (start : ℕ) (x y : Str) (p : ℕ) : Config :=
  ⟨start, fun r => if r = 0 then x else if r = 1 then y else
      if r = 2 then List.replicate p true else []⟩

/-- `Acc A M j k x y` says that machine `M` accepts input `x` with certificate `y`, when
given padding `1^((|x|+2)^j)` and `(|x|+2)^k` time steps. -/
def Acc (A : Oracle) (M : Machine) (j k : ℕ) (x y : Str) : Prop :=
  runA A M.prog ((x.length + 2) ^ k) (initC M.start x y ((x.length + 2) ^ j)) = some true

/-- `L` is in `P` relative to `A`. -/
def InP (A : Oracle) (L : Set Str) : Prop :=
  ∃ (M : Machine) (j k : ℕ), ∀ x, x ∈ L ↔ Acc A M j k x []

/-- `L` is in `NP` relative to `A`. -/
def InNP (A : Oracle) (L : Set Str) : Prop :=
  ∃ (M : Machine) (j k : ℕ), ∀ x,
    x ∈ L ↔ ∃ y : Str, y.length ≤ (x.length + 2) ^ k ∧ Acc A M j k x y

end CS

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

