import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Equiv Equiv.Perm

/-! ## Boolean formulas -/

/-- Boolean formulas over the (functionally complete) basis `{¬, ∧, ∨}` with constants,
with variables indexed by `ℕ`. -/
inductive BFormula where
  | const : Bool → BFormula
  | var : ℕ → BFormula
  | neg : BFormula → BFormula
  | and : BFormula → BFormula → BFormula
  | or : BFormula → BFormula → BFormula
  deriving DecidableEq

namespace BFormula

/-- Semantics of a Boolean formula. -/
def eval : BFormula → (ℕ → Bool) → Bool
  | const b, _ => b
  | var i, x => x i
  | neg F, x => !(F.eval x)
  | and F G, x => F.eval x && G.eval x
  | or F G, x => F.eval x || G.eval x

/-- Depth of a Boolean formula (number of gates on a longest root-to-leaf path). -/
def depth : BFormula → ℕ
  | const _ => 0
  | var _ => 0
  | neg F => F.depth + 1
  | and F G => max F.depth G.depth + 1
  | or F G => max F.depth G.depth + 1

@[simp] lemma eval_const (b : Bool) (x : ℕ → Bool) : (const b).eval x = b := rfl
@[simp] lemma eval_var (i : ℕ) (x : ℕ → Bool) : (var i).eval x = x i := rfl
@[simp] lemma eval_neg (F : BFormula) (x : ℕ → Bool) : (neg F).eval x = !(F.eval x) := rfl
@[simp] lemma eval_and (F G : BFormula) (x : ℕ → Bool) :
    (and F G).eval x = (F.eval x && G.eval x) := rfl
@[simp] lemma eval_or (F G : BFormula) (x : ℕ → Bool) :
    (or F G).eval x = (F.eval x || G.eval x) := rfl

@[simp] lemma depth_const (b : Bool) : (const b).depth = 0 := rfl
@[simp] lemma depth_var (i : ℕ) : (var i).depth = 0 := rfl
@[simp] lemma depth_neg (F : BFormula) : (neg F).depth = F.depth + 1 := rfl
@[simp] lemma depth_and (F G : BFormula) : (and F G).depth = max F.depth G.depth + 1 := rfl
@[simp] lemma depth_or (F G : BFormula) : (or F G).depth = max F.depth G.depth + 1 := rfl

end BFormula

/-! ## Width-5 permutation branching programs -/

/-- The group `S₅`. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A single instruction of a width-5 permutation branching program: read variable `i`,
apply the first permutation if it is `false` and the second one if it is `true`. -/
abbrev Instr := ℕ × Perm5 × Perm5

/-- A width-5 permutation branching program is a list of instructions. -/
abbrev Prog := List Instr

/-- The permutation applied by a single instruction on a given input. -/
def instrVal (x : ℕ → Bool) (e : Instr) : Perm5 := if x e.1 then e.2.2 else e.2.1

/-- The permutation computed by a program on a given input: the ordered product of the
permutations selected by the instructions. -/
def run (P : Prog) (x : ℕ → Bool) : Perm5 := (P.map (instrVal x)).prod

/-- `P` `σ`-computes `f`: the program outputs `σ` on inputs accepted by `f` and the
identity on the other inputs. -/
def Computes (P : Prog) (σ : Perm5) (f : (ℕ → Bool) → Bool) : Prop :=
  ∀ x, run P x = if f x then σ else 1

@[simp] lemma run_nil (x : ℕ → Bool) : run [] x = 1 := rfl

@[simp] lemma run_cons (e : Instr) (P : Prog) (x : ℕ → Bool) :
    run (e :: P) x = instrVal x e * run P x := rfl

@[simp] lemma run_append (P Q : Prog) (x : ℕ → Bool) :
    run (P ++ Q) x = run P x * run Q x := by
  simp [run, List.map_append, List.prod_append]

/-- A permutation of `Fin 5` is a five-cycle iff its cycle type is `{5}`. -/
def IsFiveCycle (σ : Perm5) : Prop := σ.cycleType = {5}

lemma IsFiveCycle.inv {σ : Perm5} (h : IsFiveCycle σ) : IsFiveCycle σ⁻¹ := by
  unfold IsFiveCycle at *; rwa [Equiv.Perm.cycleType_inv]

lemma IsFiveCycle.conj {σ : Perm5} (h : IsFiveCycle σ) (t : Perm5) :
    IsFiveCycle (t * σ * t⁻¹) := by
  unfold IsFiveCycle at *; rwa [Equiv.Perm.cycleType_conj]

/-- Any two five-cycles of `S₅` are conjugate. -/
lemma exists_conj_of_isFiveCycle {σ τ : Perm5} (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    ∃ t : Perm5, t * σ * t⁻¹ = τ := by
  have : IsConj σ τ := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hσ, hτ]
  rw [isConj_iff] at this
  exact this

/-! ### Basic program constructions -/

/-- Conjugating every instruction of a program by `t`. -/
def conjProg (t : Perm5) (P : Prog) : Prog :=
  P.map (fun e => (e.1, t * e.2.1 * t⁻¹, t * e.2.2 * t⁻¹))

@[simp] lemma length_conjProg (t : Perm5) (P : Prog) : (conjProg t P).length = P.length := by
  simp [conjProg]

lemma conjProg_ne_nil {t : Perm5} {P : Prog} (h : P ≠ []) : conjProg t P ≠ [] := by
  simpa [conjProg] using h

@[simp] lemma run_conjProg (t : Perm5) (P : Prog) (x : ℕ → Bool) :
    run (conjProg t P) x = t * run P x * t⁻¹ := by
  induction P with
  | nil => simp [conjProg]
  | cons e P ih =>
      have hval : instrVal x (e.1, t * e.2.1 * t⁻¹, t * e.2.2 * t⁻¹)
          = t * instrVal x e * t⁻¹ := by
        unfold instrVal; by_cases h : x e.1 <;> simp [h]
      simp only [conjProg, List.map_cons] at *
      rw [run_cons, ih, hval, run_cons]
      group

lemma computes_conj {P : Prog} {σ : Perm5} {f : (ℕ → Bool) → Bool} (t : Perm5)
    (h : Computes P σ f) : Computes (conjProg t P) (t * σ * t⁻¹) f := by
  intro x
  rw [run_conjProg, h x]
  by_cases hf : f x <;> simp [hf]

/-- Multiply the last instruction of a program on the right by `g`. -/
def mulLast (g : Perm5) : Prog → Prog
  | [] => []
  | [e] => [(e.1, e.2.1 * g, e.2.2 * g)]
  | e :: f :: rest => e :: mulLast g (f :: rest)

@[simp] lemma length_mulLast (g : Perm5) (P : Prog) : (mulLast g P).length = P.length := by
  induction P with
  | nil => rfl
  | cons e P ih =>
      cases P with
      | nil => rfl
      | cons f rest => simpa [mulLast] using ih

lemma mulLast_ne_nil {g : Perm5} {P : Prog} (h : P ≠ []) : mulLast g P ≠ [] := by
  cases P with
  | nil => exact absurd rfl h
  | cons e Q => cases Q <;> simp [mulLast]

lemma run_mulLast (g : Perm5) {P : Prog} (hP : P ≠ []) (x : ℕ → Bool) :
    run (mulLast g P) x = run P x * g := by
  induction P with
  | nil => exact absurd rfl hP
  | cons e P ih =>
      cases P with
      | nil =>
          have hval : instrVal x (e.1, e.2.1 * g, e.2.2 * g) = instrVal x e * g := by
            unfold instrVal; by_cases h : x e.1 <;> simp [h]
          simp [mulLast, hval]
      | cons f rest =>
          have h2 : (f :: rest : Prog) ≠ [] := by simp
          simp only [mulLast]
          rw [run_cons, ih h2]
          simp [run_cons, mul_assoc]

/-- Negation is free: from a program `σ`-computing `f` we get one of the same length
`σ`-computing `¬f`. -/
lemma computes_not {P : Prog} {σ : Perm5} {f : (ℕ → Bool) → Bool} (hP : P ≠ [])
    (hσ : IsFiveCycle σ) (h : Computes P σ f) :
    ∃ Q : Prog, Q ≠ [] ∧ Q.length = P.length ∧ Computes Q σ (fun x => !(f x)) := by
  obtain ⟨t, ht⟩ := exists_conj_of_isFiveCycle hσ.inv hσ
  refine ⟨conjProg t (mulLast σ⁻¹ P), conjProg_ne_nil (mulLast_ne_nil hP), by simp, ?_⟩
  have hbase : Computes (mulLast σ⁻¹ P) σ⁻¹ (fun x => !(f x)) := by
    intro x
    rw [run_mulLast _ hP, h x]
    by_cases hf : f x <;> simp [hf]
  have := computes_conj t hbase
  rwa [ht] at this

/-- The commutator construction: this is the heart of Barrington's theorem. -/
lemma computes_and_comm {P₁ P₂ P₃ P₄ : Prog} {α β : Perm5} {f g : (ℕ → Bool) → Bool}
    (h₁ : Computes P₁ α f) (h₂ : Computes P₂ β g)
    (h₃ : Computes P₃ α⁻¹ f) (h₄ : Computes P₄ β⁻¹ g) :
    Computes (P₁ ++ P₂ ++ P₃ ++ P₄) (α * β * α⁻¹ * β⁻¹) (fun x => f x && g x) := by
  intro x
  rw [run_append, run_append, run_append, h₁ x, h₂ x, h₃ x, h₄ x]
  by_cases hf : f x <;> by_cases hg : g x <;> simp [hf, hg]

/-! ### The group-theoretic input -/

private def alpha5 : Perm5 := c[0, 1, 2, 3, 4]
private def beta5 : Perm5 := c[0, 3, 4, 1, 2]

private lemma alpha5_isFiveCycle : IsFiveCycle alpha5 := by unfold IsFiveCycle; decide
private lemma beta5_isFiveCycle : IsFiveCycle beta5 := by unfold IsFiveCycle; decide
private lemma comm_isFiveCycle : IsFiveCycle (alpha5 * beta5 * alpha5⁻¹ * beta5⁻¹) := by
  unfold IsFiveCycle; decide

/-- Every five-cycle of `S₅` is the commutator of two five-cycles. -/
lemma exists_commutator {σ : Perm5} (hσ : IsFiveCycle σ) :
    ∃ α β : Perm5, IsFiveCycle α ∧ IsFiveCycle β ∧ α * β * α⁻¹ * β⁻¹ = σ := by
  obtain ⟨t, ht⟩ := exists_conj_of_isFiveCycle comm_isFiveCycle hσ
  refine ⟨t * alpha5 * t⁻¹, t * beta5 * t⁻¹, alpha5_isFiveCycle.conj t,
    beta5_isFiveCycle.conj t, ?_⟩
  rw [← ht]
  group

/-! ## Barrington's theorem: formulas to width-5 branching programs -/

/-- **Barrington's theorem** (the hard direction).  For every Boolean formula `F` of depth `d`
and every five-cycle `σ` there is a width-5 permutation branching program of length at most
`4 ^ d` which `σ`-computes `F`. -/
theorem formula_to_prog (F : BFormula) :
    ∀ σ : Perm5, IsFiveCycle σ →
      ∃ P : Prog, P ≠ [] ∧ P.length ≤ 4 ^ F.depth ∧ Computes P σ F.eval := by
  induction F with
  | const b =>
      intro σ _
      refine ⟨[(0, if b then σ else 1, if b then σ else 1)], by simp, by simp, ?_⟩
      intro x
      cases b <;> simp [run, instrVal, BFormula.eval]
  | var i =>
      intro σ _
      refine ⟨[(i, 1, σ)], by simp, by simp, ?_⟩
      intro x
      by_cases h : x i <;> simp [run, instrVal, BFormula.eval, h]
  | neg F ih =>
      intro σ hσ
      obtain ⟨P, hPne, hPlen, hP⟩ := ih σ hσ
      obtain ⟨Q, hQne, hQlen, hQ⟩ := computes_not hPne hσ hP
      refine ⟨Q, hQne, ?_, hQ⟩
      calc Q.length = P.length := hQlen
        _ ≤ 4 ^ F.depth := hPlen
        _ ≤ 4 ^ (F.depth + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  | and F G ihF ihG =>
      intro σ hσ
      obtain ⟨α, β, hα, hβ, hcomm⟩ := exists_commutator hσ
      obtain ⟨P₁, h1ne, h1len, h1⟩ := ihF α hα
      obtain ⟨P₂, h2ne, h2len, h2⟩ := ihG β hβ
      obtain ⟨P₃, h3ne, h3len, h3⟩ := ihF α⁻¹ hα.inv
      obtain ⟨P₄, h4ne, h4len, h4⟩ := ihG β⁻¹ hβ.inv
      refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, by simp [h1ne], ?_, ?_⟩
      · have hF : (4 : ℕ) ^ F.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hG : (4 : ℕ) ^ G.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        simp only [BFormula.depth_and, List.length_append, pow_succ]
        omega
      · have := computes_and_comm h1 h2 h3 h4
        rw [hcomm] at this
        exact this
  | or F G ihF ihG =>
      intro σ hσ
      obtain ⟨α, β, hα, hβ, hcomm⟩ := exists_commutator hσ.inv
      obtain ⟨P₁, h1ne, h1len, h1⟩ := ihF α hα
      obtain ⟨P₂, h2ne, h2len, h2⟩ := ihG β hβ
      obtain ⟨P₃, h3ne, h3len, h3⟩ := ihF α⁻¹ hα.inv
      obtain ⟨P₄, h4ne, h4len, h4⟩ := ihG β⁻¹ hβ.inv
      -- negate each of the four programs (for free)
      obtain ⟨Q₁, q1ne, q1len, q1⟩ := computes_not h1ne hα h1
      obtain ⟨Q₂, q2ne, q2len, q2⟩ := computes_not h2ne hβ h2
      obtain ⟨Q₃, q3ne, q3len, q3⟩ := computes_not h3ne hα.inv h3
      obtain ⟨Q₄, q4ne, q4len, q4⟩ := computes_not h4ne hβ.inv h4
      have hand := computes_and_comm q1 q2 q3 q4
      rw [hcomm] at hand
      obtain ⟨R, hRne, hRlen, hR⟩ := computes_not (P := Q₁ ++ Q₂ ++ Q₃ ++ Q₄)
        (by simp [q1ne]) hσ.inv hand
      obtain ⟨t, ht⟩ := exists_conj_of_isFiveCycle hσ.inv hσ
      refine ⟨conjProg t R, conjProg_ne_nil hRne, ?_, ?_⟩
      · have hF : (4 : ℕ) ^ F.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hG : (4 : ℕ) ^ G.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        simp only [length_conjProg, hRlen, List.length_append, q1len, q2len, q3len, q4len,
          BFormula.depth_or, pow_succ]
        omega
      · have hc := computes_conj t hR
        rw [ht] at hc
        intro x
        rw [hc x]
        simp [BFormula.eval]

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

