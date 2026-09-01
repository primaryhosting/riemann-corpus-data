/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not permit a module docstring `/-! ... -/` before `import`; the header above is
-- reproduced verbatim as the module docstring immediately after the import.)
import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

open Equiv

/-! ## Boolean formulas (the `NC¹` side)

A `Formula n` is a fan-in-two Boolean formula over the variables `x 0, …, x (n-1)`.
Logarithmic-depth formulas are exactly (non-uniform) `NC¹`. -/

/-- Fan-in-two Boolean formulas over `n` variables. -/
inductive Formula (n : ℕ) : Type
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

namespace Formula

variable {n : ℕ}

/-- The Boolean function computed by a formula. -/
def eval : Formula n → (Fin n → Bool) → Bool
  | const b, _ => b
  | var i, x => x i
  | not F, x => !(F.eval x)
  | and F G, x => (F.eval x) && (G.eval x)
  | or F G, x => (F.eval x) || (G.eval x)

/-- The depth of a formula. -/
def depth : Formula n → ℕ
  | const _ => 0
  | var _ => 0
  | not F => F.depth + 1
  | and F G => max F.depth G.depth + 1
  | or F G => max F.depth G.depth + 1

/-- Disjunction of a list of formulas (right-nested). -/
def bigOr : List (Formula n) → Formula n
  | [] => const false
  | F :: t => or F (bigOr t)

lemma eval_bigOr (l : List (Formula n)) (x : Fin n → Bool) :
    (bigOr l).eval x = true ↔ ∃ F ∈ l, F.eval x = true := by
  induction l with
  | nil => simp [bigOr, eval]
  | cons F t ih => simp [bigOr, eval, ih]

lemma depth_bigOr (l : List (Formula n)) (D : ℕ) (h : ∀ F ∈ l, F.depth ≤ D) :
    (bigOr l).depth ≤ D + l.length := by
  induction l with
  | nil => simp [bigOr, depth]
  | cons F t ih =>
    have h1 : F.depth ≤ D := h F (by simp)
    have h2 := ih (fun G hG => h G (by simp [hG]))
    simp only [bigOr, depth, List.length_cons]
    omega

end Formula

/-! ## Width-5 permutation branching programs -/

/-- The symmetric group on five points, the "width 5" of the model. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A single layer of a width-5 permutation branching program: either it queries an input
bit and applies one of two permutations, or it applies a fixed permutation. -/
inductive Instr (n : ℕ) : Type
  | query : Fin n → Perm5 → Perm5 → Instr n
  | konst : Perm5 → Instr n

namespace Instr

variable {n : ℕ}

/-- The permutation applied by a layer on a given input. -/
def eval : Instr n → (Fin n → Bool) → Perm5
  | query i a b, x => if x i then b else a
  | konst a, _ => a

/-- Multiply the layer's permutations on the left by `α`. -/
def mulLeft (α : Perm5) : Instr n → Instr n
  | query i a b => query i (α * a) (α * b)
  | konst a => konst (α * a)

/-- Invert the layer's permutations. -/
def inv : Instr n → Instr n
  | query i a b => query i a⁻¹ b⁻¹
  | konst a => konst a⁻¹

@[simp] lemma eval_mulLeft (α : Perm5) (ι : Instr n) (x : Fin n → Bool) :
    (ι.mulLeft α).eval x = α * ι.eval x := by
  cases ι with
  | query i a b => simp only [mulLeft, eval]; split <;> rfl
  | konst a => rfl

@[simp] lemma eval_inv (ι : Instr n) (x : Fin n → Bool) :
    (Instr.inv ι).eval x = (ι.eval x)⁻¹ := by
  cases ι with
  | query i a b => simp only [Instr.inv, eval]; split <;> rfl
  | konst a => rfl

end Instr

/-- A width-5 permutation branching program on `n` input bits is a list of layers.
Its length is the number of layers. -/
abbrev BP (n : ℕ) := List (Instr n)

namespace BP

variable {n : ℕ}

/-- The permutation computed by a program on a given input: the product of the layers. -/
def eval (P : BP n) (x : Fin n → Bool) : Perm5 := (P.map (fun ι => ι.eval x)).prod

@[simp] lemma eval_nil (x : Fin n → Bool) : eval ([] : BP n) x = 1 := rfl

@[simp] lemma eval_cons (ι : Instr n) (P : BP n) (x : Fin n → Bool) :
    eval (ι :: P) x = ι.eval x * eval P x := rfl

@[simp] lemma eval_append (P Q : BP n) (x : Fin n → Bool) :
    eval (P ++ Q) x = eval P x * eval Q x := by
  simp [eval, List.prod_append]

/-- Multiply the whole program's output on the left by `α`, without changing the length
(except that the empty program grows to one layer). -/
def mulLeft (α : Perm5) : BP n → BP n
  | [] => [Instr.konst α]
  | ι :: t => ι.mulLeft α :: t

/-- The program computing the inverse permutation. -/
def inv (P : BP n) : BP n := (P.map Instr.inv).reverse

@[simp] lemma eval_mulLeft (α : Perm5) (P : BP n) (x : Fin n → Bool) :
    eval (mulLeft α P) x = α * eval P x := by
  cases P with
  | nil => simp [mulLeft, eval, Instr.eval]
  | cons ι t => simp [mulLeft, mul_assoc]

@[simp] lemma eval_inv (P : BP n) (x : Fin n → Bool) :
    eval (inv P) x = (eval P x)⁻¹ := by
  simp [inv, eval, List.prod_inv_reverse, List.map_reverse, List.map_map, Function.comp_def]

lemma length_mulLeft (α : Perm5) (P : BP n) : (mulLeft α P).length ≤ max 1 P.length := by
  cases P <;> simp [mulLeft]

@[simp] lemma length_inv (P : BP n) : (inv P).length = P.length := by simp [inv]

end BP

/-- `P` computes the Boolean function `f` with the permutation `σ`: on inputs where `f` is
true the program's product is `σ`, and elsewhere it is the identity. -/
def Computes {n : ℕ} (P : BP n) (σ : Perm5) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, P.eval x = if f x then σ else 1

lemma Computes.congr {n : ℕ} {P : BP n} {σ : Perm5} {f g : (Fin n → Bool) → Bool}
    (h : Computes P σ f) (hfg : ∀ x, f x = g x) : Computes P σ g := by
  intro x; rw [h x, hfg x]

/-- `σ` is a 5-cycle in `S₅`. -/
def IsFiveCycle (σ : Perm5) : Prop := σ.IsCycle ∧ σ.support.card = 5

lemma IsFiveCycle.ne_one {σ : Perm5} (h : IsFiveCycle σ) : σ ≠ 1 := by
  rintro rfl
  simp [IsFiveCycle, Equiv.Perm.support_one] at h


/-! ## Group-theoretic core: 5-cycles are commutators of 5-cycles -/

lemma IsFiveCycle.conj {σ : Perm5} (h : IsFiveCycle σ) (γ : Perm5) :
    IsFiveCycle (γ * σ * γ⁻¹) := by
  refine ⟨h.1.conj, ?_⟩
  rw [Equiv.Perm.support_conj, Finset.card_map]
  exact h.2

lemma isConj_of_isFiveCycle {σ τ : Perm5} (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    IsConj σ τ := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq, hσ.1.cycleType, hτ.1.cycleType, hσ.2, hτ.2]

/-- Every 5-cycle of `S₅` is the commutator of two 5-cycles.  This is the group-theoretic
heart of Barrington's theorem. -/
lemma exists_commutator (σ : Perm5) (hσ : IsFiveCycle σ) :
    ∃ τ ρ : Perm5, IsFiveCycle τ ∧ IsFiveCycle ρ ∧ τ * ρ * τ⁻¹ * ρ⁻¹ = σ := by
  have ht : IsFiveCycle (c[(0 : Fin 5), 1, 2, 3, 4] : Perm5) :=
    ⟨by apply List.isCycle_formPerm <;> decide, by decide⟩
  have hr : IsFiveCycle (c[(0 : Fin 5), 1, 3, 4, 2] : Perm5) :=
    ⟨by apply List.isCycle_formPerm <;> decide, by decide⟩
  have hcomm : (c[(0 : Fin 5), 1, 2, 3, 4] : Perm5) * c[(0 : Fin 5), 1, 3, 4, 2] *
      (c[(0 : Fin 5), 1, 2, 3, 4] : Perm5)⁻¹ * (c[(0 : Fin 5), 1, 3, 4, 2] : Perm5)⁻¹
      = c[(0 : Fin 5), 4, 1, 3, 2] := by decide
  have hs : IsFiveCycle ((c[(0 : Fin 5), 1, 2, 3, 4] : Perm5) * c[(0 : Fin 5), 1, 3, 4, 2] *
      (c[(0 : Fin 5), 1, 2, 3, 4] : Perm5)⁻¹ * (c[(0 : Fin 5), 1, 3, 4, 2] : Perm5)⁻¹) := by
    rw [hcomm]
    exact ⟨by apply List.isCycle_formPerm <;> decide, by decide⟩
  obtain ⟨γ, hγ⟩ := isConj_iff.1 (isConj_of_isFiveCycle hs hσ)
  refine ⟨γ * c[(0 : Fin 5), 1, 2, 3, 4] * γ⁻¹, γ * c[(0 : Fin 5), 1, 3, 4, 2] * γ⁻¹,
    ht.conj γ, hr.conj γ, ?_⟩
  rw [← hγ]; group

/-! ## Formulas of depth `d` are simulated by programs of length `4 ^ d` -/

lemma computes_not {n : ℕ} {P : BP n} {σ : Perm5} {f : (Fin n → Bool) → Bool}
    (h : Computes P σ f) : Computes (BP.mulLeft σ (BP.inv P)) σ (fun x => !f x) := by
  intro x
  simp only [BP.eval_mulLeft, BP.eval_inv, h x]
  by_cases hf : f x <;> simp [hf]

lemma computes_and {n : ℕ} {σ τ ρ : Perm5} (hc : τ * ρ * τ⁻¹ * ρ⁻¹ = σ) {P Q : BP n}
    {f g : (Fin n → Bool) → Bool} (hP : Computes P τ f) (hQ : Computes Q ρ g) :
    Computes (P ++ Q ++ BP.inv P ++ BP.inv Q) σ (fun x => f x && g x) := by
  intro x
  simp only [BP.eval_append, BP.eval_inv, hP x, hQ x]
  by_cases hf : f x = true <;> by_cases hg : g x = true <;> simp [hf, hg, hc]

lemma length_and_prog {n : ℕ} (P Q : BP n) :
    (P ++ Q ++ BP.inv P ++ BP.inv Q).length = 2 * (P.length + Q.length) := by
  simp; omega

private lemma pow4_le {d m : ℕ} (h : d ≤ m) : (4 : ℕ) ^ d ≤ 4 ^ m :=
  Nat.pow_le_pow_right (by norm_num) h

private lemma two_add_pow4 (d₁ d₂ m : ℕ) (h₁ : d₁ ≤ m) (h₂ : d₂ ≤ m) :
    2 * ((4 : ℕ) ^ d₁ + 4 ^ d₂) ≤ 4 ^ (m + 1) := by
  have a₁ := pow4_le h₁
  have a₂ := pow4_le h₂
  have : (4 : ℕ) ^ (m + 1) = 4 * 4 ^ m := by ring
  omega

/-- **Barrington's simulation.**  Every fan-in-two Boolean formula of depth `d` is computed,
for *every* prescribed 5-cycle `σ`, by a width-5 permutation branching program with at most
`4 ^ d` layers. -/
theorem exists_bp {n : ℕ} (F : Formula n) :
    ∀ σ : Perm5, IsFiveCycle σ → ∃ P : BP n, P.length ≤ 4 ^ F.depth ∧ Computes P σ F.eval := by
  induction F with
  | const b =>
      intro σ _
      refine ⟨[Instr.konst (if b then σ else 1)], by simp [Formula.depth], ?_⟩
      intro x
      simp [BP.eval, Instr.eval, Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[Instr.query i 1 σ], by simp [Formula.depth], ?_⟩
      intro x
      by_cases h : x i = true <;> simp [BP.eval, Instr.eval, Formula.eval, h]
  | not F ih =>
      intro σ hσ
      obtain ⟨P, hlen, hc⟩ := ih σ hσ
      refine ⟨BP.mulLeft σ (BP.inv P), ?_, (computes_not hc).congr (fun x => rfl)⟩
      have h1 := BP.length_mulLeft σ (BP.inv P)
      have h2 : (BP.inv P).length = P.length := BP.length_inv P
      have h3 : (4 : ℕ) ^ F.depth ≤ 4 ^ (F.depth + 1) := pow4_le (Nat.le_succ _)
      have h4 : 1 ≤ (4 : ℕ) ^ (F.depth + 1) := Nat.one_le_pow _ _ (by norm_num)
      simp only [Formula.depth]
      omega
  | and F G ihF ihG =>
      intro σ hσ
      obtain ⟨τ, ρ, hτ, hρ, hc⟩ := exists_commutator σ hσ
      obtain ⟨P, hlP, hcP⟩ := ihF τ hτ
      obtain ⟨Q, hlQ, hcQ⟩ := ihG ρ hρ
      refine ⟨P ++ Q ++ BP.inv P ++ BP.inv Q, ?_,
        (computes_and hc hcP hcQ).congr (fun x => rfl)⟩
      rw [length_and_prog]
      have := two_add_pow4 F.depth G.depth (max F.depth G.depth) (le_max_left _ _)
        (le_max_right _ _)
      simp only [Formula.depth]
      omega
  | or F G ihF ihG =>
      intro σ hσ
      obtain ⟨τ, ρ, hτ, hρ, hc⟩ := exists_commutator σ hσ
      obtain ⟨P, hlP, hcP⟩ := ihF τ hτ
      obtain ⟨Q, hlQ, hcQ⟩ := ihG ρ hρ
      set N₁ : BP n := BP.mulLeft τ (BP.inv P) with hN₁
      set N₂ : BP n := BP.mulLeft ρ (BP.inv Q) with hN₂
      have hcN₁ : Computes N₁ τ (fun x => !F.eval x) := computes_not hcP
      have hcN₂ : Computes N₂ ρ (fun x => !G.eval x) := computes_not hcQ
      set R : BP n := N₁ ++ N₂ ++ BP.inv N₁ ++ BP.inv N₂ with hR
      have hcR : Computes R σ (fun x => (!F.eval x) && (!G.eval x)) :=
        computes_and hc hcN₁ hcN₂
      refine ⟨BP.mulLeft σ (BP.inv R), ?_, (computes_not hcR).congr ?_⟩
      · have e1 : N₁.length ≤ max 1 P.length := by
          rw [hN₁]; simpa using BP.length_mulLeft τ (BP.inv P)
        have e2 : N₂.length ≤ max 1 Q.length := by
          rw [hN₂]; simpa using BP.length_mulLeft ρ (BP.inv Q)
        have e3 := BP.length_mulLeft σ (BP.inv R)
        have e4 : (BP.inv R).length = R.length := BP.length_inv R
        have e5 : R.length = 2 * (N₁.length + N₂.length) := by rw [hR, length_and_prog]
        have e6 := two_add_pow4 F.depth G.depth (max F.depth G.depth) (le_max_left _ _)
          (le_max_right _ _)
        have e7 : 1 ≤ (4 : ℕ) ^ F.depth := Nat.one_le_pow _ _ (by norm_num)
        have e8 : 1 ≤ (4 : ℕ) ^ G.depth := Nat.one_le_pow _ _ (by norm_num)
        have e9 : 1 ≤ (4 : ℕ) ^ (max F.depth G.depth + 1) := Nat.one_le_pow _ _ (by norm_num)
        simp only [Formula.depth]
        omega
      · intro x
        show (!((!F.eval x) && (!G.eval x))) = (Formula.or F G).eval x
        simp [Formula.eval]

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

