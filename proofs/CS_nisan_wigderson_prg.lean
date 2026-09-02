/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits over a variable type `α`, with gates `¬` and `∧` and constants. -/
inductive Circ (α : Type) where
  | var (a : α) : Circ α
  | const (b : Bool) : Circ α
  | neg (c : Circ α) : Circ α
  | conj (c₁ c₂ : Circ α) : Circ α

namespace Circ

variable {α β : Type}

/-- The Boolean function computed by a circuit. -/
def eval : Circ α → (α → Bool) → Bool
  | var a, x => x a
  | const b, _ => b
  | neg c, x => !(c.eval x)
  | conj c₁ c₂, x => (c₁.eval x) && (c₂.eval x)

/-- The number of gates of a circuit. -/
def size : Circ α → ℕ
  | var _ => 1
  | const _ => 1
  | neg c => c.size + 1
  | conj c₁ c₂ => c₁.size + c₂.size + 1

@[simp] lemma eval_var (a : α) (x : α → Bool) : (var a).eval x = x a := rfl
@[simp] lemma eval_const (b : Bool) (x : α → Bool) : (const b : Circ α).eval x = b := rfl
@[simp] lemma eval_neg (c : Circ α) (x : α → Bool) : (neg c).eval x = !(c.eval x) := rfl
@[simp] lemma eval_conj (c₁ c₂ : Circ α) (x : α → Bool) :
    (conj c₁ c₂).eval x = ((c₁.eval x) && (c₂.eval x)) := rfl

@[simp] lemma size_var (a : α) : (var a).size = 1 := rfl
@[simp] lemma size_const (b : Bool) : (const b : Circ α).size = 1 := rfl
@[simp] lemma size_neg (c : Circ α) : (neg c).size = c.size + 1 := rfl
@[simp] lemma size_conj (c₁ c₂ : Circ α) : (conj c₁ c₂).size = c₁.size + c₂.size + 1 := rfl

/-- Disjunction, via de Morgan. -/
def disj (c₁ c₂ : Circ α) : Circ α := neg (conj (neg c₁) (neg c₂))

@[simp] lemma eval_disj (c₁ c₂ : Circ α) (x : α → Bool) :
    (disj c₁ c₂).eval x = ((c₁.eval x) || (c₂.eval x)) := by
  simp [disj]

@[simp] lemma size_disj (c₁ c₂ : Circ α) : (disj c₁ c₂).size = c₁.size + c₂.size + 4 := by
  simp [disj]; omega

/-- Substituting a circuit for each variable. -/
def subst : Circ β → (β → Circ α) → Circ α
  | var b, τ => τ b
  | const b, _ => const b
  | neg c, τ => neg (c.subst τ)
  | conj c₁ c₂, τ => conj (c₁.subst τ) (c₂.subst τ)

lemma eval_subst (c : Circ β) (τ : β → Circ α) (x : α → Bool) :
    (c.subst τ).eval x = c.eval (fun b => (τ b).eval x) := by
  induction c with
  | var b => rfl
  | const b => rfl
  | neg c ih => simp [subst, ih]
  | conj c₁ c₂ ih₁ ih₂ => simp [subst, ih₁, ih₂]

lemma size_subst_le (c : Circ β) (τ : β → Circ α) (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ b, (τ b).size ≤ t) : (c.subst τ).size ≤ c.size * t := by
  induction c with
  | var b => simpa [subst] using h b
  | const b => simpa [subst] using ht
  | neg c ih => simp only [subst, size_neg, add_mul, one_mul]; omega
  | conj c₁ c₂ ih₁ ih₂ =>
      simp only [subst, size_conj, add_mul, one_mul]; omega

/-- Every Boolean function depending only on the coordinates in a finite set `S` is computed
by a circuit of size at most `10 * 2 ^ |S|`. -/
lemma exists_of_support [DecidableEq α] (S : Finset α) :
    ∀ g : (α → Bool) → Bool, (∀ x y, (∀ a ∈ S, x a = y a) → g x = g y) →
      ∃ c : Circ α, (∀ x, c.eval x = g x) ∧ c.size + 9 ≤ 10 * 2 ^ S.card := by
  induction S using Finset.induction_on with
  | empty =>
      intro g hg
      refine ⟨const (g (fun _ => false)), fun x => ?_, by simp⟩
      simpa using (hg x (fun _ => false) (by simp)).symm ▸ rfl
  | insert a T ha ih =>
      intro g hg
      have hsupp : ∀ b : Bool, ∀ x y : α → Bool, (∀ i ∈ T, x i = y i) →
          g (Function.update x a b) = g (Function.update y a b) := by
        intro b x y hxy
        refine hg _ _ ?_
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hiT
        · simp
        · have hia : i ≠ a := fun h => ha (h ▸ hiT)
          simp [hia, hxy i hiT]
      obtain ⟨c0, hc0, hs0⟩ := ih (fun x => g (Function.update x a false)) (hsupp false)
      obtain ⟨c1, hc1, hs1⟩ := ih (fun x => g (Function.update x a true)) (hsupp true)
      refine ⟨disj (conj (var a) c1) (conj (neg (var a)) c0), fun x => ?_, ?_⟩
      · cases hx : x a with
        | false =>
            simp only [eval_disj, eval_conj, eval_var, eval_neg, hx, Bool.not_false,
              Bool.true_and, Bool.false_and, Bool.false_or, hc0]
            rw [show Function.update x a false = x by rw [← hx]; exact Function.update_eq_self a x]
        | true =>
            simp only [eval_disj, eval_conj, eval_var, eval_neg, hx, Bool.not_true,
              Bool.true_and, Bool.false_and, Bool.or_false, hc1]
            rw [show Function.update x a true = x by rw [← hx]; exact Function.update_eq_self a x]
      · rw [Finset.card_insert_of_notMem ha, pow_succ]
        simp only [size_disj, size_conj, size_var, size_neg]
        omega

end Circ

/-! ## Probability helpers -/

/-- Indicator of a Boolean value. -/
def ind (b : Bool) : ℚ := if b = true then 1 else 0

/-- Indicator that two Boolean values agree. -/
def agree (u v : Bool) : ℚ := if u = v then 1 else 0

@[simp] lemma ind_true : ind true = 1 := rfl
@[simp] lemma ind_false : ind false = 0 := rfl

lemma ind_not (b : Bool) : ind (!b) = 1 - ind b := by cases b <;> simp

/-- Symmetrisation: two functions with the same `ι`-symmetrised values have the same sum. -/
lemma sum_eq_of_involutive {α : Type*} [Fintype α] (ι : α → α) (hι : Function.Involutive ι)
    (H R : α → ℚ) (h : ∀ a, H a + H (ι a) = R a + R (ι a)) :
    ∑ a, H a = ∑ a, R a := by
  have key : ∀ F : α → ℚ, ∑ a, F (ι a) = ∑ a, F a := fun F => Equiv.sum_comp (hι.toPerm) F
  have h2 : (2 : ℚ) * ∑ a, H a = 2 * ∑ a, R a := by
    have e1 : ∑ a, (H a + H (ι a)) = ∑ a, (R a + R (ι a)) := Finset.sum_congr rfl fun a _ => h a
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, key H, key R] at e1
    linarith [e1]
  linarith

/-- Overwrite the coordinates in the image of `σ` by `y`. -/
noncomputable def plug {n ℓ : ℕ} (σ : Fin ℓ → Fin n) (x : Fin n → Bool) (y : Fin ℓ → Bool) : Fin n → Bool :=
  fun i => if h : ∃ a, σ a = i then y h.choose else x i

lemma plug_apply_mem {n ℓ : ℕ} {σ : Fin ℓ → Fin n} (hσ : Function.Injective σ)
    (x : Fin n → Bool) (y : Fin ℓ → Bool) (a : Fin ℓ) : plug σ x y (σ a) = y a := by
  have hex : ∃ b, σ b = σ a := ⟨a, rfl⟩
  rw [plug, dif_pos hex]
  exact congrArg y (hσ hex.choose_spec)

lemma plug_apply_not_mem {n ℓ : ℕ} {σ : Fin ℓ → Fin n} (x : Fin n → Bool) (y : Fin ℓ → Bool)
    {i : Fin n} (h : ¬ ∃ a, σ a = i) : plug σ x y i = x i := dif_neg h

/-- The map `(x, y) ↦ (plug x y, x ∘ σ)` is an involution of `Bool^n × Bool^ℓ`. -/
lemma plug_involutive {n ℓ : ℕ} {σ : Fin ℓ → Fin n} (hσ : Function.Injective σ) :
    Function.Involutive
      (fun p : (Fin n → Bool) × (Fin ℓ → Bool) => (plug σ p.1 p.2, fun a => p.1 (σ a))) := by
  rintro ⟨x, y⟩
  have h1 : (fun a => plug σ x y (σ a)) = y := funext fun a => plug_apply_mem hσ x y a
  refine Prod.ext ?_ h1
  refine funext fun i => ?_
  by_cases hi : ∃ a, σ a = i
  · obtain ⟨a, rfl⟩ := hi
    simp [plug_apply_mem hσ]
  · simp [plug_apply_not_mem _ _ hi]

/-- Averaging over the plugged coordinates. -/
lemma sum_plug {n ℓ : ℕ} {σ : Fin ℓ → Fin n} (hσ : Function.Injective σ)
    (F : (Fin n → Bool) → ℚ) :
    ∑ p : (Fin n → Bool) × (Fin ℓ → Bool), F (plug σ p.1 p.2) = 2 ^ ℓ * ∑ x, F x := by
  have h := Equiv.sum_comp ((plug_involutive hσ).toPerm) (fun p : (Fin n → Bool) × (Fin ℓ → Bool) =>
    F p.1)
  simp only [Function.Involutive.coe_toPerm] at h
  rw [h]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  norm_num

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

