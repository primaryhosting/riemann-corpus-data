import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Matrix Equiv Finset

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Counting form of the permanent (membership in `#P`).**
The permanent of a `0/1` matrix is the number of permutations `σ` all of whose entries
`A (σ i) i` equal `1`, i.e. the number of perfect matchings of the bipartite graph
described by `A`. -/
theorem permanent_eq_card_perms (A : Matrix V V ℕ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent = (univ.filter (fun σ : Perm V => ∀ i, A (σ i) i = 1)).card := by
  rw [Matrix.permanent, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, A (σ i) i = 1
  · simp [h]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg (by simpa using ⟨i, hi⟩)]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases h01 (σ i) i with h0 | h1
    · exact h0
    · exact absurd h1 hi

/-- The same count, phrased over *functions* `V → V` (bit strings of length `|V| log |V|`)
subject to the polynomial-time checkable predicate "is a bijection and all selected entries
are `1`". -/
theorem permanent_eq_card_bijections (A : Matrix V V ℕ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent =
      (univ.filter (fun f : V → V => Function.Bijective f ∧ ∀ i, A (f i) i = 1)).card := by
  rw [permanent_eq_card_perms A h01]
  refine Finset.card_bij (fun σ _ => ⇑σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact ⟨σ.bijective, hσ⟩
  · intro σ _ τ _ h
    exact Equiv.coe_fn_injective h
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨Equiv.ofBijective f hf.1, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    simpa using hf.2 i

end Counting

section Gadget

variable {n K : ℕ}

/-- Auxiliary ("midpoint") vertices of the gadget graph: for each pair `(i, j)` of original
vertices there are `K + 1` midpoints, of which the first `A i j` are *live*. -/
abbrev Mid (n K : ℕ) : Type := Fin n × Fin n × Fin (K + 1)

/-- Vertices of the gadget graph: the original ones together with the midpoints. -/
abbrev Vtx (n K : ℕ) : Type := Fin n ⊕ Mid n K

/-- The `0/1` gadget matrix associated with a nonnegative integer matrix `A`:
every entry `A i j` (a weight, given in unary) is replaced by `A i j` parallel length-two
paths through fresh midpoint vertices, each unused midpoint carrying a loop. -/
def gadget (A : Matrix (Fin n) (Fin n) ℕ) (K : ℕ) : Matrix (Vtx n K) (Vtx n K) ℕ :=
  fun r c =>
    match r, c with
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inl r, Sum.inr m => if r = m.1 ∧ (m.2.2 : ℕ) < A m.1 m.2.1 then 1 else 0
    | Sum.inr m, Sum.inl c => if m.2.1 = c ∧ (m.2.2 : ℕ) < A m.1 m.2.1 then 1 else 0
    | Sum.inr m, Sum.inr m' => if m = m' then 1 else 0

@[simp] theorem gadget_inl_inl (A : Matrix (Fin n) (Fin n) ℕ) (r c : Fin n) :
    gadget A K (Sum.inl r) (Sum.inl c) = 0 := rfl

@[simp] theorem gadget_inl_inr (A : Matrix (Fin n) (Fin n) ℕ) (r : Fin n) (m : Mid n K) :
    gadget A K (Sum.inl r) (Sum.inr m) =
      if r = m.1 ∧ (m.2.2 : ℕ) < A m.1 m.2.1 then 1 else 0 := rfl

@[simp] theorem gadget_inr_inl (A : Matrix (Fin n) (Fin n) ℕ) (m : Mid n K) (c : Fin n) :
    gadget A K (Sum.inr m) (Sum.inl c) =
      if m.2.1 = c ∧ (m.2.2 : ℕ) < A m.1 m.2.1 then 1 else 0 := rfl

@[simp] theorem gadget_inr_inr (A : Matrix (Fin n) (Fin n) ℕ) (m m' : Mid n K) :
    gadget A K (Sum.inr m) (Sum.inr m') = if m = m' then 1 else 0 := rfl

/-- The gadget matrix is a `0/1` matrix. -/
theorem gadget_zero_or_one (A : Matrix (Fin n) (Fin n) ℕ) (r c : Vtx n K) :
    gadget A K r c = 0 ∨ gadget A K r c = 1 := by
  cases r <;> cases c <;> simp only [gadget_inl_inl, gadget_inl_inr, gadget_inr_inl,
    gadget_inr_inr] <;> first | (left; rfl) | (split <;> simp)

/-- The permutation of the gadget graph associated with a permutation `σ` of the original
vertices together with a choice `t` of a parallel path for each vertex. -/
def gadgetPerm (σ : Perm (Fin n)) (t : Fin n → Fin (K + 1)) : Perm (Vtx n K) where
  toFun x := match x with
    | Sum.inl c => Sum.inr (σ c, c, t c)
    | Sum.inr m => if m = (σ m.2.1, m.2.1, t m.2.1) then Sum.inl m.1 else Sum.inr m
  invFun x := match x with
    | Sum.inl r => Sum.inr (r, σ.symm r, t (σ.symm r))
    | Sum.inr m => if m = (σ m.2.1, m.2.1, t m.2.1) then Sum.inl m.2.1 else Sum.inr m
  left_inv x := by
    cases x with
    | inl c => simp
    | inr m =>
      by_cases h : m = (σ m.2.1, m.2.1, t m.2.1)
      · simp only [h, if_pos rfl]
        conv_rhs => rw [h]
        simp
      · simp [h]
  right_inv x := by
    cases x with
    | inl r => simp
    | inr m =>
      by_cases h : m = (σ m.2.1, m.2.1, t m.2.1)
      · simp only [h, if_pos rfl]
        conv_rhs => rw [h]
        simp
      · simp [h]

@[simp] theorem gadgetPerm_inl (σ : Perm (Fin n)) (t : Fin n → Fin (K + 1)) (c : Fin n) :
    gadgetPerm σ t (Sum.inl c) = Sum.inr (σ c, c, t c) := rfl

@[simp] theorem gadgetPerm_inr (σ : Perm (Fin n)) (t : Fin n → Fin (K + 1)) (m : Mid n K) :
    gadgetPerm σ t (Sum.inr m) =
      if m = (σ m.2.1, m.2.1, t m.2.1) then Sum.inl m.1 else Sum.inr m := rfl

/-- The permutation of the original vertices read off from a permutation of the gadget graph. -/
def rowFun (τ : Perm (Vtx n K)) (c : Fin n) : Fin n :=
  match τ (Sum.inl c) with
  | Sum.inl r => r
  | Sum.inr m => m.1

/-- The choice of parallel path read off from a permutation of the gadget graph. -/
def colFun (τ : Perm (Vtx n K)) (c : Fin n) : Fin (K + 1) :=
  match τ (Sum.inl c) with
  | Sum.inl _ => 0
  | Sum.inr m => m.2.2

/-- A permutation of the gadget graph contributes to the permanent iff it satisfies this
predicate. -/
def Valid (A : Matrix (Fin n) (Fin n) ℕ) (τ : Perm (Vtx n K)) : Prop :=
  ∀ x, gadget A K (τ x) x = 1

instance (A : Matrix (Fin n) (Fin n) ℕ) (τ : Perm (Vtx n K)) : Decidable (Valid A τ) := by
  unfold Valid; infer_instance

/-- A valid permutation sends an original vertex to the midpoint prescribed by
`rowFun` and `colFun`, which is moreover live. -/
theorem valid_inl (A : Matrix (Fin n) (Fin n) ℕ) {τ : Perm (Vtx n K)} (hτ : Valid A τ)
    (c : Fin n) :
    τ (Sum.inl c) = Sum.inr (rowFun τ c, c, colFun τ c) ∧
      ((colFun τ c : ℕ) < A (rowFun τ c) c) := by
  have h := hτ (Sum.inl c)
  revert h
  rcases hc : τ (Sum.inl c) with r | m
  · simp
  · intro h
    simp only [gadget_inr_inl] at h
    have h' : m.2.1 = c ∧ (m.2.2 : ℕ) < A m.1 m.2.1 := by
      by_contra hcon
      rw [if_neg hcon] at h
      exact absurd h (by norm_num)
    have hrow : rowFun τ c = m.1 := by simp [rowFun, hc]
    have hcol : colFun τ c = m.2.2 := by simp [colFun, hc]
    refine ⟨?_, ?_⟩
    · rw [hc, hrow, hcol, h'.1]
    · rw [hrow, hcol]
      simpa [h'.1] using h'.2

theorem valid_inr (A : Matrix (Fin n) (Fin n) ℕ) {τ : Perm (Vtx n K)} (hτ : Valid A τ)
    (d : Fin n) : τ (Sum.inr (rowFun τ d, d, colFun τ d)) = Sum.inl (rowFun τ d) := by
  have hd := (valid_inl A hτ d).1
  have hne : τ (Sum.inr (rowFun τ d, d, colFun τ d)) ≠ Sum.inr (rowFun τ d, d, colFun τ d) := by
    intro hcon
    have := τ.injective (hd.trans hcon.symm)
    exact absurd this (by simp)
  have hval := hτ (Sum.inr (rowFun τ d, d, colFun τ d))
  revert hval hne
  rcases hval2 : τ (Sum.inr (rowFun τ d, d, colFun τ d)) with r | m
  · intro hval _
    simp only [gadget_inl_inr] at hval
    have : r = rowFun τ d ∧ _ := by
      by_contra hcon
      rw [if_neg hcon] at hval
      exact absurd hval (by norm_num)
    rw [this.1]
  · intro hval hne
    simp only [gadget_inr_inr] at hval
    have : m = (rowFun τ d, d, colFun τ d) := by
      by_contra hcon
      rw [if_neg hcon] at hval
      exact absurd hval (by norm_num)
    exact absurd (by rw [this]) hne

theorem rowFun_injective (A : Matrix (Fin n) (Fin n) ℕ) {τ : Perm (Vtx n K)} (hτ : Valid A τ) :
    Function.Injective (rowFun τ) := by
  intro c c' h
  have e1 := valid_inr A hτ c
  have e2 := valid_inr A hτ c'
  rw [h] at e1
  have hmid := τ.injective (e1.trans e2.symm)
  have : (rowFun τ c, c, colFun τ c) = (rowFun τ c', c', colFun τ c') := by
    simpa using hmid
  simpa using congrArg (fun p : Mid n K => p.2.1) this

end Gadget

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

