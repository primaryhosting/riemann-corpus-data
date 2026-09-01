import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/
def PrefixFreeList (L : List (List Bool)) : Prop :=
  L.Pairwise (fun x y => ¬ x <+: y ∧ ¬ y <+: x)

/-- The Kraft sum `∑ 2^(-|s|)` of a list of codewords. -/
def kraftL (L : List (List Bool)) : ℝ := (L.map (fun s => (1/2:ℝ) ^ s.length)).sum

/-- The codewords starting with the bit `b`, with that leading bit removed. -/
def child (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | [] :: L => child b L
  | (c :: t) :: L => if c = b then t :: child b L else child b L

/-- Total length of all codewords, used as a termination measure. -/
def lenSum (L : List (List Bool)) : ℕ := (L.map List.length).sum

lemma kraftL_nonneg (L : List (List Bool)) : 0 ≤ kraftL L := by
  unfold kraftL
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨s, _, rfl⟩ := hx
  positivity

lemma mem_child (b : Bool) {L : List (List Bool)} {u : List Bool}
    (hu : u ∈ child b L) : (b :: u) ∈ L := by
  induction L with
  | nil => simp [child] at hu
  | cons s L ih =>
    match s with
    | [] =>
      simp only [child] at hu
      exact List.mem_cons_of_mem _ (ih hu)
    | c :: t =>
      simp only [child] at hu
      by_cases hcb : c = b
      · subst hcb
        simp only [if_pos rfl, List.mem_cons] at hu
        rcases hu with h | h
        · subst h; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h)
      · rw [if_neg hcb] at hu
        exact List.mem_cons_of_mem _ (ih hu)

lemma prefixFree_child (b : Bool) {L : List (List Bool)} (h : PrefixFreeList L) :
    PrefixFreeList (child b L) := by
  induction L with
  | nil => simp [child, PrefixFreeList]
  | cons s L ih =>
    rw [PrefixFreeList, List.pairwise_cons] at h
    obtain ⟨hhead, htail⟩ := h
    have ihp := ih htail
    match s with
    | [] => simpa only [child] using ihp
    | c :: t =>
      simp only [child]
      by_cases hcb : c = b
      · subst hcb
        rw [if_pos rfl, PrefixFreeList, List.pairwise_cons]
        refine ⟨?_, ihp⟩
        intro u hu
        have hmem := mem_child c hu
        have := hhead _ hmem
        constructor
        · intro hpre
          exact this.1 (List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
        · intro hpre
          exact this.2 (List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
      · rw [if_neg hcb]; exact ihp

lemma kraftL_split {L : List (List Bool)} (h : ∀ s ∈ L, s ≠ []) :
    kraftL L = (kraftL (child false L) + kraftL (child true L)) / 2 := by
  induction L with
  | nil => simp [kraftL, child]
  | cons s L ih =>
    have hL : ∀ t ∈ L, t ≠ [] := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have ihL := ih hL
    match s with
    | [] => exact absurd rfl (h [] (List.mem_cons_self ..))
    | c :: t =>
      cases c with
      | false =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (false = true))]
        simp only [kraftL, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        rw [ihL]; ring
      | true =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (true = false))]
        simp only [kraftL, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        rw [ihL]; ring

lemma lenSum_split {L : List (List Bool)} (h : ∀ s ∈ L, s ≠ []) :
    lenSum L = L.length + lenSum (child false L) + lenSum (child true L) := by
  induction L with
  | nil => simp [lenSum, child]
  | cons s L ih =>
    have hL : ∀ t ∈ L, t ≠ [] := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have ihL := ih hL
    match s with
    | [] => exact absurd rfl (h [] (List.mem_cons_self ..))
    | c :: t =>
      cases c with
      | false =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (false = true))]
        simp only [lenSum, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        omega
      | true =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (true = false))]
        simp only [lenSum, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        omega

/-- **Kraft's inequality**: a finite prefix-free binary code satisfies `∑ 2^(-|s|) ≤ 1`. -/
theorem kraftL_le_one : ∀ (L : List (List Bool)), PrefixFreeList L → kraftL L ≤ 1 := by
  intro L
  induction hn : lenSum L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  intro hpf
  subst hn
  by_cases hemp : [] ∈ L
  · -- the empty codeword forces `L = [[]]`
    have hsingle : L = [[]] := by
      rcases List.mem_iff_append.1 hemp with ⟨A, B, rfl⟩
      have hA : A = [] := by
        rcases A with _ | ⟨a, A'⟩
        · rfl
        · exfalso
          rw [PrefixFreeList, List.pairwise_append] at hpf
          have := hpf.2.2 a (List.mem_cons_self ..) [] (List.mem_cons_self ..)
          exact this.2 (List.nil_prefix)
      have hB : B = [] := by
        rcases B with _ | ⟨b, B'⟩
        · rfl
        · exfalso
          subst hA
          simp only [List.nil_append, PrefixFreeList, List.pairwise_cons] at hpf
          exact (hpf.1 b (List.mem_cons_self ..)).1 List.nil_prefix
      subst hA; subst hB; rfl
    rw [hsingle]; simp [kraftL]
  · have hne : ∀ s ∈ L, s ≠ [] := by
      intro s hs hcon; exact hemp (hcon ▸ hs)
    rcases L with _ | ⟨s, L'⟩
    · simp [kraftL]
    · set L := s :: L' with hLdef
      have hlen : 0 < L.length := by simp [hLdef]
      have hsplit := lenSum_split hne
      have h0 : lenSum (child false L) < lenSum L := by omega
      have h1 : lenSum (child true L) < lenSum L := by omega
      have k0 := ih _ h0 (child false L) rfl (prefixFree_child false hpf)
      have k1 := ih _ h1 (child true L) rfl (prefixFree_child true hpf)
      rw [kraftL_split hne]
      linarith

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

