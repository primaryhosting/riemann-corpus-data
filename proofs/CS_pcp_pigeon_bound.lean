/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace CS

/-- The finite set of all binary words (lists of booleans) of length `n`. -/
def wordsOfLen (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)

@[simp] lemma mem_wordsOfLen {n : ℕ} {v : List Bool} : v ∈ wordsOfLen n ↔ v.length = n := by
  constructor
  · intro h
    simp only [wordsOfLen, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨f, rfl⟩ := h
    simp
  · intro h
    subst h
    simp only [wordsOfLen, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => v[i], by simp⟩

lemma card_wordsOfLen (n : ℕ) : (wordsOfLen n).card = 2 ^ n := by
  rw [wordsOfLen, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- The words of length `n` extending a fixed word `w` are exactly the words `w ++ u`
with `u` of length `n - w.length`. -/
lemma extensions_eq {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    (wordsOfLen n).filter (fun v => w <+: v)
      = (wordsOfLen (n - w.length)).image (fun u => w ++ u) := by
  ext v
  simp only [Finset.mem_filter, mem_wordsOfLen, Finset.mem_image]
  constructor
  · rintro ⟨hlen, t, rfl⟩
    exact ⟨t, by simp at hlen ⊢; omega, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨by simp [hu]; omega, ⟨u, rfl⟩⟩

lemma card_extensions {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    ((wordsOfLen n).filter (fun v => w <+: v)).card = 2 ^ (n - w.length) := by
  rw [extensions_eq hw,
    Finset.card_image_of_injective _ (List.append_right_injective w), card_wordsOfLen]

/-- Kraft's inequality in integer form: for a prefix-free set `S` of binary words all of
length at most `n`, we have `∑ 2 ^ (n - ℓ) ≤ 2 ^ n`. -/
lemma kraft_nat (S : Finset (List Bool)) (n : ℕ) (hn : ∀ w ∈ S, w.length ≤ n)
    (hpf : ∀ w ∈ S, ∀ v ∈ S, w <+: v → w = v) :
    ∑ w ∈ S, 2 ^ (n - w.length) ≤ 2 ^ n := by
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint
      (fun w => (wordsOfLen n).filter (fun v => w <+: v)) := by
    intro a ha b hb hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro v ⟨-, hav⟩ ⟨-, hbv⟩
    rcases List.prefix_or_prefix_of_prefix hav hbv with h | h
    · exact hab (hpf a ha b hb h)
    · exact hab (hpf b hb a ha h).symm
  calc ∑ w ∈ S, 2 ^ (n - w.length)
      = ∑ w ∈ S, ((wordsOfLen n).filter (fun v => w <+: v)).card := by
        refine Finset.sum_congr rfl fun w hw => (card_extensions (hn w hw)).symm
    _ = (S.biUnion (fun w => (wordsOfLen n).filter (fun v => w <+: v))).card :=
        (Finset.card_biUnion (fun a ha b hb hab => hdisj ha hb hab)).symm
    _ ≤ (wordsOfLen n).card :=
        Finset.card_le_card (Finset.biUnion_subset.2 fun w _ => Finset.filter_subset _ _)
    _ = 2 ^ n := card_wordsOfLen n

/-- **Kraft's inequality**: any prefix-free binary code satisfies `∑ 2 ^ (-ℓᵢ) ≤ 1`.

Here a code is a finite set `S` of binary words (lists of booleans), and prefix-freeness
says that no word of `S` is a proper prefix of another word of `S`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ w ∈ S, ∀ v ∈ S, w <+: v → w = v) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  obtain ⟨n, hn⟩ : ∃ n, ∀ w ∈ S, w.length ≤ n :=
    ⟨(S.image List.length).sup id, fun w hw =>
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hw)⟩
  have key := kraft_nat S n hn hpf
  have hcast : ((∑ w ∈ S, 2 ^ (n - w.length) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at hcast
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have heq : ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length = (∑ w ∈ S, (2 : ℝ) ^ (n - w.length)) / 2 ^ n := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hle : w.length ≤ n := hn w hw
    rw [div_pow, one_pow, eq_div_iff (ne_of_gt h2), div_mul_eq_mul_div, one_mul,
      eq_comm, eq_div_iff (by positivity : ((2 : ℝ) ^ w.length) ≠ 0), ← pow_add]
    congr 1
    omega
  rw [heq, div_le_one h2]
  exact hcast

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

