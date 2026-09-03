import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finite set of all binary strings (lists of booleans) of length `n`. -/
def binLists (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)

lemma mem_binLists {n : ℕ} {l : List Bool} : l ∈ binLists n ↔ l.length = n := by
  constructor
  · rintro hl
    simp only [binLists, Finset.mem_image] at hl
    obtain ⟨f, -, rfl⟩ := hl
    simp
  · intro hl
    subst hl
    simp only [binLists, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => l.get i, by simp⟩

lemma card_binLists (n : ℕ) : (binLists n).card = 2 ^ n := by
  rw [binLists, Finset.card_image_of_injective _ (List.ofFn_injective)]
  simp

/-- The set of length-`L` extensions of a codeword `c`. -/
def exts (L : ℕ) (c : List Bool) : Finset (List Bool) :=
  (binLists (L - c.length)).image (fun t => c ++ t)

lemma card_exts (L : ℕ) (c : List Bool) : (exts L c).card = 2 ^ (L - c.length) := by
  rw [exts, Finset.card_image_of_injective _ (fun x y hxy => List.append_cancel_left hxy),
    card_binLists]

lemma exts_subset {L : ℕ} {c : List Bool} (hc : c.length ≤ L) :
    exts L c ⊆ binLists L := by
  intro l hl
  simp only [exts, Finset.mem_image] at hl
  obtain ⟨t, ht, rfl⟩ := hl
  rw [mem_binLists] at ht ⊢
  simp [ht]
  omega

lemma prefix_of_mem_exts {L : ℕ} {c l : List Bool} (hl : l ∈ exts L c) : c <+: l := by
  simp only [exts, Finset.mem_image] at hl
  obtain ⟨t, -, rfl⟩ := hl
  exact ⟨t, rfl⟩

/-- **Kraft's inequality**: for a prefix-free set of binary codewords `S`
(no codeword is a proper prefix of another), we have `∑ 2^(-ℓ) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ c ∈ S, ∀ d ∈ S, c <+: d → c = d) :
    ∑ c ∈ S, (1 / 2 : ℝ) ^ c.length ≤ 1 := by
  classical
  set L : ℕ := ∑ c ∈ S, c.length with hL
  have hlen : ∀ c ∈ S, c.length ≤ L := by
    intro c hc
    exact Finset.single_le_sum (f := fun c : List Bool => c.length)
      (fun i _ => Nat.zero_le _) hc
  -- the extension sets are pairwise disjoint
  have hdisj : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → Disjoint (exts L c) (exts L d) := by
    intro c hc d hd hcd
    rw [Finset.disjoint_left]
    intro l hlc hld
    have h1 : c <+: l := prefix_of_mem_exts hlc
    have h2 : d <+: l := prefix_of_mem_exts hld
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hcd (hpf c hc d hd h)
    · exact hcd (hpf d hd c hc h).symm
  -- counting
  have hcard : ∑ c ∈ S, 2 ^ (L - c.length) ≤ 2 ^ L := by
    have hsub : S.biUnion (exts L) ⊆ binLists L := by
      intro l hl
      simp only [Finset.mem_biUnion] at hl
      obtain ⟨c, hc, hlc⟩ := hl
      exact exts_subset (hlen c hc) hlc
    have := Finset.card_le_card hsub
    rw [Finset.card_biUnion (fun c hc d hd hcd => hdisj c hc d hd hcd), card_binLists] at this
    simpa [card_exts] using this
  -- convert to the real inequality
  have key : ∑ c ∈ S, (2 : ℝ) ^ (L - c.length) ≤ 2 ^ L := by
    exact_mod_cast hcard
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  refine le_of_mul_le_mul_right ?_ h2L
  rw [one_mul, Finset.sum_mul]
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl ?_
  intro c hc
  have hcl := hlen c hc
  rw [one_div, inv_pow, inv_mul_eq_div, div_eq_mul_inv,
    ← pow_sub₀ (2 : ℝ) (by norm_num) hcl]

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

