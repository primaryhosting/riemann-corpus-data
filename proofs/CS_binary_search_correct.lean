import Mathlib

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
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

variable {α : Type*} [LinearOrder α]

/-- Binary search for `key` in the index range `[lo, hi)` of the "array" `f`. -/
def bsearchAux (f : ℕ → α) (key : α) (lo hi : ℕ) : Option ℕ :=
  if lo < hi then
    if f ((lo + hi) / 2) = key then some ((lo + hi) / 2)
    else if f ((lo + hi) / 2) < key then bsearchAux f key ((lo + hi) / 2 + 1) hi
    else bsearchAux f key lo ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Soundness: if binary search returns an index, it is in range and holds the key. -/
theorem bsearchAux_sound (f : ℕ → α) (key : α) (lo hi i : ℕ)
    (h : bsearchAux f key lo hi = some i) :
    lo ≤ i ∧ i < hi ∧ f i = key := by
  induction lo, hi using bsearchAux.induct (f := f) (key := key) with
  | case1 lo hi hlt hmid =>
      rw [bsearchAux, if_pos hlt, if_pos hmid] at h
      have hi' : i = (lo + hi) / 2 := by simpa using h.symm
      subst hi'
      exact ⟨by omega, by omega, hmid⟩
  | case2 lo hi hlt hne hmlt ih =>
      rw [bsearchAux, if_pos hlt, if_neg hne, if_pos hmlt] at h
      have := ih h
      exact ⟨by omega, this.2.1, this.2.2⟩
  | case3 lo hi hlt hne hmlt ih =>
      rw [bsearchAux, if_pos hlt, if_neg hne, if_neg hmlt] at h
      have := ih h
      exact ⟨this.1, by omega, this.2.2⟩
  | case4 lo hi hlt =>
      rw [bsearchAux, if_neg hlt] at h
      exact absurd h (by simp)

/-- Completeness: on a range where `f` is monotone, if the key occurs then binary search
finds some index. -/
theorem bsearchAux_complete (f : ℕ → α) (key : α) (lo hi : ℕ)
    (hmono : ∀ i j, lo ≤ i → i ≤ j → j < hi → f i ≤ f j)
    (i : ℕ) (hlo : lo ≤ i) (hhi : i < hi) (hfi : f i = key) :
    (bsearchAux f key lo hi).isSome := by
  induction lo, hi using bsearchAux.induct (f := f) (key := key) generalizing i with
  | case1 lo hi hlt hmid =>
      rw [bsearchAux, if_pos hlt, if_pos hmid]
      rfl
  | case2 lo hi hlt hne hmlt ih =>
      rw [bsearchAux, if_pos hlt, if_neg hne, if_pos hmlt]
      have himid : (lo + hi) / 2 < i := by
        by_contra hcon
        push_neg at hcon
        have hle : f i ≤ f ((lo + hi) / 2) := hmono i ((lo + hi) / 2) hlo hcon (by omega)
        rw [hfi] at hle
        exact absurd hmlt (not_lt.mpr hle)
      exact ih (fun a b ha hab hb => hmono a b (by omega) hab hb) i (by omega) hhi hfi
  | case3 lo hi hlt hne hmlt ih =>
      rw [bsearchAux, if_pos hlt, if_neg hne, if_neg hmlt]
      have himid : i < (lo + hi) / 2 := by
        by_contra hcon
        push_neg at hcon
        have hle : f ((lo + hi) / 2) ≤ f i := hmono ((lo + hi) / 2) i (by omega) hcon hhi
        rw [hfi] at hle
        have hkm : key < f ((lo + hi) / 2) := lt_of_le_of_ne (not_lt.mp hmlt) (Ne.symm hne)
        exact absurd hle (not_le.mpr hkm)
      exact ih (fun a b ha hab hb => hmono a b ha hab (by omega)) i hlo himid hfi
  | case4 lo hi hlt =>
      omega

/-- Binary search on an array, using the standard midpoint recursion. -/
def bsearch [Inhabited α] (a : Array α) (key : α) : Option ℕ :=
  bsearchAux (fun i => a[i]!) key 0 a.size

/--
**Binary search is correct.**

If `a` is a sorted array (indices in increasing order have non-decreasing entries), then
`CS.bsearch a key` returns an index if and only if `key` occurs in `a`; moreover whenever it
returns an index `i`, that index is in range and `a[i] = key`.
-/
theorem binary_search_correct [Inhabited α] (a : Array α) (key : α)
    (hsorted : ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    ((bsearch a key).isSome ↔ ∃ i, ∃ h : i < a.size, a[i] = key) ∧
      ∀ i, bsearch a key = some i → ∃ h : i < a.size, a[i] = key := by
  have hsound : ∀ i, bsearch a key = some i → 0 ≤ i ∧ i < a.size ∧ a[i]! = key := by
    intro i h
    exact bsearchAux_sound (fun i => a[i]!) key 0 a.size i h
  constructor
  · constructor
    · intro h
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨-, hlt, heq⟩ := hsound i hi
      exact ⟨i, hlt, by rwa [getElem!_pos a i hlt] at heq⟩
    · rintro ⟨i, hlt, heq⟩
      refine bsearchAux_complete (fun i => a[i]!) key 0 a.size
        (fun p q _ hpq hq => hsorted p q hpq hq) i (Nat.zero_le _) hlt ?_
      simpa [getElem!_pos a i hlt] using heq
  · intro i h
    obtain ⟨-, hlt, heq⟩ := hsound i h
    exact ⟨hlt, by rwa [getElem!_pos a i hlt] at heq⟩

end CS

#print axioms CS.binary_search_correct

