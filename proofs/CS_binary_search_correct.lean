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

namespace CS

/-- Binary search for `key` in the sub-range `[lo, hi)` of the array `a`.
Returns `some i` for an index `i` with `a[i]! = key`, and `none` if the key is
not found in that range. -/
def bsearchAux (a : Array Int) (key : Int) (lo hi : Nat) : Option Nat :=
  if _h : lo < hi then
    if a[(lo + hi) / 2]! = key then some ((lo + hi) / 2)
    else if a[(lo + hi) / 2]! < key then bsearchAux a key ((lo + hi) / 2 + 1) hi
    else bsearchAux a key lo ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search over the whole array. -/
def binarySearch (a : Array Int) (key : Int) : Option Nat :=
  bsearchAux a key 0 a.size

/-- `a` is sorted in non-decreasing order. -/
def Sorted (a : Array Int) : Prop :=
  ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]!

/-- Soundness of the auxiliary search: any returned index lies in the searched
range and points at the key. -/
theorem bsearchAux_sound (a : Array Int) (key : Int) :
    ∀ (lo hi i : Nat), bsearchAux a key lo hi = some i →
      lo ≤ i ∧ i < hi ∧ a[i]! = key := by
  intro lo hi
  induction lo, hi using bsearchAux.induct (a := a) (key := key) with
  | case1 lo hi h hmid =>
    intro i hi'
    rw [bsearchAux] at hi'
    simp only [dif_pos h, if_pos hmid, Option.some.injEq] at hi'
    subst hi'
    exact ⟨by omega, by omega, hmid⟩
  | case2 lo hi h hne hlt ih =>
    intro i hi'
    rw [bsearchAux] at hi'
    simp only [dif_pos h, if_neg hne, if_pos hlt] at hi'
    have := ih i hi'
    exact ⟨by omega, this.2.1, this.2.2⟩
  | case3 lo hi h hne hlt ih =>
    intro i hi'
    rw [bsearchAux] at hi'
    simp only [dif_pos h, if_neg hne, if_neg hlt] at hi'
    have := ih i hi'
    exact ⟨this.1, by omega, this.2.2⟩
  | case4 lo hi h =>
    intro i hi'
    rw [bsearchAux] at hi'
    simp only [dif_neg h, reduceCtorEq] at hi'

/-- Completeness of the auxiliary search on a sorted array: if the key occurs in
the searched range, the search returns some index. -/
theorem bsearchAux_complete (a : Array Int) (key : Int) (hs : Sorted a) :
    ∀ (lo hi : Nat), hi ≤ a.size →
      ∀ j : Nat, lo ≤ j → j < hi → a[j]! = key →
        ∃ i, bsearchAux a key lo hi = some i := by
  intro lo hi
  induction lo, hi using bsearchAux.induct (a := a) (key := key) with
  | case1 lo hi h hmid =>
    intro _ _ _ _ _
    refine ⟨(lo + hi) / 2, ?_⟩
    rw [bsearchAux]
    simp only [dif_pos h, if_pos hmid]
  | case2 lo hi h hne hlt ih =>
    intro hhi j hlj hjh hj
    rw [bsearchAux]
    simp only [dif_pos h, if_neg hne, if_pos hlt]
    refine ih hhi j ?_ hjh hj
    by_contra hcon
    have hjm : j ≤ (lo + hi) / 2 := by omega
    have := hs j ((lo + hi) / 2) hjm (by omega)
    rw [hj] at this
    omega
  | case3 lo hi h hne hlt ih =>
    intro hhi j hlj hjh hj
    rw [bsearchAux]
    simp only [dif_pos h, if_neg hne, if_neg hlt]
    refine ih (by omega) j hlj ?_ hj
    by_contra hcon
    have hmj : (lo + hi) / 2 ≤ j := by omega
    have := hs ((lo + hi) / 2) j hmj (by omega)
    rw [hj] at this
    omega
  | case4 lo hi h =>
    intro _ j hlj hjh _
    omega

/-- **Binary search is correct**: on a sorted array, binary search returns an
index if and only if the key is present in the array.  Moreover (see
`CS.binary_search_index`) any returned index really points at the key. -/
theorem binary_search_correct (a : Array Int) (key : Int) (hs : Sorted a) :
    (∃ i, binarySearch a key = some i) ↔ (∃ i, i < a.size ∧ a[i]! = key) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨-, h2, h3⟩ := bsearchAux_sound a key 0 a.size i hi
    exact ⟨i, h2, h3⟩
  · rintro ⟨j, hj, hjk⟩
    exact bsearchAux_complete a key hs 0 a.size le_rfl j (Nat.zero_le _) hj hjk

/-- Any index returned by binary search is a valid index of the array holding
the key. -/
theorem binary_search_index (a : Array Int) (key : Int) (i : Nat)
    (h : binarySearch a key = some i) : i < a.size ∧ a[i]! = key := by
  obtain ⟨-, h2, h3⟩ := bsearchAux_sound a key 0 a.size i h
  exact ⟨h2, h3⟩

end CS

