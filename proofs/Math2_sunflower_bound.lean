/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- A family of sets `S` is a *sunflower* if all pairwise intersections of distinct
members are equal to a common `core`. -/
def IsSunflower {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Prop :=
  ∃ core : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = core

/-!
### Statement and status

`Math2.sunflower_bound` below is the **Erdős–Rado sunflower lemma**: every family `F` of
`w`-element sets with `w ! * (r - 1) ^ w < F.card` contains a sunflower with `r` petals.

The Alweiss–Lovett–Wu–Zhang improvement asserts the stronger bound

```
∃ C : ℝ, ∀ w r F, (∀ A ∈ F, A.card = w) → (C * r * Real.log w) ^ w < F.card →
  ∃ S ⊆ F, S.card = r ∧ IsSunflower S
```

which is *not* established in this file; only the classical bound above is proved here.
-/

/-- **Erdős–Rado sunflower lemma.**  If every member of the family `F` of finite sets has
exactly `w` elements and `F` has more than `w ! * (r - 1) ^ w` members, then `F` contains a
sunflower with `r` petals, i.e. `r` distinct members whose pairwise intersections all equal a
common core. -/
theorem sunflower_bound {α : Type*} [DecidableEq α] :
    ∀ (w r : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card = w) →
      w.factorial * (r - 1) ^ w < F.card → ∃ S ⊆ F, S.card = r ∧ IsSunflower S := by
  intro w
  induction w with
  | zero =>
      intro r F hw hcard
      exfalso
      have hsub : F ⊆ {∅} := by
        intro A hA
        have := hw A hA
        simp [Finset.card_eq_zero.mp this]
      have := Finset.card_le_card hsub
      simp at this
      simp at hcard
      omega
  | succ w ih =>
      intro r F hw hcard
      classical
      rcases Nat.lt_or_ge r 2 with hr | hr
      · interval_cases r
        · exact ⟨∅, Finset.empty_subset _, Finset.card_empty, ⟨∅, by simp⟩⟩
        · have hpos : 0 < F.card := Nat.lt_of_le_of_lt (Nat.zero_le _) hcard
          obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
          refine ⟨{A}, by simpa using hA, Finset.card_singleton _, ⟨∅, ?_⟩⟩
          intro X hX Y hY hne
          simp only [Finset.mem_singleton] at hX hY
          exact absurd (hX.trans hY.symm) hne
      · -- the interesting case: `2 ≤ r`
        set P := F.powerset.filter (fun T => ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) with hP
        have hPne : P.Nonempty := ⟨∅, by simp [hP]⟩
        obtain ⟨D, hD, hDmax⟩ := Finset.exists_max_image P Finset.card hPne
        rw [hP, Finset.mem_filter, Finset.mem_powerset] at hD
        obtain ⟨hDF, hDdisj⟩ := hD
        rcases Nat.lt_or_ge D.card r with hDr | hDr
        · -- few pairwise disjoint sets: pass to a link and use induction
          set Y := D.biUnion id with hY
          have hYcard : Y.card ≤ (r - 1) * (w + 1) := by
            have h1 : Y.card ≤ ∑ A ∈ D, (id A).card := Finset.card_biUnion_le
            have h2 : ∑ A ∈ D, (id A).card ≤ D.card * (w + 1) := by
              have := Finset.sum_le_card_nsmul D (fun A => (id A).card) (w + 1)
                (fun A hA => le_of_eq (hw A (hDF hA)))
              simpa [smul_eq_mul] using this
            have h3 : D.card * (w + 1) ≤ (r - 1) * (w + 1) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          have hmeet : ∀ A ∈ F, ∃ y ∈ Y, y ∈ A := by
            intro A hA
            by_contra hcon
            push_neg at hcon
            have hAdisj : ∀ B ∈ D, Disjoint A B := by
              intro B hB
              rw [Finset.disjoint_left]
              intro a haA haB
              exact hcon a (by rw [hY]; exact Finset.mem_biUnion.mpr ⟨B, hB, haB⟩) haA
            have hAnotD : A ∉ D := by
              intro hAD
              have hcardA : A.card = w + 1 := hw A hA
              obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
              exact hcon a (by rw [hY]; exact Finset.mem_biUnion.mpr ⟨A, hAD, ha⟩) ha
            have hins : insert A D ∈ P := by
              rw [hP, Finset.mem_filter, Finset.mem_powerset]
              constructor
              · intro B hB
                rcases Finset.mem_insert.mp hB with h | h
                · exact h ▸ hA
                · exact hDF h
              · intro X hX Z hZ hne
                rcases Finset.mem_insert.mp hX with hx | hx <;>
                  rcases Finset.mem_insert.mp hZ with hz | hz
                · exact absurd (hx.trans hz.symm) hne
                · exact hx ▸ hAdisj Z hz
                · exact hz ▸ (hAdisj X hx).symm
                · exact hDdisj X hx Z hz hne
            have hcards := hDmax _ hins
            rw [Finset.card_insert_of_notMem hAnotD] at hcards
            omega
          have hFsub : F ⊆ Y.biUnion (fun y => F.filter (fun A => y ∈ A)) := by
            intro A hA
            obtain ⟨y, hyY, hyA⟩ := hmeet A hA
            exact Finset.mem_biUnion.mpr ⟨y, hyY, Finset.mem_filter.mpr ⟨hA, hyA⟩⟩
          have hsum : F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card :=
            (Finset.card_le_card hFsub).trans Finset.card_biUnion_le
          have hex : ∃ y ∈ Y, w.factorial * (r - 1) ^ w <
              (F.filter (fun A => y ∈ A)).card := by
            by_contra hcon
            push_neg at hcon
            have h1 : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card
                ≤ Y.card * (w.factorial * (r - 1) ^ w) := by
              simpa [smul_eq_mul] using
                Finset.sum_le_card_nsmul Y (fun y => (F.filter (fun A => y ∈ A)).card)
                  (w.factorial * (r - 1) ^ w) hcon
            have h2 : Y.card * (w.factorial * (r - 1) ^ w)
                ≤ ((r - 1) * (w + 1)) * (w.factorial * (r - 1) ^ w) :=
              Nat.mul_le_mul_right _ hYcard
            have h3 : ((r - 1) * (w + 1)) * (w.factorial * (r - 1) ^ w)
                = (w + 1).factorial * (r - 1) ^ (w + 1) := by
              rw [Nat.factorial_succ, pow_succ]; ring
            exact absurd hcard (not_lt.mpr (hsum.trans (h1.trans (h2.trans_eq h3))))
          obtain ⟨y, hyY, hy⟩ := hex
          set G := (F.filter (fun A => y ∈ A)).image (fun A => A.erase y) with hG
          have hGmem : ∀ A ∈ G, y ∉ A ∧ insert y A ∈ F := by
            intro A hA
            rw [hG] at hA
            obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
            rw [Finset.mem_filter] at hB
            refine ⟨Finset.notMem_erase _ _, ?_⟩
            rw [Finset.insert_erase hB.2]
            exact hB.1
          have hGcard : G.card = (F.filter (fun A => y ∈ A)).card := by
            rw [hG]
            refine Finset.card_image_of_injOn ?_
            intro A hA B hB hAB
            simp only [Finset.mem_coe, Finset.mem_filter] at hA hB
            have h := congrArg (insert y) hAB
            rwa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] at h
          have hGw : ∀ A ∈ G, A.card = w := by
            intro A hA
            rw [hG] at hA
            obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
            rw [Finset.mem_filter] at hB
            rw [Finset.card_erase_of_mem hB.2, hw B hB.1]
            omega
          obtain ⟨S', hS'G, hS'card, c, hS'sun⟩ := ih r G hGw (by rw [hGcard]; exact hy)
          have hinj : Set.InjOn (insert y) (S' : Set (Finset α)) := by
            intro A hA B hB hAB
            have hyA : y ∉ A := (hGmem A (hS'G hA)).1
            have hyB : y ∉ B := (hGmem B (hS'G hB)).1
            have h := congrArg (fun s => Finset.erase s y) hAB
            simpa [Finset.erase_insert hyA, Finset.erase_insert hyB] using h
          refine ⟨S'.image (insert y), ?_, ?_, ⟨insert y c, ?_⟩⟩
          · intro A hA
            obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
            exact (hGmem A' (hS'G hA')).2
          · rw [Finset.card_image_of_injOn hinj, hS'card]
          · intro A hA B hB hne
            obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
            obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
            have hne' : A' ≠ B' := fun h => hne (by rw [h])
            have hinter : (insert y A') ∩ (insert y B') = insert y (A' ∩ B') := by
              ext z; simp only [Finset.mem_inter, Finset.mem_insert]; tauto
            rw [hinter, hS'sun A' hA' B' hB' hne']
        · -- many pairwise disjoint sets: they form a sunflower with empty core
          obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hDr
          exact ⟨S, hSD.trans hDF, hScard, ⟨∅, fun A hA B hB hne =>
            Finset.disjoint_iff_inter_eq_empty.mp (hDdisj A (hSD hA) B (hSD hB) hne)⟩⟩

end Math2

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

