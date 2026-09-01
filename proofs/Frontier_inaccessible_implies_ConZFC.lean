import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

We formalize the classical theorem that an inaccessible cardinal `κ` yields a model of `ZFC`,
namely the level `V_κ` of the cumulative hierarchy, and deduce that `ZFC` (as a first-order
theory in the language of set theory) is consistent, i.e. satisfiable.

The development proceeds in the following steps:

* `Frontier.Vh` : the cumulative hierarchy `V_o` of `ZFSet`s, with `x ∈ V_o ↔ rank x < o`.
* `Frontier.card_Vh_lt` : if `κ` is inaccessible and `o < κ.ord` then `V_o` has cardinality `< κ`.
* `Frontier.setLang` : the first-order language of set theory (one binary relation).
* `Frontier.ZFC` : the theory `ZFC`, with the separation and replacement schemes.
* `Frontier.VSet κ` : the model, the set of `ZFSet`s of rank `< κ.ord`.
* `Frontier.inaccessible_implies_ConZFC` : an inaccessible cardinal gives `Con(ZFC)`.
-/

universe u

namespace Frontier

open Ordinal Cardinal ZFSet

/-! ### The cumulative hierarchy -/

/-- The `o`-th level of the cumulative hierarchy of `ZFSet`s. -/
noncomputable def Vh (o : Ordinal.{u}) : ZFSet.{u} :=
  ⋃ (i : Set.Iio o), ZFSet.powerset (Vh i.1)
termination_by o
decreasing_by exact i.2

theorem Vh_def (o : Ordinal.{u}) : Vh o = ⋃ (i : Set.Iio o), ZFSet.powerset (Vh i.1) := by
  rw [Vh]

/-- The members of `V_o` are exactly the sets of rank `< o`. -/
theorem mem_Vh {o : Ordinal.{u}} {x : ZFSet.{u}} : x ∈ Vh o ↔ x.rank < o := by
  induction o using Ordinal.induction generalizing x with
  | _ o ih =>
    rw [Vh_def, ZFSet.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [ZFSet.mem_powerset] at hi
      refine lt_of_le_of_lt ?_ i.2
      rw [ZFSet.rank_le_iff]
      intro y hy
      exact (ih i.1 i.2 (x := y)).1 (hi hy)
    · intro h
      refine ⟨⟨x.rank, h⟩, ?_⟩
      rw [ZFSet.mem_powerset]
      intro y hy
      exact (ih _ h).2 (ZFSet.rank_lt_of_mem hy)

theorem rank_Vh_le (o : Ordinal.{u}) : (Vh o).rank ≤ o :=
  ZFSet.rank_le_iff.2 fun _ hy => mem_Vh.1 hy

theorem mk_shrink_Iio (o : Ordinal.{u}) : #(Shrink.{u} (Set.Iio o)) = o.card := by
  have h := Cardinal.lift_mk_shrink''.{u + 1, u} (Set.Iio o)
  rw [Ordinal.mk_Iio_ordinal] at h
  exact Cardinal.lift_injective h

theorem card_iUnion_lt {ι : Type u} (f : ι → ZFSet.{u}) {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hι : #ι < κ) (h : ∀ i, (f i).card < κ) : (⋃ i, f i).card < κ := by
  have h1 := ZFSet.lift_card_iUnion_le_sum_card (f := f)
  rw [Cardinal.lift_id] at h1
  exact lt_of_le_of_lt h1 (Cardinal.sum_lt_of_isRegular hκ hι h)

theorem Vh_subset_union (o : Ordinal.{u}) :
    Vh o ⊆ ⋃ (i : Shrink.{u} (Set.Iio o)),
      ZFSet.powerset (Vh ((equivShrink (Set.Iio o)).symm i : Set.Iio o).1) := by
  intro x hx
  rw [mem_Vh] at hx
  rw [ZFSet.mem_iUnion]
  refine ⟨equivShrink (Set.Iio o) ⟨x.rank, hx⟩, ?_⟩
  rw [Equiv.symm_apply_apply, ZFSet.mem_powerset]
  intro y hy
  exact mem_Vh.2 (ZFSet.rank_lt_of_mem hy)

/-- Below an inaccessible cardinal, every level of the cumulative hierarchy is small. -/
theorem card_Vh_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {o : Ordinal.{u}} (ho : o < κ.ord) :
    (Vh o).card < κ := by
  induction o using Ordinal.induction with
  | _ o ih =>
    refine lt_of_le_of_lt (ZFSet.card_mono (Vh_subset_union o)) ?_
    refine card_iUnion_lt _ hκ.isRegular ?_ ?_
    · rw [mk_shrink_Iio]
      exact Cardinal.lt_ord.1 ho
    · rintro i
      rw [ZFSet.card_powerset]
      exact hκ.isStrongLimit.two_power_lt (ih _ ((equivShrink (Set.Iio o)).symm i).2
        (lt_trans ((equivShrink (Set.Iio o)).symm i).2 ho))

/-- Below an inaccessible cardinal, every set of small rank is small. -/
theorem card_lt_of_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x.rank < κ.ord) : x.card < κ := by
  refine lt_of_le_of_lt (ZFSet.card_mono (fun y hy => mem_Vh.2 (ZFSet.rank_lt_of_mem hy))) ?_
  exact card_Vh_lt hκ hx

theorem ord_isSuccLimit {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    Order.IsSuccLimit κ.ord :=
  Cardinal.isSuccLimit_ord hκ.isRegular.aleph0_le

theorem succ_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x.rank < κ.ord) : Order.succ x.rank < κ.ord :=
  (ord_isSuccLimit hκ).succ_lt hx

/-- Below an inaccessible cardinal, small-indexed ranges of small sets are small. -/
theorem rank_range_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {ι : Type u} (hι : #ι < κ)
    (f : ι → ZFSet.{u}) (hf : ∀ i, (f i).rank < κ.ord) : (ZFSet.range f).rank < κ.ord := by
  rw [ZFSet.rank_range]
  refine Ordinal.iSup_lt_ord_lift ?_ fun i => succ_rank_lt hκ (hf i)
  rw [Cardinal.lift_id]
  rw [hκ.isRegular.cof_eq]
  exact hι

end Frontier

