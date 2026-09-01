import Mathlib

/-!
Low-degree function spaces on the Boolean cube.
-/

namespace RS

open Finset

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

section

variable {F : Type*} [Field F] {n : ℕ}

/-- The multilinear monomial function `x ↦ ∏_{i ∈ S} x i`. -/
def mono (F : Type*) [Field F] {n : ℕ} (S : Finset (Fin n)) : Cube n → F :=
  fun x => if ∀ i ∈ S, x i = true then 1 else 0

@[simp] lemma mono_empty : mono F (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mono]

lemma mono_mul (S T : Finset (Fin n)) :
    mono F S * mono F T = mono F (S ∪ T) := by
  funext x
  simp only [mono, Pi.mul_apply]
  by_cases hS : ∀ i ∈ S, x i = true <;> by_cases hT : ∀ i ∈ T, x i = true <;>
    simp [hS, hT] <;> aesop

end

section

variable (F : Type*) [Field F] (n : ℕ)

/-- Subsets of `Fin n` of size at most `D`. -/
def lowSets (n D : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => S.card ≤ D)

lemma mem_lowSets {n D : ℕ} {S : Finset (Fin n)} : S ∈ lowSets n D ↔ S.card ≤ D := by
  simp [lowSets]

/-- The space of functions on the cube computed by multilinear polynomials of degree `≤ D`. -/
def Deg (D : ℕ) : Submodule F (Cube n → F) :=
  Submodule.span F (((lowSets n D).image (mono F) : Finset (Cube n → F)) : Set (Cube n → F))

end

section

variable {F : Type*} [Field F] {n : ℕ}

lemma mono_mem_Deg {S : Finset (Fin n)} {D : ℕ} (h : S.card ≤ D) :
    mono F S ∈ Deg F n D := by
  apply Submodule.subset_span
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨S, mem_lowSets.2 h, rfl⟩

lemma Deg_mono {D D' : ℕ} (h : D ≤ D') : Deg F n D ≤ Deg F n D' := by
  rw [Deg, Submodule.span_le]
  rintro f hf
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hf
  obtain ⟨S, hS, rfl⟩ := hf
  exact mono_mem_Deg (le_trans (mem_lowSets.1 hS) h)

lemma mem_Deg_of_le {f : Cube n → F} {D D' : ℕ} (h : D ≤ D') (hf : f ∈ Deg F n D) :
    f ∈ Deg F n D' := Deg_mono h hf

lemma one_mem_Deg (D : ℕ) : (1 : Cube n → F) ∈ Deg F n D := by
  have := mono_mem_Deg (F := F) (S := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

lemma Deg_mul_Deg (a b : ℕ) : Deg F n a * Deg F n b ≤ Deg F n (a + b) := by
  rw [Deg, Deg, Submodule.span_mul_span, Submodule.span_le]
  rintro f hf
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.1 hf
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
  obtain ⟨S, hS, rfl⟩ := hu
  obtain ⟨T, hT, rfl⟩ := hv
  rw [mono_mul]
  refine mono_mem_Deg ?_
  calc (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le _ _
    _ ≤ a + b := Nat.add_le_add (mem_lowSets.1 hS) (mem_lowSets.1 hT)

lemma mul_mem_Deg {f g : Cube n → F} {a b : ℕ} (hf : f ∈ Deg F n a) (hg : g ∈ Deg F n b) :
    f * g ∈ Deg F n (a + b) :=
  Deg_mul_Deg a b (Submodule.mul_mem_mul hf hg)

lemma pow_mem_Deg {f : Cube n → F} {a : ℕ} (hf : f ∈ Deg F n a) (k : ℕ) :
    f ^ k ∈ Deg F n (k * a) := by
  induction k with
  | zero => simpa using one_mem_Deg 0
  | succ k ih =>
      have : f ^ (k + 1) = f ^ k * f := by ring
      rw [this]
      have := mul_mem_Deg ih hf
      refine mem_Deg_of_le ?_ this
      omega

lemma prod_mem_Deg {ι : Type*} (s : Finset ι) (g : ι → Cube n → F)
    (hg : ∀ i ∈ s, g i ∈ Deg F n 1) : (∏ i ∈ s, g i) ∈ Deg F n s.card := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : g a ∈ Deg F n 1 := hg a (Finset.mem_insert_self _ _)
      have h2 : (∏ i ∈ s, g i) ∈ Deg F n s.card :=
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have := mul_mem_Deg h1 h2
      exact mem_Deg_of_le (by omega) this

/-- The coordinate function is of degree one. -/
lemma coord_mem_Deg (i : Fin n) : (fun x : Cube n => if x i = true then (1:F) else 0) ∈ Deg F n 1 := by
  have := mono_mem_Deg (F := F) (S := ({i} : Finset (Fin n))) (D := 1) (by simp)
  convert this using 1
  funext x
  simp [mono]

lemma sub_mem_Deg {f g : Cube n → F} {a : ℕ} (hf : f ∈ Deg F n a) (hg : g ∈ Deg F n a) :
    f - g ∈ Deg F n a := Submodule.sub_mem _ hf hg

/-- Point indicators are in `Deg n`. -/
lemma indicator_mem_Deg (a : Cube n) :
    (fun x : Cube n => if x = a then (1:F) else 0) ∈ Deg F n n := by
  classical
  set g : Fin n → Cube n → F := fun i x =>
    if a i then (if x i = true then (1:F) else 0) else (1 - (if x i = true then (1:F) else 0)) with hgdef
  have hgi : ∀ i ∈ (Finset.univ : Finset (Fin n)), g i ∈ Deg F n 1 := by
    intro i _
    by_cases h : a i = true
    · simpa [hgdef, h] using coord_mem_Deg (F := F) i
    · have : g i = 1 - (fun x : Cube n => if x i = true then (1:F) else 0) := by
        funext x; simp [hgdef, h]
      rw [this]
      exact Submodule.sub_mem _ (one_mem_Deg 1) (coord_mem_Deg i)
  have hprod := prod_mem_Deg (F := F) (n := n) Finset.univ g hgi
  rw [Finset.card_univ, Fintype.card_fin] at hprod
  convert hprod using 1
  funext x
  by_cases hx : x = a
  · subst hx
    rw [if_pos rfl]
    symm
    apply Finset.prod_eq_one
    intro i _
    by_cases h : x i = true <;> simp [hgdef, h]
  · rw [if_neg hx]
    symm
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
      by_contra hcon
      push_neg at hcon
      exact hx (funext hcon)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hxi : x i <;> cases hai : a i <;> simp_all [hgdef]

lemma Deg_top : Deg F n n = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro f -
  have hf : f = ∑ a : Cube n, f a • (fun x : Cube n => if x = a then (1:F) else 0) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x f]
    simp
  rw [hf]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (indicator_mem_Deg a))

lemma finrank_Deg_le (D : ℕ) :
    Module.finrank F (Deg F n D) ≤ (lowSets n D).card := by
  refine le_trans (finrank_span_finset_le_card _) ?_
  exact Finset.card_image_le

instance Deg_finite (D : ℕ) : Module.Finite F (Deg F n D) := by
  rw [Deg]
  exact Module.Finite.span_of_finite _ (Set.toFinite _)

end

end RS

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

