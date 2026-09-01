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

import Mathlib

/-!
# Equidecomposability and paradoxical decompositions

This file develops the basic abstract theory used in the proof of the Banach–Tarski paradox.

Given a group `G` acting on a type `X`, two sets `A B : Set X` are *equidecomposable*
(`BT.Equidec G A B`) if there is a bijection `f : A → B` which is piecewise given by finitely many
elements of `G`.  A set `E` is *paradoxical* (`BT.Paradoxical G E`) if it contains two disjoint
subsets, each of which is equidecomposable with `E` itself.
-/

open Function Set Pointwise

namespace BT

variable {X : Type*} {G : Type*} [Group G] [MulAction G X]

/-- `A` and `B` are `G`-equidecomposable: there is a bijection from `A` to `B` which is
piecewise given by finitely many elements of `G`. -/
def Equidec (G : Type*) [Group G] [MulAction G X] (A B : Set X) : Prop :=
  ∃ (f : X → X) (S : Finset G), (∀ a ∈ A, ∃ g ∈ S, f a = g • a) ∧ Set.BijOn f A B

/-- `E` is `G`-paradoxical: it contains two disjoint subsets each equidecomposable with `E`. -/
def Paradoxical (G : Type*) [Group G] [MulAction G X] (E : Set X) : Prop :=
  ∃ A B : Set X, A ⊆ E ∧ B ⊆ E ∧ Disjoint A B ∧ Equidec G A E ∧ Equidec G B E

namespace Equidec

variable {A B C A₁ A₂ B₁ B₂ : Set X}

theorem refl (A : Set X) : Equidec G A A :=
  ⟨id, {1}, fun a _ => ⟨1, Finset.mem_singleton_self _, by simp⟩, Set.bijOn_id A⟩

theorem symm [Nonempty X] (h : Equidec G A B) : Equidec G B A := by
  classical
  obtain ⟨f, S, hS, hbij⟩ := h
  refine ⟨invFunOn f A, S⁻¹, ?_, hbij.symm (hbij.invOn_invFunOn)⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hbij.surjOn hb
  obtain ⟨g, hgS, hg⟩ := hS a ha
  refine ⟨g⁻¹, Finset.inv_mem_inv hgS, ?_⟩
  rw [hbij.invOn_invFunOn.1 ha, hg, inv_smul_smul]

theorem trans (h₁ : Equidec G A B) (h₂ : Equidec G B C) : Equidec G A C := by
  classical
  obtain ⟨f, S, hS, hbij⟩ := h₁
  obtain ⟨f', S', hS', hbij'⟩ := h₂
  refine ⟨f' ∘ f, S' * S, ?_, hbij'.comp hbij⟩
  intro a ha
  obtain ⟨g, hgS, hg⟩ := hS a ha
  obtain ⟨g', hgS', hg'⟩ := hS' (f a) (hbij.mapsTo ha)
  refine ⟨g' * g, Finset.mul_mem_mul hgS' hgS, ?_⟩
  rw [Function.comp_apply, hg', hg, mul_smul]

/-- The restriction of an equidecomposition to a subset. -/
theorem restrict (h : Equidec G A B) (hA₁ : A₁ ⊆ A) : ∃ B₁ ⊆ B, Equidec G A₁ B₁ := by
  obtain ⟨f, S, hS, hbij⟩ := h
  refine ⟨f '' A₁, (Set.image_mono hA₁).trans hbij.mapsTo.image_subset,
    ⟨f, S, fun a ha => hS a (hA₁ ha), (hbij.injOn.mono hA₁).bijOn_image⟩⟩

theorem union (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂)
    (h₁ : Equidec G A₁ B₁) (h₂ : Equidec G A₂ B₂) : Equidec G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f, S, hS, hbij⟩ := h₁
  obtain ⟨f', S', hS', hbij'⟩ := h₂
  have hd : ∀ x ∈ A₂, x ∉ A₁ := fun x hx h => (hA.le_bot ⟨h, hx⟩).elim
  have hdB : ∀ x ∈ B₂, x ∉ B₁ := fun x hx h => (hB.le_bot ⟨h, hx⟩).elim
  refine ⟨fun x => if x ∈ A₁ then f x else f' x, S ∪ S', ?_, ?_, ?_, ?_⟩
  · rintro a (ha | ha)
    · obtain ⟨g, hg, hga⟩ := hS a ha
      exact ⟨g, Finset.mem_union_left _ hg, by simpa [ha] using hga⟩
    · obtain ⟨g, hg, hga⟩ := hS' a ha
      exact ⟨g, Finset.mem_union_right _ hg, by simpa [hd a ha] using hga⟩
  · rintro a (ha | ha)
    · exact Or.inl (by simpa [ha] using hbij.mapsTo ha)
    · exact Or.inr (by simpa [hd a ha] using hbij'.mapsTo ha)
  · rintro a ha b hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · simp only [ha, hb, if_true] at hab
      exact hbij.injOn ha hb hab
    · simp only [ha, hd b hb, if_true, if_false] at hab
      exact absurd (hab ▸ hbij.mapsTo ha) (hdB _ (hbij'.mapsTo hb))
    · simp only [hb, hd a ha, if_true, if_false] at hab
      exact absurd (hab ▸ hbij'.mapsTo ha) (fun h => hdB _ h (hbij.mapsTo hb))
    · simp only [hd a ha, hd b hb, if_false] at hab
      exact hbij'.injOn ha hb hab
  · rintro b (hb | hb)
    · obtain ⟨a, ha, rfl⟩ := hbij.surjOn hb
      exact ⟨a, Or.inl ha, by simp [ha]⟩
    · obtain ⟨a, ha, rfl⟩ := hbij'.surjOn hb
      exact ⟨a, Or.inr ha, by simp [hd a ha]⟩

/-- Transfer along a group homomorphism compatible with the actions. -/
theorem of_hom {H : Type*} [Group H] [MulAction H X] (φ : G →* H)
    (hφ : ∀ (g : G) (x : X), (φ g) • x = g • x) (h : Equidec G A B) : Equidec H A B := by
  classical
  obtain ⟨f, S, hS, hbij⟩ := h
  refine ⟨f, S.image φ, ?_, hbij⟩
  intro a ha
  obtain ⟨g, hg, hga⟩ := hS a ha
  exact ⟨φ g, Finset.mem_image_of_mem _ hg, by rw [hga, hφ]⟩

end Equidec

theorem Paradoxical.congr [Nonempty X] {E F : Set X} (h : Paradoxical G E) (hEF : Equidec G E F) :
    Paradoxical G F := by
  obtain ⟨A, B, hA, hB, hAB, hAE, hBE⟩ := h
  obtain ⟨f, S, hS, hbij⟩ := hEF
  have h1 : Equidec G A (f '' A) :=
    ⟨f, S, fun a ha => hS a (hA ha), (hbij.injOn.mono hA).bijOn_image⟩
  have h2 : Equidec G B (f '' B) :=
    ⟨f, S, fun a ha => hS a (hB ha), (hbij.injOn.mono hB).bijOn_image⟩
  refine ⟨f '' A, f '' B, (Set.image_mono hA).trans hbij.mapsTo.image_subset,
    (Set.image_mono hB).trans hbij.mapsTo.image_subset, ?_, ?_, ?_⟩
  · rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have hba : b = a := hbij.injOn (hB hb) (hA ha) hab
    subst hba
    exact (hAB.le_bot ⟨hb, ha⟩).elim
  · exact (h1.symm.trans hAE).trans ⟨f, S, hS, hbij⟩
  · exact (h2.symm.trans hBE).trans ⟨f, S, hS, hbij⟩

theorem Paradoxical.of_hom {H : Type*} [Group H] [MulAction H X] {E : Set X} (φ : G →* H)
    (hφ : ∀ (g : G) (x : X), (φ g) • x = g • x) (h : Paradoxical G E) : Paradoxical H E := by
  obtain ⟨A, B, hA, hB, hAB, hAE, hBE⟩ := h
  exact ⟨A, B, hA, hB, hAB, hAE.of_hom φ hφ, hBE.of_hom φ hφ⟩

end BT

