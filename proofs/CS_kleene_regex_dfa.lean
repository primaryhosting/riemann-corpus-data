import Mathlib

/-!
# Regular expressions define regular languages

This file proves the "easy" direction of Kleene's theorem: the language matched by a regular
expression is accepted by some DFA with finitely many states (`Language.IsRegular`).

The proof goes through the Myhill–Nerode characterisation
`Language.isRegular_iff_finite_range_leftQuotient`: a language is regular iff it has finitely
many left quotients.
-/

open Language Computability

namespace Kleene

variable {α : Type*}

/-- The union of a family of languages, as a language. -/
def unionOf (T : Set (Language α)) : Language α := {y | ∃ N ∈ T, y ∈ N}

@[simp]
theorem mem_unionOf {T : Set (Language α)} {y : List α} :
    y ∈ unionOf T ↔ ∃ N ∈ T, y ∈ N := Iff.rfl

/-- `L` if `b` is true, the empty language otherwise. -/
def condLang (b : Bool) (L : Language α) : Language α := if b then L else 0

@[simp]
theorem mem_condLang {b : Bool} {L : Language α} {y : List α} :
    y ∈ condLang b L ↔ b = true ∧ y ∈ L := by
  cases b <;> simp [condLang, Language, Language.zero_def]

theorem mem_of_le {L M : Language α} (h : L ≤ M) {x : List α} (hx : x ∈ L) : x ∈ M := h hx

/-! ### Base cases -/

theorem isRegular_zero : (0 : Language α).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset (Set.finite_singleton (0 : Language α)) ?_
  rw [Set.range_subset_iff]
  intro x
  simp only [Set.mem_singleton_iff]
  ext y
  simp [leftQuotient, Language, Language.zero_def]

theorem isRegular_one : (1 : Language α).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset (Set.toFinite {(1 : Language α), 0}) ?_
  rw [Set.range_subset_iff]
  intro x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases eq_or_ne x [] with rfl | hx
  · left; simp
  · right
    ext y
    simp [leftQuotient, Language, Language.zero_def, Language.one_def, hx]

theorem isRegular_singleton (a : α) : ({[a]} : Language α).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset (Set.toFinite {({[a]} : Language α), 1, 0}) ?_
  rw [Set.range_subset_iff]
  intro x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  match x with
  | [] => left; ext y; simp [leftQuotient, Language]
  | [b] =>
      by_cases hb : b = a
      · subst hb
        right; left
        ext y
        simp [leftQuotient, Language, Language.one_def]
      · right; right
        ext y
        simp [leftQuotient, Language, Language.zero_def, hb]
  | b :: c :: t =>
      right; right
      ext y
      simp [leftQuotient, Language, Language.zero_def]

/-! ### Concatenation -/

/-- Membership in the left quotient of a product: either `x` consumes a prefix of the first
factor, or the whole first factor lies inside `x`. -/
theorem mem_leftQuotient_mul (L₁ L₂ : Language α) (x y : List α) :
    y ∈ (L₁ * L₂).leftQuotient x ↔
      y ∈ (L₁.leftQuotient x) * L₂ ∨
        ∃ v, (∃ u, u ++ v = x ∧ u ∈ L₁) ∧ y ∈ L₂.leftQuotient v := by
  simp only [mem_leftQuotient, Language.mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    rcases List.append_eq_append_iff.1 hpq with ⟨as, hx, hq'⟩ | ⟨bs, hp', hy⟩
    · exact Or.inr ⟨as, ⟨p, hx.symm, hp⟩, by rw [← hq']; exact hq⟩
    · exact Or.inl ⟨bs, by rw [← hp']; exact hp, q, hq, hy.symm⟩
  · rintro (⟨b, hb, c, hc, hbc⟩ | ⟨v, ⟨u, huv, hu⟩, hy⟩)
    · exact ⟨x ++ b, hb, c, hc, by rw [List.append_assoc, hbc]⟩
    · exact ⟨u, hu, v ++ y, hy, by rw [← List.append_assoc, huv]⟩

theorem isRegular_mul {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient] at h₁ h₂ ⊢
  refine Set.Finite.subset (s := (fun p : Language α × Set (Language α) => p.1 * L₂ + unionOf p.2)
    '' (Set.range L₁.leftQuotient ×ˢ {T | T ⊆ Set.range L₂.leftQuotient}))
    ((h₁.prod h₂.finite_subsets).image _) ?_
  rw [Set.range_subset_iff]
  intro x
  refine ⟨(L₁.leftQuotient x,
    {N | ∃ v, (∃ u, u ++ v = x ∧ u ∈ L₁) ∧ N = L₂.leftQuotient v}), ⟨⟨x, rfl⟩, ?_⟩, ?_⟩
  · rintro N ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · ext y
    rw [mem_leftQuotient_mul, Language.mem_add]
    simp only [mem_unionOf, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨N, ⟨v, hv, rfl⟩, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hy⟩
    · rintro (h | ⟨v, hv, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨v, hv, rfl⟩, hy⟩

/-! ### Kleene star -/

/-- Splitting a word of `L∗` along a prefix: either the prefix is itself in `L∗`, or the prefix
ends strictly inside one of the factors. -/
theorem kstar_split (L : Language α) :
    ∀ (l : List (List α)), (∀ y ∈ l, y ∈ L) → ∀ (x w : List α), l.flatten = x ++ w →
      (x ∈ L∗ ∧ w ∈ L∗) ∨
        ∃ u v r s, u ++ v = x ∧ v ≠ [] ∧ u ∈ L∗ ∧ v ++ r ∈ L ∧ s ∈ L∗ ∧ w = r ++ s := by
  intro l
  induction l with
  | nil =>
      intro _ x w h
      rw [List.flatten_nil] at h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
      exact Or.inl ⟨nil_mem_kstar L, nil_mem_kstar L⟩
  | cons z l ih =>
      intro hl x w h
      have hz : z ∈ L := hl z (by simp)
      have hl' : ∀ y ∈ l, y ∈ L := fun y hy => hl y (by simp [hy])
      rw [List.flatten_cons] at h
      rcases List.append_eq_append_iff.1 h with ⟨as, hx, hfl⟩ | ⟨bs, hz', hw⟩
      · rcases ih hl' as w hfl with ⟨h1, h2⟩ | ⟨u, v, r, s, huv, hv, hu, hvr, hs, hws⟩
        · refine Or.inl ⟨?_, h2⟩
          rw [hx]
          exact mem_of_le mul_kstar_le_kstar (append_mem_mul hz h1)
        · refine Or.inr ⟨z ++ u, v, r, s, ?_, hv, ?_, hvr, hs, hws⟩
          · rw [List.append_assoc, huv, ← hx]
          · exact mem_of_le mul_kstar_le_kstar (append_mem_mul hz hu)
      · rcases eq_or_ne x [] with rfl | hx
        · refine Or.inl ⟨nil_mem_kstar L, ?_⟩
          rw [← List.nil_append w, ← h]
          exact mem_of_le mul_kstar_le_kstar (append_mem_mul hz (join_mem_kstar hl'))
        · exact Or.inr ⟨[], x, bs, l.flatten, by simp, hx, nil_mem_kstar L,
            by rw [← hz']; exact hz, join_mem_kstar hl', hw⟩

theorem mem_leftQuotient_kstar (L : Language α) (x y : List α) :
    y ∈ (L∗).leftQuotient x ↔
      (x ∈ L∗ ∧ y ∈ L∗) ∨
        ∃ v, (∃ u, u ++ v = x ∧ v ≠ [] ∧ u ∈ L∗) ∧ y ∈ (L.leftQuotient v) * L∗ := by
  rw [mem_leftQuotient]
  constructor
  · rintro hxy
    obtain ⟨l, hl, hmem⟩ := Language.mem_kstar.1 hxy
    rcases kstar_split L l hmem x y hl.symm with h | ⟨u, v, r, s, huv, hv, hu, hvr, hs, hys⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, ⟨u, huv, hv, hu⟩, ⟨r, by rwa [mem_leftQuotient], s, hs, hys.symm⟩⟩
  · rintro (⟨hx, hy⟩ | ⟨v, ⟨u, huv, -, hu⟩, ⟨r, hr, s, hs, hrs⟩⟩)
    · exact mem_of_le (kstar_mul_kstar L).le (append_mem_mul hx hy)
    · rw [mem_leftQuotient] at hr
      have h2 : (v ++ r) ++ s ∈ L∗ := mem_of_le mul_kstar_le_kstar (append_mem_mul hr hs)
      have h3 : u ++ ((v ++ r) ++ s) ∈ L∗ := mem_of_le (kstar_mul_kstar L).le (append_mem_mul hu h2)
      have hxy : x ++ y = u ++ ((v ++ r) ++ s) := by
        rw [← huv, ← hrs]; simp [List.append_assoc]
      rwa [hxy]

theorem isRegular_kstar {L : Language α} (h : L.IsRegular) : (L∗).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient] at h ⊢
  refine Set.Finite.subset (s := (fun p : Bool × Set (Language α) =>
      condLang p.1 (L∗) + unionOf ((fun N => N * L∗) '' p.2))
    '' (Set.univ ×ˢ {T | T ⊆ Set.range L.leftQuotient}))
    ((Set.finite_univ.prod h.finite_subsets).image _) ?_
  rw [Set.range_subset_iff]
  intro x
  classical
  refine ⟨(decide (x ∈ L∗),
    {N | ∃ v, (∃ u, u ++ v = x ∧ v ≠ [] ∧ u ∈ L∗) ∧ N = L.leftQuotient v}),
    ⟨Set.mem_univ _, ?_⟩, ?_⟩
  · rintro N ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · ext y
    rw [mem_leftQuotient_kstar, Language.mem_add]
    simp only [mem_unionOf, mem_condLang, Set.mem_image, Set.mem_setOf_eq, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨N, ⟨M, ⟨v, hv, rfl⟩, rfl⟩, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hy⟩
    · rintro (h | ⟨v, hv, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, hy⟩

/-! ### Main result -/

/-- **Kleene's theorem, easy direction**: the language of a regular expression is regular,
i.e. accepted by a finite DFA. -/
theorem isRegular_matches' (P : RegularExpression α) : P.matches'.IsRegular := by
  induction P with
  | zero => simpa using isRegular_zero
  | epsilon => simpa using isRegular_one
  | char a => simpa [RegularExpression.matches'] using isRegular_singleton a
  | plus P Q hP hQ => simpa [RegularExpression.matches'] using hP.add hQ
  | comp P Q hP hQ => simpa [RegularExpression.matches'] using isRegular_mul hP hQ
  | star P hP => simpa [RegularExpression.matches'] using isRegular_kstar hP

end Kleene

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

