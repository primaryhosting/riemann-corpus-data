/-
  Brockian/GoldbachSelectionRule.lean — the UNCONDITIONAL finite selection rule.

  Harvests the elementary, finite, fully-provable core of the paper
  "A Pentagonal Selection Rule for Goldbach Representations" (Thms 2.2, 2.3, 2.5,
  Remark 2.6). Everything here is a decidable statement about `ZMod m`; NONE of it
  is progress on Goldbach — the paper claims none, and neither does this module.

  ┌────────────────────────────────────────────────────────────────────────────┐
  │  RUNG: PROVED (unconditional, finite). The single new piece the reused       │
  │  admissibility core lacks is the D_m UNIFICATION (Thm 2.5): the reflection   │
  │  side (Goldbach `p+q=2n`, Thm 2.2) and the translation side (twin/cousin gap │
  │  transition, Thm 2.3) are the two orbits of ONE count law that holds         │
  │  uniformly across the whole affine dihedral symmetry group `Σ ≅ D_m`.        │
  └────────────────────────────────────────────────────────────────────────────┘

  ## What is proved
    • `admissibleUnits_card` — **the master count (general prime `m`).** For ANY
        permutation `f : Equiv.Perm (ZMod m)`, the set of units `i` with `f i` a unit
        has cardinality `m − 1` if `f 0 = 0`, else `m − 2`. Real reasoning: `f i = 0`
        has the unique solution `i = f⁻¹ 0`, so the admissible set is
        `univ \ {0, f⁻¹ 0}`, whose two excluded points coincide iff `f 0 = 0`.
    • `admissibleUnits_card_totient` — Remark 2.6 form: the same count is
        `φ(m) − (if f 0 = 0 then 0 else 1)` (since `φ(m) = m − 1` for prime `m`).
    • `admissible_reflection_card` / `admissible_translation_card` — **Thm 2.2 / Thm 2.3
        (general prime `m`)** as the reflection (`x ↦ c − x`, `f 0 = c`) and translation
        (`x ↦ x + g`, `f 0 = g`) restrictions of the master count.
    • `admissible_card_dihedral` — **Thm 2.5:** the master count applied to every element
        of the affine dihedral group `Σ = image (dihedralToPerm) ≅ D_m` — one statement,
        both sides as its rotation / reflection orbits.
    • `translation_eq_dihedral` / `reflection_eq_dihedral` — identifies translations and
        reflections with the `r` / `sr` families of `AffineSymmetry.dihedralToPerm`,
        so `Σ` here is literally the group built in `Brockian.AffineSymmetry`.
    • `admissibleUnits_translation_eq_residues` / `_reflection_eq_residues` — REUSE
        bridges: these units-admissibility sets equal the existing
        `Brockian.Admissibility.admissibleResidues`, so the count agrees with the
        already-verified `admissibility_count_dichotomy`.
    • `goldbachPairs_card` (Thm 2.2, `m = 5` concrete) / `gapPairs_card` (Thm 2.3,
        `m = 5` concrete) — the paper's literal pair-set forms
        `𝒢(c) = {(i,j) ∈ Uˣ×Uˣ : i+j = c}`, `𝒯(g) = {(i,j) : j = i+g}`, each of
        cardinality `4` if the parameter is `0`, else `3`, by kernel `decide`
        (COMPUTATION).
    • `goldbach_pairs_eq_reflection_admissible` / `gap_pairs_eq_translation_admissible`
        — the pair-set counts equal the corresponding master-count restrictions,
        making 2.2 / 2.3 rigorously the restrictions of the single statement 2.5.
    • `sigma_card` — `|Σ| = 2m` (re-exported from `AffineSymmetry.dihedralToPerm_card`).
    • `units_card` — `|(ZMod m)ˣ| = m − 1`, so the `φ(m)` of Remark 2.6 is the unit count.

  ## What is NOT proved
    • **Goldbach's conjecture** — untouched. This is the finite selection rule only.
    • **The 4/3 asymptotic ratio / equidistribution (paper Thm 3.1).** That the
        admissible residues are asymptotically EQUIDISTRIBUTED among the primes — hence
        the "4 : 3" heuristic for representation densities — is CONDITIONAL on the
        Hardy–Littlewood prime-tuple conjecture. It is an analytic statement about the
        primes, not a finite `ZMod m` fact, and is deliberately NOT stated here (not even
        as a Lean conditional). The unconditional content is purely the finite counting
        law `|𝒜(f)| ∈ {m−1, m−2}`; the ratio `4/3 = (m−1)/(m−2)|_{m=5}` is a ratio of
        these finite counts, carrying NO claim about how primes populate the residues.

  Verification: AXLE independent — @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `admit`,
  no new `axiom`, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import Brockian.AffineSymmetry
import Brockian.Admissibility
import Brockian.AdmissibilityDiagonal

open Finset
open DihedralGroup
open Brockian.AffineSymmetry
open Brockian.Admissibility
open Brockian.AdmissibilityDiagonal

namespace Brockian.GoldbachSelectionRule

/-! ## 1. The admissible-units set of a permutation and the master count

For a permutation `f` of `ZMod m` (`m` prime), a residue `i` is *admissible* for `f`
when both `i` and `f i` are units — i.e. neither is `0`, since in the field `ZMod m`
a residue is a unit iff it is nonzero. The paper's `𝒜(f) := {i ∈ (ZMod m)ˣ : f i ∈ (ZMod m)ˣ}`. -/

/-- **`admissibleUnits m f`** — residues `i : ZMod m` with `i` and `f i` both units
(equivalently both nonzero, as `mem_admissibleUnits_iff` records). This is the paper's
`𝒜(f)`. -/
def admissibleUnits (m : ℕ) [Fact m.Prime] (f : Equiv.Perm (ZMod m)) : Finset (ZMod m) :=
  Finset.univ.filter (fun i => i ≠ 0 ∧ f i ≠ 0)

/-- Membership in `admissibleUnits` is exactly the paper's units condition
`IsUnit i ∧ IsUnit (f i)` (a unit is a nonzero element of the field `ZMod m`). -/
theorem mem_admissibleUnits_iff {m : ℕ} [Fact m.Prime] (f : Equiv.Perm (ZMod m))
    (i : ZMod m) : i ∈ admissibleUnits m f ↔ IsUnit i ∧ IsUnit (f i) := by
  simp only [admissibleUnits, Finset.mem_filter, Finset.mem_univ, true_and,
    isUnit_iff_ne_zero]

/-- The admissible set is the whole space minus the two forbidden residues `0` and
`f⁻¹ 0`: `i` fails when `i = 0` (`i` not a unit) or `f i = 0` (i.e. `i = f⁻¹ 0`). -/
theorem admissibleUnits_eq_sdiff {m : ℕ} [Fact m.Prime] (f : Equiv.Perm (ZMod m)) :
    admissibleUnits m f = Finset.univ \ {0, f.symm 0} := by
  ext i
  simp only [admissibleUnits, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨hi, hfi⟩
    exact ⟨hi, fun hc => hfi (by rw [hc]; exact f.apply_symm_apply 0)⟩
  · rintro ⟨hi, hsy⟩
    refine ⟨hi, fun hc => hsy ?_⟩
    have h := congrArg f.symm hc
    rwa [f.symm_apply_apply] at h

/-- **The master count (Thm 2.5 core, general prime `m`).** For any permutation `f`
of `ZMod m`, `|𝒜(f)| = m − 1` if `f 0 = 0`, else `m − 2`. The two excluded residues
`0` and `f⁻¹ 0` coincide exactly when `f 0 = 0`. -/
theorem admissibleUnits_card {m : ℕ} [Fact m.Prime] (f : Equiv.Perm (ZMod m)) :
    (admissibleUnits m f).card = if f 0 = 0 then m - 1 else m - 2 := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).pos.ne'⟩
  have hcard : (Finset.univ : Finset (ZMod m)).card = m := by
    rw [Finset.card_univ, ZMod.card]
  rw [admissibleUnits_eq_sdiff, Finset.card_sdiff, Finset.inter_univ, hcard]
  by_cases h : f 0 = 0
  · have hs : f.symm 0 = 0 := by
      have h2 := f.symm_apply_apply 0
      rw [h] at h2; exact h2
    rw [if_pos h, hs,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self (0 : ZMod m)),
      Finset.card_singleton]
  · have hs : f.symm 0 ≠ 0 := by
      intro hc
      apply h
      have h2 := congrArg f hc
      rw [f.apply_symm_apply] at h2
      exact h2.symm
    rw [if_neg h, Finset.card_pair (Ne.symm hs)]

/-- **Remark 2.6 form.** The count equals `φ(m)` minus an indicator: `φ(m)` if
`f 0 = 0` (nothing extra excluded), else `φ(m) − 1`. Uses `φ(m) = m − 1` for prime `m`. -/
theorem admissibleUnits_card_totient {m : ℕ} [Fact m.Prime] (f : Equiv.Perm (ZMod m)) :
    (admissibleUnits m f).card = Nat.totient m - (if f 0 = 0 then 0 else 1) := by
  have hm : 2 ≤ m := (Fact.out : m.Prime).two_le
  rw [admissibleUnits_card, Nat.totient_prime (Fact.out : m.Prime)]
  split_ifs <;> omega

/-! ## 2. The affine family `Σ`: translations and reflections

`Σ = {x ↦ x + a} ∪ {x ↦ a − x}` — built from `AffineSymmetry.affinePerm` (slope `+1`
= translation, slope `−1` = reflection). These are the `r` / `sr` families of the
dihedral realization `AffineSymmetry.dihedralToPerm : DihedralGroup m →* Equiv.Perm (ZMod m)`. -/

/-- Translation `x ↦ x + g` (slope `+1`), the reused `affinePerm m 1 g`. -/
def translation (m : ℕ) [Fact m.Prime] (g : ZMod m) : Equiv.Perm (ZMod m) :=
  affinePerm m 1 g

/-- Reflection `x ↦ c − x` (slope `−1`), the reused `affinePerm m (-1) c`. -/
def reflection (m : ℕ) [Fact m.Prime] (c : ZMod m) : Equiv.Perm (ZMod m) :=
  affinePerm m (-1) c

@[simp] theorem translation_apply {m : ℕ} [Fact m.Prime] (g x : ZMod m) :
    translation m g x = x + g := by
  rw [translation, affinePerm_apply]; simp

@[simp] theorem reflection_apply {m : ℕ} [Fact m.Prime] (c x : ZMod m) :
    reflection m c x = c - x := by
  rw [reflection, affinePerm_apply]
  simp only [Units.val_neg, Units.val_one]; ring

@[simp] theorem translation_zero {m : ℕ} [Fact m.Prime] (g : ZMod m) :
    translation m g 0 = g := by rw [translation_apply]; simp

@[simp] theorem reflection_zero {m : ℕ} [Fact m.Prime] (c : ZMod m) :
    reflection m c 0 = c := by rw [reflection_apply]; simp

/-- Translations are exactly the rotation family `r` of `dihedralToPerm`. -/
theorem translation_eq_dihedral {m : ℕ} [Fact m.Prime] (g : ZMod m) :
    translation m g = dihedralToPerm m (r g) := by
  rw [translation, dihedralToPerm_r]

/-- Reflections are exactly the reflection family `sr` of `dihedralToPerm`
(`reflection m c = dihedralToPerm m (sr (-c))`). -/
theorem reflection_eq_dihedral {m : ℕ} [Fact m.Prime] (c : ZMod m) :
    reflection m c = dihedralToPerm m (sr (-c)) := by
  rw [reflection, dihedralToPerm_sr, neg_neg]

/-! ## 3. Thm 2.2 / 2.3 (general prime `m`) as restrictions of the master count -/

/-- **Thm 2.2 (general prime `m`) — the Goldbach / reflection side.** With `f x = c − x`
(`f 0 = c`), `|𝒜(f)| = m − 1` if `c = 0`, else `m − 2`. This is the reflection side of
the Goldbach relation `p + q = 2n`. -/
theorem admissible_reflection_card {m : ℕ} [Fact m.Prime] (c : ZMod m) :
    (admissibleUnits m (reflection m c)).card = if c = 0 then m - 1 else m - 2 := by
  rw [admissibleUnits_card, reflection_zero]

/-- **Thm 2.3 (general prime `m`) — the gap / translation side.** With `f x = x + g`
(`f 0 = g`), `|𝒜(f)| = m − 1` if `g = 0`, else `m − 2`. This recovers the twin/cousin
gap transition law. -/
theorem admissible_translation_card {m : ℕ} [Fact m.Prime] (g : ZMod m) :
    (admissibleUnits m (translation m g)).card = if g = 0 then m - 1 else m - 2 := by
  rw [admissibleUnits_card, translation_zero]

/-- **Thm 2.5 — the unification.** The master count applied to EVERY element of the
affine dihedral symmetry group `Σ = image (dihedralToPerm m) ≅ D_m`. Thm 2.2 (the
reflections, `sr`) and Thm 2.3 (the translations, `r`) are its two orbits — a single
count law across all `2m` symmetries. -/
theorem admissible_card_dihedral {m : ℕ} [Fact m.Prime] (σ : DihedralGroup m) :
    (admissibleUnits m (dihedralToPerm m σ)).card
      = if (dihedralToPerm m σ) 0 = 0 then m - 1 else m - 2 :=
  admissibleUnits_card (dihedralToPerm m σ)

/-- **`|Σ| = 2m`.** The affine dihedral group `Σ` has order `2m` (re-exported from
`AffineSymmetry.dihedralToPerm_card`), matching `|D_m|`. -/
theorem sigma_card {m : ℕ} [Fact m.Prime] (hm : (2 : ZMod m) ≠ 0) :
    Nat.card (dihedralToPerm m).range = 2 * m :=
  dihedralToPerm_card m hm

/-- `|(ZMod m)ˣ| = m − 1 = φ(m)`: the unit count that Remark 2.6 calls `φ(m)`. -/
theorem units_card {m : ℕ} [Fact m.Prime] : Fintype.card (ZMod m)ˣ = m - 1 :=
  ZMod.card_units m

/-! ## 4. Reuse bridges to `Brockian.Admissibility.admissibleResidues`

The units-admissibility set of a translation / reflection coincides with the
already-verified `admissibleResidues`, so the master count agrees with the existing
`admissibility_count_dichotomy` (`q − 1` if `g = 0`, else `q − 2`). No duplication. -/

/-- The translation admissible set is exactly the existing `admissibleResidues m g`
(`univ \ {0, −g}`). -/
theorem admissibleUnits_translation_eq_residues {m : ℕ} [Fact m.Prime] (g : ZMod m) :
    admissibleUnits m (translation m g) = admissibleResidues m g := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).pos.ne'⟩
  rw [admissibleUnits_eq_sdiff, admissibleResidues]
  have hs : (translation m g).symm 0 = -g := by
    rw [Equiv.symm_apply_eq, translation_apply, neg_add_cancel]
  rw [hs]

/-- The reflection admissible set is `admissibleResidues m (−c)` (`univ \ {0, c}`). -/
theorem admissibleUnits_reflection_eq_residues {m : ℕ} [Fact m.Prime] (c : ZMod m) :
    admissibleUnits m (reflection m c) = admissibleResidues m (-c) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).pos.ne'⟩
  rw [admissibleUnits_eq_sdiff, admissibleResidues, neg_neg]
  have hs : (reflection m c).symm 0 = c := by
    rw [Equiv.symm_apply_eq, reflection_apply, sub_self]
  rw [hs]

/-- Consistency: the translation count equals the reused dichotomy count. -/
theorem admissible_translation_matches_dichotomy {m : ℕ} [Fact m.Prime] (g : ZMod m) :
    (admissibleUnits m (translation m g)).card = if g = 0 then m - 1 else m - 2 := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).pos.ne'⟩
  rw [admissibleUnits_translation_eq_residues, admissibility_count_dichotomy]

/-! ## 5. The paper's literal pair-set forms at `m = 5` (COMPUTATION, `decide`) -/

/-- **`𝒢(c)` (Thm 2.2, `m = 5`)** — ordered pairs of units summing to `c`. -/
def goldbachPairs (c : ZMod 5) : Finset ((ZMod 5)ˣ × (ZMod 5)ˣ) :=
  Finset.univ.filter (fun p => ((p.1 : ZMod 5) + (p.2 : ZMod 5)) = c)

/-- **`𝒯(g)` (Thm 2.3, `m = 5`)** — ordered pairs of units with `j = i + g`. -/
def gapPairs (g : ZMod 5) : Finset ((ZMod 5)ˣ × (ZMod 5)ˣ) :=
  Finset.univ.filter (fun p => (p.2 : ZMod 5) = (p.1 : ZMod 5) + g)

/-- **Thm 2.2, `m = 5` (concrete).** `|𝒢(c)| = 4` if `c = 0`, else `3`. -/
theorem goldbachPairs_card (c : ZMod 5) :
    (goldbachPairs c).card = if c = 0 then 4 else 3 := by
  revert c; decide

/-- **Thm 2.3, `m = 5` (concrete).** `|𝒯(g)| = 4` if `g = 0`, else `3`. -/
theorem gapPairs_card (g : ZMod 5) :
    (gapPairs g).card = if g = 0 then 4 else 3 := by
  revert g; decide

/-- The paper's pair-count `𝒢(c)` equals the master-count restriction to the
reflection `x ↦ c − x`: Thm 2.2 is rigorously the reflection restriction of Thm 2.5. -/
theorem goldbach_pairs_eq_reflection_admissible (c : ZMod 5) :
    (goldbachPairs c).card = (admissibleUnits 5 (reflection 5 c)).card := by
  rw [goldbachPairs_card, admissible_reflection_card]

/-- The paper's pair-count `𝒯(g)` equals the master-count restriction to the
translation `x ↦ x + g`: Thm 2.3 is rigorously the translation restriction of Thm 2.5. -/
theorem gap_pairs_eq_translation_admissible (g : ZMod 5) :
    (gapPairs g).card = (admissibleUnits 5 (translation 5 g)).card := by
  rw [gapPairs_card, admissible_translation_card]

end Brockian.GoldbachSelectionRule
