-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

open DihedralGroup

namespace Brockian

/-!
## Setup: the dihedral group acting on the vertices of a regular `n`-gon

We model the vertices of the regular `n`-gon by `ZMod n`.  The dihedral group
`DihedralGroup n` acts on them, with the rotation `r i` translating by `-i` and the
reflection `sr i` acting by `x ↦ i - x`.  (The signs are dictated by Mathlib's
multiplication convention `r i * r j = r (i + j)`, `r i * sr j = sr (j - i)`,
`sr i * r j = sr (i + j)`, `sr i * sr j = r (j - i)`.)
-/

/-- The underlying map of the action of `DihedralGroup n` on the vertex set `ZMod n`
of the regular `n`-gon. -/
def vertexSMul {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | r i, x => x - i
  | sr i, x => i - x

/-- The natural action of the dihedral group `DihedralGroup n` on the vertex set
`ZMod n` of the regular `n`-gon. -/
instance vertexAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := vertexSMul
  one_smul x := by
    show vertexSMul (r 0) x = x
    simp [vertexSMul]
  mul_smul g h x := by
    cases g with
    | r i =>
      cases h with
      | r j =>
        show vertexSMul (r (i + j)) x = vertexSMul (r i) (vertexSMul (r j) x)
        simp [vertexSMul]; ring
      | sr j =>
        show vertexSMul (sr (j - i)) x = vertexSMul (r i) (vertexSMul (sr j) x)
        simp [vertexSMul]; ring
    | sr i =>
      cases h with
      | r j =>
        show vertexSMul (sr (i + j)) x = vertexSMul (sr i) (vertexSMul (r j) x)
        simp [vertexSMul]; ring
      | sr j =>
        show vertexSMul (r (j - i)) x = vertexSMul (sr i) (vertexSMul (sr j) x)
        simp [vertexSMul]; ring

@[simp] lemma vertex_r_smul {n : ℕ} (i x : ZMod n) : (r i) • x = x - i := rfl

@[simp] lemma vertex_sr_smul {n : ℕ} (i x : ZMod n) : (sr i) • x = i - x := rfl

noncomputable instance orbitQuotientFintype (n : ℕ) [NeZero n] :
    Fintype (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) :=
  Fintype.ofFinite _

/-- The action of the dihedral group on the vertices of the `n`-gon is transitive:
there is exactly one orbit. -/
lemma card_orbits (n : ℕ) [NeZero n] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ (0 : ZMod n), ?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    refine ⟨r (0 - a), ?_⟩
    show (r (0 - a)) • (0 : ZMod n) = a
    rw [vertex_r_smul]; ring

/-!
## The permutation character

`permChar n g` is the value at `g` of the character of the permutation representation of
`DihedralGroup n` on the vertices of the `n`-gon, i.e. the number of vertices fixed by `g`.
-/

/-- The permutation character of the dihedral group acting on the vertices of the
regular `n`-gon: the number of vertices fixed by `g`. -/
noncomputable def permChar (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℕ :=
  Fintype.card (MulAction.fixedBy (ZMod n) g)

/-- Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) applied
to the vertex action: the total number of fixed vertices is `|D_n| = 2n`. -/
lemma sum_permChar (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, permChar n g = 2 * n := by
  simp only [permChar]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group, card_orbits, one_mul,
    DihedralGroup.card]

/-!
## Explicit values of the permutation character

These are not needed for the main theorem, but they pin down the character concretely and
confirm that the setup is the intended one: a nontrivial rotation fixes no vertex, the
identity fixes all `n` of them, and (for odd `n`) every reflection fixes exactly one vertex.
-/

/-- The identity rotation fixes every vertex. -/
lemma fixedBy_r_zero (n : ℕ) :
    MulAction.fixedBy (ZMod n) (r (0 : ZMod n)) = Set.univ := by
  ext x; simp

/-- The identity of `DihedralGroup n` has character value `n`. -/
lemma permChar_r_zero (n : ℕ) [NeZero n] : permChar n (r 0) = n := by
  rw [permChar, Fintype.card_congr (Equiv.setCongr (fixedBy_r_zero n))]
  simp [ZMod.card]

/-- A nontrivial rotation fixes no vertex, so its character value is `0`. -/
lemma permChar_r_ne_zero (n : ℕ) [NeZero n] {i : ZMod n} (hi : i ≠ 0) :
    permChar n (r i) = 0 := by
  rw [permChar, Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  have hx : (x : ZMod n) - i = x := x.2
  exact hi (by linear_combination -hx)

/-- For odd `n` the element `2` is invertible in `ZMod n`. -/
lemma exists_two_inv_of_odd {n : ℕ} (hn : Odd n) : ∃ c : ZMod n, (2 : ZMod n) * c = 1 := by
  obtain ⟨m, hm⟩ := hn
  refine ⟨((m + 1 : ℕ) : ZMod n), ?_⟩
  have h : (2 : ZMod n) * ((m + 1 : ℕ) : ZMod n) = ((2 * m + 1 : ℕ) : ZMod n) + 1 := by
    push_cast; ring
  rw [h, ← hm, ZMod.natCast_self, zero_add]

/-- For odd `n` every reflection fixes exactly one vertex, so its character value is `1`. -/
lemma permChar_sr_of_odd (n : ℕ) [NeZero n] (hn : Odd n) (i : ZMod n) :
    permChar n (sr i) = 1 := by
  obtain ⟨c, hc⟩ := exists_two_inv_of_odd (n := n) hn
  rw [permChar, Fintype.card_eq_one_iff]
  refine ⟨⟨i * c, show i - i * c = i * c by linear_combination (-i) * hc⟩, ?_⟩
  rintro ⟨y, hy⟩
  have hy' : i - y = y := hy
  exact Subtype.ext (show y = i * c by linear_combination (-c) * hy' + (-y) * hc)

/-!
## Main result

For the pentagon (`n = 5`) the permutation representation of `D₅` on the five vertices
contains the trivial representation exactly once.  The theorem below extends this to every
regular `n`-gon: the multiplicity

  `⟨permChar, 1⟩ = (1 / |D_n|) * ∑_{g} permChar g`

of the trivial character in the vertex permutation character equals `1`, for all `n ≥ 1`.
-/

/-- **Pentagon Pentagon Character Multiplicity Ext.**  For every `n ≥ 1`, the multiplicity
of the trivial character inside the character of the permutation representation of the
dihedral group `DihedralGroup n` on the vertices of the regular `n`-gon equals `1`.  This
generalizes the pentagon (`n = 5`, the group `D₅`) case to all `n`-gons.  The proof is
Burnside's lemma, `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, together with
transitivity of the vertex action. -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (∑ g : DihedralGroup n, (permChar n g : ℚ)) / (Fintype.card (DihedralGroup n) : ℚ) = 1 := by
  have hsum : (∑ g : DihedralGroup n, (permChar n g : ℚ)) = ((2 * n : ℕ) : ℚ) := by
    rw [← sum_permChar n]
    push_cast
    rfl
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [hsum, DihedralGroup.card]
  push_cast
  field_simp

/-- The pentagon case: the ten elements of `D₅` fix ten vertices in total, so the trivial
representation occurs with multiplicity one in the permutation representation of `D₅` on
the five vertices of the pentagon. -/
theorem pentagon_sum_permChar :
    ∑ g : DihedralGroup 5, permChar 5 g = 10 :=
  sum_permChar 5

/-- The explicit character table entry for the pentagon: the identity fixes all five
vertices, each nontrivial rotation fixes none, and each of the five reflections fixes
exactly one vertex. -/
theorem pentagon_permChar_values :
    permChar 5 (r 0) = 5 ∧ (∀ i : ZMod 5, i ≠ 0 → permChar 5 (r i) = 0) ∧
      (∀ i : ZMod 5, permChar 5 (sr i) = 1) :=
  ⟨permChar_r_zero 5, fun _ hi => permChar_r_ne_zero 5 hi,
    fun i => permChar_sr_of_odd 5 (by decide) i⟩

/-- The pentagon case of the main theorem. -/
theorem pentagon_character_multiplicity :
    (∑ g : DihedralGroup 5, (permChar 5 g : ℚ)) / (Fintype.card (DihedralGroup 5) : ℚ) = 1 :=
  PentagonPentagonCharacterMultiplicityExt 5

end Brockian

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

