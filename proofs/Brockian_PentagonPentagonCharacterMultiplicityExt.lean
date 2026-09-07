/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

variable {n : ℕ}

/-- The permutation action of the dihedral group `DihedralGroup n` on the `n` vertices of the
regular `n`-gon (labelled by `ZMod n`): the rotation `r i` sends a vertex `x` to `x + i`, and the
reflection `sr i` sends `x` to `-i - x`. -/
def vertexPerm (n : ℕ) : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun g := match g with
    | .r i => Equiv.addRight i
    | .sr i => Equiv.subLeft (-i)
  map_one' := by
    apply Equiv.ext
    intro x
    show x + (0 : ZMod n) = x
    exact add_zero x
  map_mul' := by
    rintro (i | i) (j | j) <;> apply Equiv.ext <;> intro x <;>
      simp [Equiv.addRight, Equiv.subLeft, Equiv.Perm.mul_apply] <;> ring

@[simp]
theorem vertexPerm_r (i x : ZMod n) : vertexPerm n (.r i) x = x + i := rfl

@[simp]
theorem vertexPerm_sr (i x : ZMod n) : vertexPerm n (.sr i) x = -i - x := rfl

/-- The character of the vertex permutation representation of `DihedralGroup n`: the number of
vertices fixed by the symmetry `g`. -/
def vertexCharacter (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℕ :=
  {x : ZMod n | vertexPerm n g x = x}.toFinset.card

theorem vertexCharacter_eq_filter [NeZero n] (g : DihedralGroup n) :
    vertexCharacter n g = (univ.filter fun x : ZMod n => vertexPerm n g x = x).card := by
  simp [vertexCharacter, Set.toFinset_setOf]

/-- A rotation fixes every vertex if it is trivial, and no vertex otherwise. -/
theorem vertexCharacter_r [NeZero n] (i : ZMod n) :
    vertexCharacter n (.r i) = if i = 0 then n else 0 := by
  rw [vertexCharacter_eq_filter]
  by_cases hi : i = 0
  · subst hi
    simp [ZMod.card]
  · simp only [vertexPerm_r, hi, if_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    simpa using fun h => hi (by linear_combination h)

/-- Summed over all rotations, the character contributes `n`. -/
theorem sum_vertexCharacter_r [NeZero n] :
    ∑ i : ZMod n, vertexCharacter n (.r i) = n := by
  simp [vertexCharacter_r]

/-- Summed over all reflections, the character contributes `n`: the fixed-point sets of the
reflections are exactly the fibres of the map `x ↦ -2x`. -/
theorem sum_vertexCharacter_sr [NeZero n] :
    ∑ i : ZMod n, vertexCharacter n (.sr i) = n := by
  have key : ∀ i : ZMod n,
      (univ.filter fun x : ZMod n => vertexPerm n (.sr i) x = x)
        = univ.filter fun x : ZMod n => -2 * x = i := by
    intro i
    apply Finset.filter_congr
    intro x _
    simp only [vertexPerm_sr]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  have hcard : (univ : Finset (ZMod n)).card
      = ∑ i : ZMod n, (univ.filter fun x : ZMod n => -2 * x = i).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (-2 * x))
  calc ∑ i : ZMod n, vertexCharacter n (.sr i)
      = ∑ i : ZMod n, (univ.filter fun x : ZMod n => -2 * x = i).card := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [vertexCharacter_eq_filter, key i]
    _ = (univ : Finset (ZMod n)).card := hcard.symm
    _ = n := by simp [ZMod.card]

theorem sum_vertexCharacter [NeZero n] :
    ∑ g : DihedralGroup n, vertexCharacter n g = 2 * n := by
  let e : ZMod n ⊕ ZMod n ≃ DihedralGroup n :=
    { toFun := Sum.elim DihedralGroup.r DihedralGroup.sr
      invFun := fun g => match g with
        | .r i => Sum.inl i
        | .sr i => Sum.inr i
      left_inv := by rintro (i | i) <;> rfl
      right_inv := by rintro (i | i) <;> rfl }
  have := Fintype.sum_equiv e.symm (fun g => vertexCharacter n g)
    (fun x => vertexCharacter n (e x)) (fun g => by cases g <;> rfl)
  rw [this, Fintype.sum_sum_type]
  simp only [e, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr]
  rw [sum_vertexCharacter_r, sum_vertexCharacter_sr]
  ring

/--
**Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the `D₅`-pentagon computation to arbitrary regular `n`-gons: for every `n ≥ 1`
the vertex permutation character of `DihedralGroup n` sums to `2n = |DihedralGroup n|` over the
group, i.e. by Burnside's formula the trivial representation occurs with multiplicity exactly `1`
in the vertex permutation representation (equivalently, the action on the vertices of the
`n`-gon is transitive).
-/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (∑ g : DihedralGroup n, vertexCharacter n g) = 2 * n ∧
    (∑ g : DihedralGroup n, vertexCharacter n g) = Fintype.card (DihedralGroup n) ∧
    (∑ g : DihedralGroup n, vertexCharacter n g) / Fintype.card (DihedralGroup n) = 1 := by
  have hcard : Fintype.card (DihedralGroup n) = 2 * n := DihedralGroup.card
  refine ⟨sum_vertexCharacter, by rw [sum_vertexCharacter, hcard], ?_⟩
  rw [sum_vertexCharacter, hcard, Nat.div_self]
  have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

/-- The pentagon case `n = 5`: the vertex character of `D₅` sums to `10 = |D₅|`. -/
theorem pentagon_character_multiplicity :
    (∑ g : DihedralGroup 5, vertexCharacter 5 g) = 10 :=
  (PentagonPentagonCharacterMultiplicityExt 5).1

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

