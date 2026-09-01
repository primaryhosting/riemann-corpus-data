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

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a
regular `n`-gon, indexed by `ZMod n`: the rotation `r i` sends `v` to `v - i` and the
reflection `sr i` sends `v` to `i - v`. -/
def ngonAct : DihedralGroup n → ZMod n → ZMod n
  | r i, v => v - i
  | sr i, v => i - v

instance ngonMulAction : MulAction (DihedralGroup n) (ZMod n) where
  smul := ngonAct
  one_smul v := by
    show ngonAct (1 : DihedralGroup n) v = v
    show ngonAct (r 0) v = v
    simp [ngonAct]
  mul_smul g h v := by
    show ngonAct (g * h) v = ngonAct g (ngonAct h v)
    cases g with
    | r i => cases h with
      | r j => show ngonAct (r (i + j)) v = _; simp [ngonAct]; ring
      | sr j => show ngonAct (sr (j - i)) v = _; simp [ngonAct]; ring
    | sr i => cases h with
      | r j => show ngonAct (sr (i + j)) v = _; simp [ngonAct]; ring
      | sr j => show ngonAct (r (j - i)) v = _; simp [ngonAct]; ring

@[simp] lemma ngon_r_smul (i v : ZMod n) : (r i : DihedralGroup n) • v = v - i := rfl

@[simp] lemma ngon_sr_smul (i v : ZMod n) : (sr i : DihedralGroup n) • v = i - v := rfl

/-- The permutation character of the `n`-gon representation: the number of vertices fixed by
a given element of the dihedral group. -/
noncomputable def ngonChar [NeZero n] (g : DihedralGroup n) : ℕ :=
  (Finset.univ.filter (fun v : ZMod n => g • v = v)).card

/-- The stabiliser of a vertex consists of the identity rotation and one reflection. -/
lemma stabilizer_vertex [NeZero n] (v : ZMod n) :
    (Finset.univ.filter (fun g : DihedralGroup n => g • v = v)) = {r 0, sr (2 * v)} := by
  ext g
  cases g with
  | r i =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, ngon_r_smul]
      constructor
      · intro h
        left
        have : i = 0 := by
          have := sub_eq_self.mp h
          simpa using this
        simp [this]
      · rintro (h | h)
        · rw [DihedralGroup.r.injEq] at h
          simp [h]
        · exact absurd h (fun hh => by cases hh)
  | sr i =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, ngon_sr_smul]
      constructor
      · intro h
        right
        have : i = 2 * v := by linear_combination h
        simp [this]
      · rintro (h | h)
        · exact absurd h (fun hh => by cases hh)
        · rw [DihedralGroup.sr.injEq] at h
          subst h
          ring
  
/-- Each vertex has a stabiliser of size exactly `2`. -/
lemma card_stabilizer_vertex [NeZero n] (v : ZMod n) :
    (Finset.univ.filter (fun g : DihedralGroup n => g • v = v)).card = 2 := by
  rw [stabilizer_vertex v, Finset.card_insert_of_notMem (by
    simp only [Finset.mem_singleton]
    exact fun hh => by cases hh), Finset.card_singleton]

/--
**Pentagon Pentagon Character Multiplicity Ext.**

Generalisation of the pentagon (`n = 5`, i.e. `D₅`) computation to arbitrary regular `n`-gons:
the sum of the permutation character of the vertex representation of `DihedralGroup n` equals
`2 * n = |DihedralGroup n|`, so that the multiplicity of the trivial representation inside the
permutation representation on the vertices of a regular `n`-gon is exactly `1`
(equivalently, the action on the vertices is transitive, by Burnside's lemma).
-/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (∑ g : DihedralGroup n, ngonChar g) = 2 * n ∧
      (Fintype.card (DihedralGroup n) : ℚ)⁻¹ * ∑ g : DihedralGroup n, (ngonChar g : ℚ) = 1 := by
  have key : (∑ g : DihedralGroup n, ngonChar g) = 2 * n := by
    have h1 : ∀ g : DihedralGroup n,
        ngonChar g = ∑ v : ZMod n, if g • v = v then 1 else 0 := by
      intro g
      simp only [ngonChar, Finset.card_filter]
    calc (∑ g : DihedralGroup n, ngonChar g)
        = ∑ g : DihedralGroup n, ∑ v : ZMod n, if g • v = v then 1 else 0 := by
          simp [h1]
      _ = ∑ v : ZMod n, ∑ g : DihedralGroup n, if g • v = v then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ _v : ZMod n, 2 := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [← Finset.card_filter]
          exact card_stabilizer_vertex v
      _ = 2 * n := by
          simp [Finset.sum_const, ZMod.card, mul_comm]
  refine ⟨key, ?_⟩
  have hcard : (Fintype.card (DihedralGroup n) : ℚ) = 2 * n := by
    rw [DihedralGroup.card]; push_cast; ring
  have hsum : (∑ g : DihedralGroup n, (ngonChar g : ℚ)) = 2 * n := by
    have := congrArg (fun m : ℕ => (m : ℚ)) key
    push_cast at this
    simpa using this
  rw [hcard, hsum]
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

/-- The original pentagon case: `D₅` acting on the five vertices of a regular pentagon. -/
theorem pentagon_character_multiplicity :
    (∑ g : DihedralGroup 5, ngonChar g) = 10 :=
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

