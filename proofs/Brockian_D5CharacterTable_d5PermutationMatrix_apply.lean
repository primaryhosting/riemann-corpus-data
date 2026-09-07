/-
  Brockian/D5CharacterTable.lean

  Finite character facts for the D5 permutation representation on
  `VertexSpace = Fin 5 -> C`.

  Honest scope:
    * define the permutation matrix of the D5 action and its trace character;
    * prove the matrix acts on vertex functions as `d5Pull`;
    * identify the trace with the number of fixed vertices;
    * compute the identity, rotation, and reflection character values.

  No isotypic-completeness or analytic spectral claims are made here.
-/
import Mathlib
import Brockian.D5Representation
import Brockian.D5Isotypic
import Brockian.AutomorphismFull

open BigOperators
open DihedralGroup
open Brockian.Automorphism
open Brockian.D5Representation

namespace Brockian.D5CharacterTable

/-- Permutation matrix of the D5 pullback action in the vertex delta basis. -/
noncomputable def d5PermutationMatrix (g : DihedralGroup 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun x y => if dihedralHom g y = x then 1 else 0

/-- Matrix entries of the D5 permutation representation. -/
theorem d5PermutationMatrix_apply (g : DihedralGroup 5) (x y : Fin 5) :
    d5PermutationMatrix g x y =
      if dihedralHom g y = x then (1 : ℂ) else 0 :=
  rfl

/-- The permutation matrix acts on vertex functions by the existing `d5Pull`. -/
theorem d5PermutationMatrix_mulVec (g : DihedralGroup 5) (f : VertexSpace) (x : Fin 5) :
    (d5PermutationMatrix g).mulVec f x = d5Pull g f x := by
  classical
  simp only [Matrix.mulVec, dotProduct, d5PermutationMatrix, d5Pull_apply]
  rw [Finset.sum_eq_single ((dihedralHom g).symm x)]
  · simp
  · intro y _ hy
    have hne : dihedralHom g y ≠ x := by
      intro h
      apply hy
      rw [← h]
      simp
    simp [hne]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- Character of the permutation representation on the five vertices. -/
noncomputable def d5Character (g : DihedralGroup 5) : ℂ :=
  Matrix.trace (d5PermutationMatrix g)

/-- The permutation character is the sum of diagonal fixed-vertex indicators. -/
theorem d5Character_eq_sum_fixed (g : DihedralGroup 5) :
    d5Character g =
      ∑ x : Fin 5, if dihedralHom g x = x then (1 : ℂ) else 0 := by
  simp [d5Character, d5PermutationMatrix, Matrix.trace]

/-- The identity element fixes all five vertices, so its trace is `5`. -/
theorem d5Character_one : d5Character (1 : DihedralGroup 5) = 5 := by
  rw [d5Character_eq_sum_fixed]
  have hterm :
      (fun x : Fin 5 =>
        if dihedralHom (1 : DihedralGroup 5) x = x then (1 : ℂ) else 0) =
        fun _ => (1 : ℂ) := by
    funext x
    simp
  rw [show (∑ x : Fin 5,
      if dihedralHom (1 : DihedralGroup 5) x = x then (1 : ℂ) else 0) =
        ∑ x : Fin 5, (1 : ℂ) by rw [hterm]]
  norm_num [Fin.sum_univ_succ]

/-- Rotation character values: the identity rotation has trace `5`, the other
four rotations have trace `0`. -/
theorem d5Character_rotation (k : Fin 5) :
    d5Character (r k) = if k = 0 then (5 : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    rw [d5Character_eq_sum_fixed]
    have hterm :
        (fun x : Fin 5 =>
          if dihedralHom (r (0 : Fin 5)) x = x then (1 : ℂ) else 0) =
          fun _ => (1 : ℂ) := by
      funext x
      simp [dihedralHom_r, rotIso, rotEquiv]
    rw [show (∑ x : Fin 5,
        if dihedralHom (r (0 : Fin 5)) x = x then (1 : ℂ) else 0) =
          ∑ x : Fin 5, (1 : ℂ) by rw [hterm]]
    norm_num [Fin.sum_univ_succ]
  · rw [if_neg hk]
    fin_cases k
    · contradiction
    · rw [d5Character_eq_sum_fixed]
      norm_num [dihedralHom_r, rotIso, rotEquiv, Fin.sum_univ_succ, Fin.ext_iff]
    · rw [d5Character_eq_sum_fixed]
      norm_num [dihedralHom_r, rotIso, rotEquiv, Fin.sum_univ_succ, Fin.ext_iff]
    · rw [d5Character_eq_sum_fixed]
      norm_num [dihedralHom_r, rotIso, rotEquiv, Fin.sum_univ_succ, Fin.ext_iff]
    · rw [d5Character_eq_sum_fixed]
      norm_num [dihedralHom_r, rotIso, rotEquiv, Fin.sum_univ_succ, Fin.ext_iff]

/-- A nontrivial rotation has no fixed vertex in the permutation representation. -/
theorem d5Character_rotation_ne_zero {k : Fin 5} (hk : k ≠ 0) :
    d5Character (r k) = 0 := by
  rw [d5Character_rotation, if_neg hk]

/-- Every reflection of the pentagon fixes exactly one vertex, so its trace is `1`. -/
theorem d5Character_reflection (b : Fin 5) :
    d5Character (sr b) = 1 := by
  rw [d5Character_eq_sum_fixed]
  fin_cases b <;> norm_num [dihedralHom_sr, reflIso, reflEquiv, Fin.sum_univ_succ, Fin.ext_iff]
    <;> decide

end Brockian.D5CharacterTable
