import Mathlib
/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The classical "pentagon" facts about the dihedral group `D₅` (the symmetry group of a regular
pentagon) are:

* `D₅` has two irreducible two-dimensional complex representations `ρ₁`, `ρ₂`, obtained by letting
  the rotation `r` act as a rotation by `2π/5` resp. `4π/5`;
* they are pairwise inequivalent;
* the permutation representation of `D₅` on the five vertices of the pentagon contains each of
  them with multiplicity exactly one — i.e. each `ρⱼ`-isotypic component of the vertex
  representation is exactly two-dimensional.

This file generalises all of this to an arbitrary regular `n`-gon.  For every `j : ZMod n` we build
a genuine two–dimensional complex representation `Brockian.ngonRep n j` of `DihedralGroup n`, and we
compute its character `Brockian.ngonChar n j`.  We then show, purely by character computations:

* `ngonChar n j` has norm one (so `ngonRep n j` is irreducible) as soon as `2 * j ≠ 0`;
* `ngonChar n j` and `ngonChar n l` are orthogonal when `j ≠ l` and `j ≠ -l`;
* the character of the vertex permutation representation pairs to `1` against every `ngonChar n j`,
  i.e. the multiplicity of `ρⱼ` in the vertex representation is one for every `j`.

Specialising to `n = 5` recovers the pentagon statements.
-/

open Complex DihedralGroup

namespace Brockian

section Roots

/-- A primitive `n`-th root of unity in `ℂ`. -/
noncomputable def zetaN (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zetaN_isPrimitiveRoot (n : ℕ) [NeZero n] : IsPrimitiveRoot (zetaN n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zetaN_pow (n : ℕ) [NeZero n] : (zetaN n) ^ n = 1 :=
  (zetaN_isPrimitiveRoot n).pow_eq_one

/-- The additive character `a ↦ ζₙ ^ a` of `ZMod n`. -/
noncomputable def chiN (n : ℕ) [NeZero n] : AddChar (ZMod n) ℂ :=
  AddChar.zmodChar n (zetaN_pow n)

lemma chiN_prim (n : ℕ) [NeZero n] : (chiN n).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root n (zetaN_isPrimitiveRoot n)

lemma chiN_eq_one_iff (n : ℕ) [NeZero n] (a : ZMod n) : chiN n a = 1 ↔ a = 0 :=
  (chiN_prim n).zmod_char_eq_one_iff n a

@[simp] lemma chiN_zero (n : ℕ) [NeZero n] : chiN n 0 = 1 := AddChar.map_zero_eq_one _

lemma chiN_add (n : ℕ) [NeZero n] (a b : ZMod n) :
    chiN n (a + b) = chiN n a * chiN n b := AddChar.map_add_eq_mul _ _ _

lemma chiN_mul_neg (n : ℕ) [NeZero n] (a : ZMod n) : chiN n a * chiN n (-a) = 1 := by
  rw [← chiN_add, add_neg_cancel, chiN_zero]

lemma chiN_norm (n : ℕ) [NeZero n] (a : ZMod n) : ‖chiN n a‖ = 1 := by
  have h : (chiN n a) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  exact Complex.norm_eq_one_of_pow_eq_one h (NeZero.ne n)

/-- Complex conjugation on the values of `chiN` is negation of the argument. -/
lemma chiN_conj (n : ℕ) [NeZero n] (a : ZMod n) :
    (starRingEnd ℂ) (chiN n a) = chiN n (-a) := by
  have h1 : chiN n a * chiN n (-a) = 1 := chiN_mul_neg n a
  have h2 : (starRingEnd ℂ) (chiN n a) * chiN n a = 1 := by
    rw [mul_comm, Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, chiN_norm n a]
  calc (starRingEnd ℂ) (chiN n a) = (starRingEnd ℂ) (chiN n a) * (chiN n a * chiN n (-a)) := by
        rw [h1, mul_one]
    _ = ((starRingEnd ℂ) (chiN n a) * chiN n a) * chiN n (-a) := by ring
    _ = chiN n (-a) := by rw [h2, one_mul]

/-- Orthogonality of the characters of `ZMod n`: the "geometric sum" of `n`-th roots of unity. -/
lemma sum_chiN (n : ℕ) [NeZero n] (m : ZMod n) :
    ∑ k : ZMod n, chiN n (m * k) = if m = 0 then (n : ℂ) else 0 := by
  classical
  have h : ∀ k : ZMod n, chiN n (m * k) = (AddChar.mulShift (chiN n) m) k := fun _ => rfl
  simp only [h]
  rw [AddChar.sum_eq_ite]
  by_cases hm : m = 0
  · subst hm
    have hz : AddChar.mulShift (chiN n) 0 = 0 := by
      ext x; simp [AddChar.mulShift]
    rw [if_pos hz, if_pos rfl]
    simp
  · rw [if_neg hm, if_neg]
    intro hc
    refine hm ?_
    rw [← chiN_eq_one_iff n m]
    have := congrArg (fun f : AddChar (ZMod n) ℂ => f 1) hc
    simpa [AddChar.mulShift] using this

end Roots

section Dihedral

variable (n : ℕ) [NeZero n]

/-- Splitting a sum over `DihedralGroup n` into the rotations and the reflections. -/
private def dihEquiv : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n where
  toFun := fun s => Sum.rec r sr s
  invFun := fun g => match g with | .r k => Sum.inl k | .sr k => Sum.inr k
  left_inv := by rintro (k | k) <;> rfl
  right_inv := by rintro (k | k) <;> rfl

lemma sum_dihedral {M : Type*} [AddCommMonoid M] (f : DihedralGroup n → M) :
    ∑ g : DihedralGroup n, f g = (∑ k : ZMod n, f (r k)) + ∑ k : ZMod n, f (sr k) := by
  rw [← Equiv.sum_comp (dihEquiv n) f, Fintype.sum_sum_type]
  rfl

/-- The `j`-th two-dimensional complex representation of the dihedral group `DihedralGroup n`,
written in the eigenbasis of the rotation: the rotation `r k` acts as
`diag(ζⁿ ^ (j*k), ζⁿ ^ (-j*k))` and the reflection `sr k` swaps the two eigenlines. -/
noncomputable def ngonRep (j : ZMod n) : DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := match g with
    | .r k => !![chiN n (j * k), 0; 0, chiN n (-(j * k))]
    | .sr k => !![0, chiN n (-(j * k)); chiN n (j * k), 0]
  map_one' := by
    show (!![chiN n (j * (0 : ZMod n)), 0; 0, chiN n (-(j * (0 : ZMod n)))] :
      Matrix (Fin 2) (Fin 2) ℂ) = 1
    simp [Matrix.one_fin_two]
  map_mul' := by
    rintro (a | a) (b | b) <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;>
      ext i k <;> fin_cases i <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, mul_add, mul_sub, neg_sub,
        AddChar.map_add_eq_mul, AddChar.map_sub_eq_div, AddChar.map_neg_eq_inv] <;>
      field_simp

/-- The character of `ngonRep n j`. -/
noncomputable def ngonChar (j : ZMod n) (g : DihedralGroup n) : ℂ :=
  Matrix.trace (ngonRep n j g)

@[simp] lemma ngonChar_r (j k : ZMod n) :
    ngonChar n j (r k) = chiN n (j * k) + chiN n (-(j * k)) := by
  simp [ngonChar, ngonRep, Matrix.trace, Fin.sum_univ_succ]

@[simp] lemma ngonChar_sr (j k : ZMod n) : ngonChar n j (sr k) = 0 := by
  simp [ngonChar, ngonRep, Matrix.trace, Fin.sum_univ_succ]

lemma ngonChar_one (j : ZMod n) : ngonChar n j 1 = 2 := by
  rw [one_def, ngonChar_r]
  norm_num

/-- The action of `DihedralGroup n` on the `n` vertices of the regular `n`-gon: the rotation
`r i` sends the vertex `k` to `k - i`, the reflection `sr i` sends `k` to `i - k`. -/
def vertexAction : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun g := match g with
    | .r i => Equiv.subRight i
    | .sr i => (Equiv.neg (ZMod n)).trans (Equiv.addLeft i)
  map_one' := by ext k; exact sub_zero k
  map_mul' := by
    rintro (a | a) (b | b) <;> ext k <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, Equiv.Perm.mul_apply,
        Equiv.subRight_apply, Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addLeft] <;>
      ring

/-- The permutation representation of `DihedralGroup n` on the vertices of the regular `n`-gon. -/
noncomputable def vertexRep : DihedralGroup n →* Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.permMatrixHom.comp (vertexAction n)

/-- The character of the vertex permutation representation (the number of fixed vertices). -/
noncomputable def vertexChar (g : DihedralGroup n) : ℂ := Matrix.trace (vertexRep n g)

lemma vertexChar_r (k : ZMod n) : vertexChar n (r k) = if k = 0 then (n : ℂ) else 0 := by
  classical
  have h : vertexRep n (r k) = ((vertexAction n (r k))⁻¹).permMatrix ℂ := rfl
  rw [vertexChar, h, Matrix.trace]
  simp only [Matrix.diag_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  have hkey : ∀ a : ZMod n, ((vertexAction n (r k))⁻¹) a = a + k := fun _ => rfl
  simp_rw [hkey, add_eq_left]
  by_cases hk : k = 0 <;> simp [hk]

lemma vertexChar_sr (i : ZMod n) :
    vertexChar n (sr i) = ({a : ZMod n | 2 * a = i} : Finset (ZMod n)).card := by
  classical
  have h : vertexRep n (sr i) = ((vertexAction n (sr i))⁻¹).permMatrix ℂ := rfl
  rw [vertexChar, h, Matrix.trace]
  simp only [Matrix.diag_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  have hinv : (vertexAction n (sr i))⁻¹ = vertexAction n (sr i) := by
    rw [← map_inv, inv_sr]
  have hkey : ∀ a : ZMod n, ((vertexAction n (sr i))⁻¹) a = i - a := by
    intro a; rw [hinv]; exact (sub_eq_add_neg i a).symm ▸ rfl
  have hcond : ∀ a : ZMod n, (i - a = a) ↔ (2 * a = i) := by
    intro a; constructor <;> intro h' <;> linear_combination -h'
  simp_rw [hkey, hcond]
  rw [Finset.sum_boole]

/-- The standard hermitian inner product on class functions of `DihedralGroup n`. -/
noncomputable def charInner (f g : DihedralGroup n → ℂ) : ℂ :=
  ((Fintype.card (DihedralGroup n) : ℂ))⁻¹ *
    ∑ x : DihedralGroup n, f x * (starRingEnd ℂ) (g x)

lemma card_dihedral_ne_zero : ((Fintype.card (DihedralGroup n) : ℂ)) = 2 * n := by
  rw [DihedralGroup.card]
  push_cast
  ring

end Dihedral

section Computations

variable (n : ℕ) [NeZero n]

lemma conj_pair (a : ZMod n) :
    (starRingEnd ℂ) (chiN n a + chiN n (-a)) = chiN n a + chiN n (-a) := by
  rw [map_add, chiN_conj, chiN_conj, neg_neg]
  ring

/-- `⟨χⱼ, χⱼ⟩ = 1` whenever `2j ≠ 0`; equivalently `ngonRep n j` is irreducible. -/
theorem ngonChar_self_inner (j : ZMod n) (hj : 2 * j ≠ 0) :
    charInner n (ngonChar n j) (ngonChar n j) = 1 := by
  have hj' : -(2 * j) ≠ 0 := fun h => hj (by simpa using congrArg Neg.neg h)
  have hsum : ∑ x : DihedralGroup n, ngonChar n j x * (starRingEnd ℂ) (ngonChar n j x)
      = 2 * n := by
    rw [sum_dihedral]
    have hsr : ∀ k : ZMod n,
        ngonChar n j (sr k) * (starRingEnd ℂ) (ngonChar n j (sr k)) = 0 := by
      intro k; simp
    simp only [hsr, Finset.sum_const_zero, add_zero]
    have hterm : ∀ k : ZMod n,
        ngonChar n j (r k) * (starRingEnd ℂ) (ngonChar n j (r k))
          = chiN n ((2 * j) * k) + 1 + 1 + chiN n ((-(2 * j)) * k) := by
      intro k
      rw [ngonChar_r, conj_pair]
      have e1 : chiN n (j * k) * chiN n (j * k) = chiN n ((2 * j) * k) := by
        rw [← chiN_add]; ring_nf
      have e2 : chiN n (-(j * k)) * chiN n (-(j * k)) = chiN n ((-(2 * j)) * k) := by
        rw [← chiN_add]; ring_nf
      have e3 : chiN n (j * k) * chiN n (-(j * k)) = 1 := chiN_mul_neg n (j * k)
      have e4 : chiN n (-(j * k)) * chiN n (j * k) = 1 := by rw [mul_comm]; exact e3
      calc (chiN n (j * k) + chiN n (-(j * k))) * (chiN n (j * k) + chiN n (-(j * k)))
          = chiN n (j * k) * chiN n (j * k) + chiN n (j * k) * chiN n (-(j * k))
            + chiN n (-(j * k)) * chiN n (j * k)
            + chiN n (-(j * k)) * chiN n (-(j * k)) := by ring
        _ = chiN n ((2 * j) * k) + 1 + 1 + chiN n ((-(2 * j)) * k) := by
            rw [e1, e2, e3, e4]
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_chiN, sum_chiN, if_neg hj, if_neg hj']
    simp [ZMod.card]
    ring
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [charInner, hsum, card_dihedral_ne_zero]
  field_simp

/-- Distinct `j`'s (up to sign) give orthogonal characters, hence inequivalent representations. -/
theorem ngonChar_orthogonal (j l : ZMod n) (h1 : j ≠ l) (h2 : j ≠ -l) :
    charInner n (ngonChar n j) (ngonChar n l) = 0 := by
  have hjl : j - l ≠ 0 := sub_ne_zero_of_ne h1
  have hlj : l - j ≠ 0 := sub_ne_zero_of_ne (Ne.symm h1)
  have hpl : j + l ≠ 0 := by
    intro h; exact h2 (by linear_combination h)
  have hml : -j - l ≠ 0 := by
    intro h; exact h2 (by linear_combination -h)
  have hsum : ∑ x : DihedralGroup n, ngonChar n j x * (starRingEnd ℂ) (ngonChar n l x) = 0 := by
    rw [sum_dihedral]
    have hsr : ∀ k : ZMod n,
        ngonChar n j (sr k) * (starRingEnd ℂ) (ngonChar n l (sr k)) = 0 := by
      intro k; simp
    simp only [hsr, Finset.sum_const_zero, add_zero]
    have hterm : ∀ k : ZMod n,
        ngonChar n j (r k) * (starRingEnd ℂ) (ngonChar n l (r k))
          = chiN n ((j + l) * k) + chiN n ((j - l) * k)
            + chiN n ((-j - l) * k) + chiN n ((l - j) * k) := by
      intro k
      rw [ngonChar_r, ngonChar_r, conj_pair]
      have e1 : chiN n (j * k) * chiN n (l * k) = chiN n ((j + l) * k) := by
        rw [← chiN_add]; ring_nf
      have e2 : chiN n (j * k) * chiN n (-(l * k)) = chiN n ((j - l) * k) := by
        rw [← chiN_add]; ring_nf
      have e3 : chiN n (-(j * k)) * chiN n (l * k) = chiN n ((l - j) * k) := by
        rw [← chiN_add]; ring_nf
      have e4 : chiN n (-(j * k)) * chiN n (-(l * k)) = chiN n ((-j - l) * k) := by
        rw [← chiN_add]; ring_nf
      calc (chiN n (j * k) + chiN n (-(j * k))) * (chiN n (l * k) + chiN n (-(l * k)))
          = chiN n (j * k) * chiN n (l * k) + chiN n (j * k) * chiN n (-(l * k))
            + chiN n (-(j * k)) * chiN n (-(l * k))
            + chiN n (-(j * k)) * chiN n (l * k) := by ring
        _ = _ := by rw [e1, e2, e3, e4]
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_chiN, sum_chiN, sum_chiN, sum_chiN, if_neg hpl, if_neg hjl, if_neg hml, if_neg hlj]
    ring
  rw [charInner, hsum, mul_zero]

/-- **Multiplicity one.** The `j`-isotypic multiplicity of the two-dimensional representation
`ngonRep n j` inside the permutation representation on the `n` vertices of the regular `n`-gon
equals one, for every `j`. -/
theorem vertex_ngon_multiplicity_one (j : ZMod n) :
    charInner n (vertexChar n) (ngonChar n j) = 1 := by
  classical
  have hsum : ∑ x : DihedralGroup n, vertexChar n x * (starRingEnd ℂ) (ngonChar n j x)
      = 2 * n := by
    rw [sum_dihedral]
    have hsr : ∀ k : ZMod n,
        vertexChar n (sr k) * (starRingEnd ℂ) (ngonChar n j (sr k)) = 0 := by
      intro k; simp
    simp only [hsr, Finset.sum_const_zero, add_zero]
    have hterm : ∀ k : ZMod n,
        vertexChar n (r k) * (starRingEnd ℂ) (ngonChar n j (r k))
          = if k = 0 then (2 * n : ℂ) else 0 := by
      intro k
      rw [vertexChar_r]
      by_cases hk : k = 0
      · subst hk
        rw [if_pos rfl, ngonChar_r, conj_pair]
        simp
        ring
      · rw [if_neg hk, if_neg hk, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod n) (fun _ => (2 * n : ℂ))]
    simp
  rw [charInner, hsum, card_dihedral_ne_zero]
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

end Computations

section Intertwiner

/-!
## An explicit embedding of `ngonRep n j` into the vertex representation

The character computation above shows that the multiplicity is one.  Here we make the
"multiplicity at least one" half completely concrete by exhibiting an explicit injective
intertwiner: the `n x 2` discrete-Fourier matrix whose two columns are `a` mapsto `ζₙ^(j a)` and
`a` mapsto `ζₙ^(-j a)`.
-/

variable (n : ℕ) [NeZero n]

lemma vertexRep_mul_apply (g : DihedralGroup n) (M : Matrix (ZMod n) (Fin 2) ℂ)
    (a : ZMod n) (c : Fin 2) :
    (vertexRep n g * M) a c = M ((vertexAction n g).symm a) c := by
  have h : vertexRep n g = ((vertexAction n g)⁻¹).permMatrix ℂ := rfl
  rw [h, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rfl

lemma vertexRep_r_mul_apply (k : ZMod n) (M : Matrix (ZMod n) (Fin 2) ℂ)
    (a : ZMod n) (c : Fin 2) :
    (vertexRep n (r k) * M) a c = M (a + k) c := vertexRep_mul_apply n _ M a c

lemma vertexRep_sr_mul_apply (k : ZMod n) (M : Matrix (ZMod n) (Fin 2) ℂ)
    (a : ZMod n) (c : Fin 2) :
    (vertexRep n (sr k) * M) a c = M (k - a) c := by
  rw [vertexRep_mul_apply]
  have hinv : (vertexAction n (sr k))⁻¹ = vertexAction n (sr k) := by rw [← map_inv, inv_sr]
  have h2 : (vertexAction n (sr k)).symm a = k - a := by
    rw [← Equiv.Perm.inv_def, hinv]; exact (sub_eq_add_neg k a).symm
  rw [h2]

/-- The `n × 2` matrix whose columns are the two discrete-Fourier vectors
`a ↦ ζₙ^(j a)` and `a ↦ ζₙ^(-j a)`. -/
noncomputable def vertexIntertwiner (j : ZMod n) : Matrix (ZMod n) (Fin 2) ℂ :=
  Matrix.of fun a c => if c = 0 then chiN n (j * a) else chiN n (-(j * a))

/-- The matrix `vertexIntertwiner n j` really does intertwine `ngonRep n j` with the vertex
permutation representation, so it identifies `ℂ²` with a subrepresentation of `ℂ^(ZMod n)`. -/
theorem vertexIntertwiner_comm (j : ZMod n) (g : DihedralGroup n) :
    vertexRep n g * vertexIntertwiner n j = vertexIntertwiner n j * ngonRep n j g := by
  rcases g with k | k
  · ext a c
    rw [vertexRep_r_mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases c
    · simp [vertexIntertwiner, ngonRep, mul_add, chiN_add]
    · simp only [vertexIntertwiner, ngonRep, Matrix.of_apply, MonoidHom.coe_mk, OneHom.coe_mk]
      norm_num
      rw [show -(j * (a + k)) = -(j * a) + -(j * k) by ring, chiN_add]
  · ext a c
    rw [vertexRep_sr_mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases c
    · simp only [vertexIntertwiner, ngonRep, Matrix.of_apply, MonoidHom.coe_mk, OneHom.coe_mk]
      norm_num
      rw [show j * (k - a) = -(j * a) + j * k by ring, chiN_add]
    · simp only [vertexIntertwiner, ngonRep, Matrix.of_apply, MonoidHom.coe_mk, OneHom.coe_mk]
      norm_num
      rw [show -(j * (k - a)) = j * a + -(j * k) by ring, chiN_add]

lemma vertexIntertwiner_mulVec (j : ZMod n) (u : Fin 2 → ℂ) (a : ZMod n) :
    Matrix.mulVec (vertexIntertwiner n j) u a
      = chiN n (j * a) * u 0 + chiN n (-(j * a)) * u 1 := by
  simp [Matrix.mulVec, vertexIntertwiner]

lemma vertexIntertwiner_ker (j : ZMod n) (hj : 2 * j ≠ 0) (u : Fin 2 → ℂ)
    (hu : Matrix.mulVec (vertexIntertwiner n j) u = 0) : u = 0 := by
  have hj' : -(2 * j) ≠ 0 := fun h => hj (by simpa using congrArg Neg.neg h)
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h0 : (n : ℂ) * u 0 = 0 := by
    have hs : ∑ a : ZMod n,
        chiN n (-(j * a)) * (Matrix.mulVec (vertexIntertwiner n j) u a) = 0 := by
      rw [hu]; simp
    have hterm : ∀ a : ZMod n,
        chiN n (-(j * a)) * (Matrix.mulVec (vertexIntertwiner n j) u a)
          = u 0 + chiN n ((-(2 * j)) * a) * u 1 := by
      intro a
      rw [vertexIntertwiner_mulVec]
      have e1 : chiN n (-(j * a)) * chiN n (j * a) = 1 := by
        rw [mul_comm]; exact chiN_mul_neg n (j * a)
      have e2 : chiN n (-(j * a)) * chiN n (-(j * a)) = chiN n ((-(2 * j)) * a) := by
        rw [← chiN_add]; ring_nf
      calc chiN n (-(j * a)) * (chiN n (j * a) * u 0 + chiN n (-(j * a)) * u 1)
          = (chiN n (-(j * a)) * chiN n (j * a)) * u 0
            + (chiN n (-(j * a)) * chiN n (-(j * a))) * u 1 := by ring
        _ = u 0 + chiN n ((-(2 * j)) * a) * u 1 := by rw [e1, e2, one_mul]
    simp only [hterm] at hs
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_chiN, if_neg hj'] at hs
    simpa [ZMod.card] using hs
  have h1 : (n : ℂ) * u 1 = 0 := by
    have hs : ∑ a : ZMod n,
        chiN n (j * a) * (Matrix.mulVec (vertexIntertwiner n j) u a) = 0 := by
      rw [hu]; simp
    have hterm : ∀ a : ZMod n,
        chiN n (j * a) * (Matrix.mulVec (vertexIntertwiner n j) u a)
          = chiN n ((2 * j) * a) * u 0 + u 1 := by
      intro a
      rw [vertexIntertwiner_mulVec]
      have e1 : chiN n (j * a) * chiN n (-(j * a)) = 1 := chiN_mul_neg n (j * a)
      have e2 : chiN n (j * a) * chiN n (j * a) = chiN n ((2 * j) * a) := by
        rw [← chiN_add]; ring_nf
      calc chiN n (j * a) * (chiN n (j * a) * u 0 + chiN n (-(j * a)) * u 1)
          = (chiN n (j * a) * chiN n (j * a)) * u 0
            + (chiN n (j * a) * chiN n (-(j * a))) * u 1 := by ring
        _ = chiN n ((2 * j) * a) * u 0 + u 1 := by rw [e1, e2, one_mul]
    simp only [hterm] at hs
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_chiN, if_neg hj] at hs
    simpa [ZMod.card] using hs
  funext c
  fin_cases c
  · simpa using (mul_eq_zero.mp h0).resolve_left hn
  · simpa using (mul_eq_zero.mp h1).resolve_left hn

/-- The intertwiner is injective when `2 * j ≠ 0`, so `ngonRep n j` occurs as an honest
two-dimensional subrepresentation of the vertex representation. -/
theorem vertexIntertwiner_injective (j : ZMod n) (hj : 2 * j ≠ 0) :
    Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner n j) u) := by
  intro u v huv
  simp only at huv
  have hz : Matrix.mulVec (vertexIntertwiner n j) (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  exact sub_eq_zero.mp (vertexIntertwiner_ker n j hj _ hz)

end Intertwiner


/-- **Pentagon Pentagon Isotypic Higher N.**

The `D₅`-pentagon representation theory generalised to the regular `n`-gon.  For every `n ≥ 1` and
every `j, l : ZMod n`:

1. `ngonRep n j` is a genuine two-dimensional complex representation of `DihedralGroup n` with
   character value `2` at the identity;
2. its character is `ζⁿ^(jk) + ζⁿ^(-jk)` on the rotation `r k` and vanishes on every reflection;
3. it is irreducible as soon as `2 * j ≠ 0` (its character has norm one);
4. the characters for `j` and `l` are orthogonal whenever `j ≠ ±l`, so the representations are
   pairwise inequivalent;
5. the `j`-isotypic multiplicity of `ngonRep n j` inside the permutation representation of
   `DihedralGroup n` on the `n` vertices of the `n`-gon is exactly `1`;
6. concretely, the explicit discrete-Fourier matrix `vertexIntertwiner n j` intertwines the two
   representations, and it is injective when `2 * j ≠ 0`, so `ngonRep n j` really is realised as a
   two-dimensional subrepresentation of the vertex representation.
-/
theorem PentagonPentagonIsotypicHigherN (n : ℕ) [NeZero n] (j l : ZMod n) :
    ngonChar n j 1 = 2 ∧
    (∀ k : ZMod n, ngonChar n j (r k) = chiN n (j * k) + chiN n (-(j * k))) ∧
    (∀ k : ZMod n, ngonChar n j (sr k) = 0) ∧
    (2 * j ≠ 0 → charInner n (ngonChar n j) (ngonChar n j) = 1) ∧
    (j ≠ l → j ≠ -l → charInner n (ngonChar n j) (ngonChar n l) = 0) ∧
    charInner n (vertexChar n) (ngonChar n j) = 1 ∧
    (∀ g : DihedralGroup n,
      vertexRep n g * vertexIntertwiner n j = vertexIntertwiner n j * ngonRep n j g) ∧
    (2 * j ≠ 0 →
      Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner n j) u)) :=
  ⟨ngonChar_one n j, fun k => ngonChar_r n j k, fun k => ngonChar_sr n j k,
    ngonChar_self_inner n j, ngonChar_orthogonal n j l, vertex_ngon_multiplicity_one n j,
    vertexIntertwiner_comm n j, vertexIntertwiner_injective n j⟩

/-- The original pentagon (`n = 5`) statements, recovered as a special case: the two
two-dimensional representations `ρ₁`, `ρ₂` of `D₅` are irreducible, inequivalent, and each occurs
with multiplicity one in the permutation representation on the five vertices of the pentagon. -/
theorem pentagon_isotypic :
    charInner 5 (ngonChar 5 1) (ngonChar 5 1) = 1 ∧
    charInner 5 (ngonChar 5 2) (ngonChar 5 2) = 1 ∧
    charInner 5 (ngonChar 5 1) (ngonChar 5 2) = 0 ∧
    charInner 5 (vertexChar 5) (ngonChar 5 1) = 1 ∧
    charInner 5 (vertexChar 5) (ngonChar 5 2) = 1 ∧
    Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner 5 1) u) ∧
    Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner 5 2) u) :=
  ⟨ngonChar_self_inner 5 1 (by decide), ngonChar_self_inner 5 2 (by decide),
    ngonChar_orthogonal 5 1 2 (by decide) (by decide),
    vertex_ngon_multiplicity_one 5 1, vertex_ngon_multiplicity_one 5 2,
    vertexIntertwiner_injective 5 1 (by decide), vertexIntertwiner_injective 5 2 (by decide)⟩

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

