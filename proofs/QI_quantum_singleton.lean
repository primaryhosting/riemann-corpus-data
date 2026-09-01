/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The **quantum Singleton bound** (Knill–Laflamme bound) states that an `[[n, k, d]]`
quantum error-correcting code satisfies `n - k ≥ 2 (d - 1)`.

This file formalises the bound for **stabilizer codes** in the standard symplectic
(`GF(q)`-linear) representation, which is the combinatorial model in which the
statement is usually verified.

A stabilizer code of length `n` over a finite field `F` is encoded by:

* a subspace `S ⊆ (F × F)^n` (the *stabilizer*, written additively in the symplectic
  picture, where the pair `(a, b)` at coordinate `i` records the `X`-part and the
  `Z`-part of a Pauli operator on the `i`-th qudit),
* which is **isotropic** for the symplectic form
  `ω(u, v) = ∑ i, (u i).1 * (v i).2 - (u i).2 * (v i).1`
  (this is exactly the statement that the corresponding Pauli operators commute),
* with `dim S = n - k`, so that the joint eigenspace (the code space) has
  dimension `q ^ k`.

The *normalizer* of the code is the symplectic dual `D = S^⊥`, of dimension `n + k`,
and the **distance** `d` of the code is the minimum Hamming weight of a nonzero
element of `D` (this is the distance of a *pure*, i.e. non-degenerate, code; a
degenerate code takes the minimum over `D \ S` instead).  Here `d` is required to be
*exactly* the minimum weight: it is a lower bound for all nonzero elements of `D`
(`dist_le`) and it is attained (`dist_attained`).

The proof is the symplectic Singleton argument: deleting the first `d - 1`
coordinates is injective on `D`, because a nonzero element of `D` supported on
`d - 1` coordinates would have weight `< d`.  Hence
`n + k = dim D ≤ 2 (n - (d - 1))`, which is the bound.
-/

namespace QI

open Finset

/-! ### The symplectic form on the Pauli space `(F × F)^n` -/

/-- The symplectic form on the space `(F × F)^n` of Pauli errors:
`ω(u, v) = ∑ i, (u i).1 * (v i).2 - (u i).2 * (v i).1`.
Two Pauli operators commute exactly when this form vanishes on their symplectic
representatives. -/
noncomputable def sympForm (F : Type*) [Field F] (n : ℕ) :
    LinearMap.BilinForm F (Fin n → F × F) :=
  LinearMap.mk₂ F (fun u v => ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1))
    (by intro x y z; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by
          simp [Pi.add_apply]; ring)
    (by intro a x y
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
    (by intro x y z; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by
          simp [Pi.add_apply]; ring)
    (by intro a x y
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)

@[simp] lemma sympForm_apply {F : Type*} [Field F] {n : ℕ} (u v : Fin n → F × F) :
    sympForm F n u v = ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1) := rfl

lemma sympForm_antisymm {F : Type*} [Field F] {n : ℕ} (u v : Fin n → F × F) :
    sympForm F n u v = - sympForm F n v u := by
  simp only [sympForm_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sympForm_isRefl (F : Type*) [Field F] (n : ℕ) : (sympForm F n).IsRefl := by
  intro u v h
  rw [sympForm_antisymm, h, neg_zero]

lemma sympForm_separating {F : Type*} [Field F] {n : ℕ} (u : Fin n → F × F)
    (hu : ∀ v, sympForm F n u v = 0) : u = 0 := by
  funext i
  have h1 := hu (Pi.single i (0, 1))
  have h2 := hu (Pi.single i (1, 0))
  simp only [sympForm_apply] at h1 h2
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)] at h1 h2
  simp at h1 h2
  exact Prod.ext h1 h2

lemma sympForm_nondegenerate (F : Type*) [Field F] (n : ℕ) : (sympForm F n).Nondegenerate :=
  ⟨fun _ hu => sympForm_separating _ hu,
   fun v hv => sympForm_separating v fun u => sympForm_isRefl F n u v (hv u)⟩

/-! ### The Singleton bound for a subspace of `(F × F)^n` -/

/-- **Singleton bound** over the alphabet `F × F`: a subspace of `(F × F)^n` all of whose
nonzero elements have Hamming weight at least `d` has dimension at most
`2 * (n - (d - 1))`.  The proof deletes the first `d - 1` coordinates; the resulting
restriction map is injective on the subspace. -/
lemma finrank_le_of_minimum_weight {F : Type*} [Field F] [DecidableEq F] {n d : ℕ}
    (D : Submodule F (Fin n → F × F))
    (hd : ∀ v ∈ D, v ≠ 0 → d ≤ hammingNorm v) :
    Module.finrank F D ≤ 2 * (n - (d - 1)) := by
  set m := d - 1 with hm
  set emb : Fin (n - m) → Fin n := fun j => ⟨j + m, by omega⟩ with hemb
  have hinj : Function.Injective (((LinearMap.funLeft F (F × F) emb)).comp D.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨v, hv⟩ hker
    have hz : ∀ j : Fin (n - m), v (emb j) = 0 := by
      intro j
      have := congrFun (LinearMap.mem_ker.mp hker) j
      simpa [LinearMap.funLeft_apply] using this
    have hvz : ∀ i : Fin n, m ≤ (i : ℕ) → v i = 0 := by
      intro i hi
      have hlt : (i : ℕ) - m < n - m := by omega
      have := hz ⟨(i : ℕ) - m, hlt⟩
      simpa [hemb, Fin.ext_iff, Nat.sub_add_cancel hi] using this
    have hsub : (univ.filter (fun i : Fin n => v i ≠ 0)) ⊆
        univ.filter (fun i : Fin n => (i : ℕ) < m) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_contra h
      exact hi (hvz i (by omega))
    have hcard : (univ.filter (fun i : Fin n => (i : ℕ) < m)).card ≤ m := by
      have h := Finset.card_le_card_of_injOn (s := univ.filter (fun i : Fin n => (i : ℕ) < m))
        (t := Finset.range m) (fun i => (i : ℕ))
        (by intro i hi; simp_all)
        (by intro a _ b _ h; exact Fin.ext h)
      simpa using h
    have hw : hammingNorm v ≤ m := le_trans (Finset.card_le_card hsub) hcard
    have hv0 : v = 0 := by
      by_contra hne
      have hdv := hd v hv hne
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · rw [h0] at hm
        rw [hm] at hw
        exact hne (hammingNorm_eq_zero.mp (Nat.le_zero.mp (by simpa using hw)))
      · omega
    exact (Submodule.mem_bot F).mpr (Subtype.ext hv0)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank F (Fin (n - m) → F × F) = 2 * (n - m) := by
    simp [Module.finrank_pi_fintype]; ring
  rw [h2] at h1
  exact h1

/-! ### Stabilizer codes -/

/-- An `[[n, k, d]]` **stabilizer code** over the finite field `F`, in the symplectic
representation.

* `S` is the stabilizer, a subspace of the Pauli space `(F × F)^n` of dimension `n - k`,
* `isotropic` says that the corresponding Pauli operators pairwise commute,
* the normalizer is the symplectic dual `D = S^⊥`, and the fields `dist_le` and
  `dist_attained` say that `d` is exactly the minimum Hamming weight of a nonzero
  element of `D`, i.e. the code is a pure code of distance `d`. -/
structure StabilizerCode (F : Type*) [Field F] [DecidableEq F] (n k d : ℕ) where
  /-- The stabilizer subspace, in symplectic (`X`-part, `Z`-part) coordinates. -/
  S : Submodule F (Fin n → F × F)
  /-- The stabilizer has `n - k` independent generators. -/
  dim_S : Module.finrank F S = n - k
  /-- The number of encoded qudits is at most the number of physical qudits. -/
  k_le_n : k ≤ n
  /-- The stabilizer is isotropic: its Pauli operators commute pairwise. -/
  isotropic : ∀ u ∈ S, ∀ v ∈ S, sympForm F n u v = 0
  /-- Every nonzero element of the normalizer `S^⊥` has weight at least `d`. -/
  dist_le : ∀ v ∈ (sympForm F n).orthogonal S, v ≠ 0 → d ≤ hammingNorm v
  /-- The distance `d` is attained by some nonzero element of the normalizer. -/
  dist_attained : ∃ v ∈ (sympForm F n).orthogonal S, v ≠ 0 ∧ hammingNorm v = d

variable {F : Type*} [Field F] [DecidableEq F] {n k d : ℕ}

/-- The normalizer `S^⊥` of an `[[n, k, d]]` stabilizer code has dimension `n + k`. -/
lemma StabilizerCode.finrank_normalizer (C : StabilizerCode F n k d) :
    Module.finrank F ((sympForm F n).orthogonal C.S) = n + k := by
  have h := LinearMap.BilinForm.finrank_orthogonal (sympForm_nondegenerate F n)
    (sympForm_isRefl F n) C.S
  have htot : Module.finrank F (Fin n → F × F) = 2 * n := by
    simp [Module.finrank_pi_fintype]; ring
  rw [htot, C.dim_S] at h
  have := C.k_le_n
  omega

/-- The distance of an `[[n, k, d]]` stabilizer code is at most its length. -/
lemma StabilizerCode.dist_le_length (C : StabilizerCode F n k d) : d ≤ n := by
  obtain ⟨v, _, _, hvw⟩ := C.dist_attained
  have : hammingNorm v ≤ Fintype.card (Fin n) := hammingNorm_le_card_fintype
  simpa [hvw] using this

/-- **Quantum Singleton bound** (Knill–Laflamme bound):
an `[[n, k, d]]` quantum code satisfies `n - k ≥ 2 (d - 1)`.

Formalised for stabilizer codes in the symplectic representation, with the distance
of the (pure) code being the minimum weight of the normalizer `S^⊥`; see the header
of this file for the precise dictionary. -/
theorem quantum_singleton (C : StabilizerCode F n k d) : 2 * (d - 1) ≤ n - k := by
  have hdim := C.finrank_normalizer
  have hbound := finrank_le_of_minimum_weight ((sympForm F n).orthogonal C.S) C.dist_le
  rw [hdim] at hbound
  have hdn := C.dist_le_length
  have hkn := C.k_le_n
  omega

/-! ### Non-vacuity: the trivial `[[n, n, 1]]` code -/

/-- The trivial stabilizer code with no stabilizer generators: it encodes `n` qudits into
`n` qudits with distance `1`.  This witnesses that `StabilizerCode` is inhabited, so the
quantum Singleton bound above is not vacuous. -/
def trivialCode (F : Type*) [Field F] [DecidableEq F] (n : ℕ) (hn : 0 < n) :
    StabilizerCode F n n 1 where
  S := ⊥
  dim_S := by simp
  k_le_n := le_rfl
  isotropic := by
    intro u hu v _
    rw [Submodule.mem_bot] at hu
    simp [hu]
  dist_le := by
    intro v _ hv
    exact Nat.one_le_iff_ne_zero.mpr fun h => hv (hammingNorm_eq_zero.mp h)
  dist_attained := by
    refine ⟨(Pi.single (⟨0, hn⟩ : Fin n) (1, 0) : Fin n → F × F), ?_, ?_, ?_⟩
    · have h : (sympForm F n).orthogonal ⊥ = ⊤ := by ext w; simp
      simp [h]
    · intro h
      have hc := congrFun h ⟨0, hn⟩
      simp at hc
    · simp [hammingNorm, Pi.single_apply, Finset.filter_eq']

end QI

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

