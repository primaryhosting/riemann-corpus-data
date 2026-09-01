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

/-
# The `n`-qubit Pauli group, in symplectic (efficient) form

This file sets up the algebraic infrastructure needed for the Gottesman–Knill theorem:

* computational basis states of `n` qubits are indexed by bit strings `Bits n = Fin n → ZMod 2`;
* the Pauli operator `X^x Z^z` is the explicit complex matrix `pauliMat x z`;
* `PS n` is the *symbolic* Pauli group: a phase in `ZMod 4` together with two bit strings,
  i.e. `2 * n + 2` bits of classical data;
* `rep : PS n →* Matrix (Bits n) (Bits n) ℂ` turns symbolic Paulis into matrices, and is a
  monoid homomorphism. This is what makes the classical bookkeeping faithful.
-/
import Mathlib

namespace QI

open scoped BigOperators
open Matrix

/-- Bit strings of length `n`: both computational basis labels and symplectic vectors. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

variable {n : ℕ}

/-- The `𝔽₂`-valued inner product of two bit strings. -/
def dotB (u v : Bits n) : ZMod 2 := ∑ i, u i * v i

/-- `(-1)^b` for a bit `b`. -/
def sgnB (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- The doubling homomorphism `ZMod 2 → ZMod 4`, used to record signs inside phases. -/
def toZ4 (b : ZMod 2) : ZMod 4 := if b = 0 then 0 else 2

/-- `i^k` for `k : ZMod 4`. -/
noncomputable def iPow (k : ZMod 4) : ℂ := Complex.I ^ k.val

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma sgnB_add (a b : ZMod 2) : sgnB (a + b) = sgnB a * sgnB b := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;> subst ha <;> subst hb
  · norm_num [sgnB]
  · norm_num [sgnB]
  · norm_num [sgnB]
  · rw [show ((1 : ZMod 2) + 1) = 0 from by decide]
    norm_num [sgnB]

lemma sgnB_zero : sgnB (0 : ZMod 2) = 1 := by simp [sgnB]

@[simp] lemma toZ4_zero : toZ4 (0 : ZMod 2) = 0 := rfl

lemma toZ4_add (a b : ZMod 2) : toZ4 (a + b) = toZ4 a + toZ4 b := by
  revert a b; decide +kernel

lemma iPow_zero : iPow (0 : ZMod 4) = 1 := by simp [iPow]

lemma iPow_add (k l : ZMod 4) : iPow (k + l) = iPow k * iPow l := by
  have h : ∀ m : ZMod 4, m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by decide +kernel
  rcases h k with hk | hk | hk | hk <;> rcases h l with hl | hl | hl | hl <;>
    subst hk <;> subst hl <;>
    simp [iPow, ZMod.val, pow_succ, Complex.I_mul_I] <;> ring_nf <;>
    simp [Complex.I_mul_I] <;> ring

lemma iPow_toZ4 (b : ZMod 2) : iPow (toZ4 b) = sgnB b := by
  rcases zmod2_cases b with hb | hb <;> subst hb <;>
    simp [iPow, toZ4, sgnB, ZMod.val, Complex.I_mul_I] <;>
    norm_num [pow_succ, Complex.I_mul_I]

/-! ### Bilinearity of the symplectic form -/

lemma dotB_zero_left (v : Bits n) : dotB 0 v = 0 := by simp [dotB]

lemma dotB_zero_right (u : Bits n) : dotB u 0 = 0 := by simp [dotB]

lemma dotB_add_left (u v w : Bits n) : dotB (u + v) w = dotB u w + dotB v w := by
  simp [dotB, add_mul, Finset.sum_add_distrib]

lemma dotB_add_right (u v w : Bits n) : dotB u (v + w) = dotB u v + dotB u w := by
  simp [dotB, mul_add, Finset.sum_add_distrib]

/-! ### Pauli matrices -/

/-- The matrix of the Pauli operator `X^x Z^z` acting on the computational basis:
`(X^x Z^z) |a⟩ = (-1)^{z·a} |a + x⟩`. -/
def pauliMat (x z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun b a => if b = a + x then sgnB (dotB z a) else 0

lemma pauliMat_apply (x z : Bits n) (b a : Bits n) :
    pauliMat x z b a = if b = a + x then sgnB (dotB z a) else 0 := rfl

lemma pauliMat_zero_zero : pauliMat (0 : Bits n) 0 = 1 := by
  ext b a
  by_cases h : b = a <;>
    simp [pauliMat, Matrix.one_apply, h, dotB_zero_left, sgnB_zero, eq_comm]

/-- The multiplication rule of Pauli operators. -/
lemma pauliMat_mul (x z x' z' : Bits n) :
    pauliMat x z * pauliMat x' z' = sgnB (dotB z x') • pauliMat (x + x') (z + z') := by
  ext b a
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (a + x')]
  · by_cases h : b = a + x' + x
    · have h3 : a + x' + x = a + (x + x') := by ring
      rw [pauliMat_apply, pauliMat_apply, Matrix.smul_apply, pauliMat_apply, smul_eq_mul,
        if_pos h, if_pos rfl, if_pos (h.trans h3)]
      rw [dotB_add_right, dotB_add_left, sgnB_add, sgnB_add]
      ring
    · have h2 : ¬ b = a + (x + x') := by
        intro hc; exact h (by rw [hc]; ring)
      simp [pauliMat_apply, h, h2]
  · intro c _ hc
    simp [pauliMat_apply, hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The symbolic Pauli group `PS n` -/

/-- A symbolic Pauli operator: the phase exponent `ph` (a power of `i`) together with the
`X`-part `x` and the `Z`-part `z`.  This is exactly `2 * n + 2` bits of classical data. -/
@[ext]
structure PS (n : ℕ) where
  ph : ZMod 4
  x : Bits n
  z : Bits n

namespace PS

instance : Mul (PS n) :=
  ⟨fun p q => ⟨p.ph + q.ph + toZ4 (dotB p.z q.x), p.x + q.x, p.z + q.z⟩⟩

instance : One (PS n) := ⟨⟨0, 0, 0⟩⟩

@[simp] lemma mul_ph (p q : PS n) : (p * q).ph = p.ph + q.ph + toZ4 (dotB p.z q.x) := rfl
@[simp] lemma mul_x (p q : PS n) : (p * q).x = p.x + q.x := rfl
@[simp] lemma mul_z (p q : PS n) : (p * q).z = p.z + q.z := rfl
@[simp] lemma one_ph : (1 : PS n).ph = 0 := rfl
@[simp] lemma one_x : (1 : PS n).x = 0 := rfl
@[simp] lemma one_z : (1 : PS n).z = 0 := rfl

instance : Monoid (PS n) where
  mul_assoc p q r := by
    ext
    · simp only [mul_ph, mul_x, mul_z, dotB_add_left, dotB_add_right, toZ4_add]
      ring
    · simp [add_assoc]
    · simp [add_assoc]
  one_mul p := by ext <;> simp [dotB_zero_left]
  mul_one p := by ext <;> simp [dotB_zero_right]

end PS

/-- The matrix representation of a symbolic Pauli. -/
noncomputable def rep (p : PS n) : Matrix (Bits n) (Bits n) ℂ :=
  iPow p.ph • pauliMat p.x p.z

lemma rep_one : rep (1 : PS n) = 1 := by
  simp [rep, iPow_zero, pauliMat_zero_zero]

lemma rep_mul (p q : PS n) : rep (p * q) = rep p * rep q := by
  simp only [rep, PS.mul_ph, PS.mul_x, PS.mul_z, Matrix.smul_mul, Matrix.mul_smul,
    pauliMat_mul, iPow_add, iPow_toZ4, smul_smul]
  ring_nf

/-- `rep` as a monoid homomorphism from the symbolic Pauli group to matrices. -/
noncomputable def repHom : PS n →* Matrix (Bits n) (Bits n) ℂ where
  toFun := rep
  map_one' := rep_one
  map_mul' := rep_mul

@[simp] lemma repHom_apply (p : PS n) : (repHom p : Matrix (Bits n) (Bits n) ℂ) = rep p := rfl

/-! ### Generators -/

/-- The `i`-th standard basis bit string. -/
def eB (i : Fin n) : Bits n := Pi.single i 1

/-- The symbolic Pauli `X_i`. -/
def gX (i : Fin n) : PS n := ⟨0, eB i, 0⟩

/-- The symbolic Pauli `Z_i`. -/
def gZ (i : Fin n) : PS n := ⟨0, 0, eB i⟩

lemma dotB_eB (z : Bits n) (i : Fin n) : dotB z (eB i) = z i := by
  simp [dotB, eB, Pi.single_apply, Finset.sum_ite_eq']

lemma dotB_eB_left (i : Fin n) (z : Bits n) : dotB (eB i) z = z i := by
  simp [dotB, eB, Pi.single_apply, Finset.sum_ite_eq']

end QI

/-
# Clifford gates and the tableau (symplectic) description of their action

A Clifford gate is a unitary `U` that conjugates every Pauli operator to a Pauli operator.
Since the Pauli group is generated by `X_1, …, X_n, Z_1, …, Z_n`, such a gate is completely
described by the `2 * n` symbolic Paulis `imX j`, `imZ j` — the classical *tableau* of the gate,
which is only `2 * n * (2 * n + 2)` bits of data.

The main result of this file, `Clifford.conj_rep`, shows that this finite data determines the
conjugation action on *every* Pauli, via the explicit classical computation `conjPS`.
-/
import RequestProject.QI.Pauli

namespace QI

open scoped BigOperators
open Matrix

variable {n : ℕ}

/-- A Clifford gate on `n` qubits, together with its tableau: the images of the generators
`X_j` and `Z_j` under conjugation. -/
structure Clifford (n : ℕ) where
  /-- The unitary matrix implementing the gate. -/
  U : Matrix (Bits n) (Bits n) ℂ
  /-- The gate is unitary. -/
  unitary : U * Uᴴ = 1
  /-- Tableau: the image of `X_j` under conjugation by `U`. -/
  imX : Fin n → PS n
  /-- Tableau: the image of `Z_j` under conjugation by `U`. -/
  imZ : Fin n → PS n
  /-- `U X_j U⁻¹ = imX j`. -/
  conjX : ∀ j, U * rep (gX j) = rep (imX j) * U
  /-- `U Z_j U⁻¹ = imZ j`. -/
  conjZ : ∀ j, U * rep (gZ j) = rep (imZ j) * U

/-- Ordered product of the images of the generators selected by the bit string `b`. -/
def genProd (f : Fin n → PS n) (b : Bits n) : PS n :=
  ((List.finRange n).map (fun j => if b j = 1 then f j else 1)).prod

/-- The conjugate of a symbolic Pauli `p` by a Clifford gate, computed from the tableau. -/
def conjPS (C : Clifford n) (p : PS n) : PS n :=
  (⟨p.ph, 0, 0⟩ : PS n) * genProd C.imX p.x * genProd C.imZ p.z

lemma rep_phase (k : ZMod 4) : rep (⟨k, 0, 0⟩ : PS n) = iPow k • (1 : Matrix (Bits n) (Bits n) ℂ) := by
  simp [rep, pauliMat_zero_zero]

lemma phase_comm (k : ZMod 4) (M : Matrix (Bits n) (Bits n) ℂ) :
    M * rep (⟨k, 0, 0⟩ : PS n) = rep (⟨k, 0, 0⟩ : PS n) * M := by
  simp [rep_phase, Matrix.mul_smul, Matrix.smul_mul]

/-! ### The generator products compute the Pauli they should -/

private lemma prod_gX_list (l : List (Fin n)) (b : Bits n) :
    ((l.map (fun j => if b j = 1 then gX j else 1)).prod)
      = ⟨0, (l.map (fun j => if b j = 1 then eB j else 0)).sum, 0⟩ := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
    by_cases hb : b j = 1 <;> · ext <;> simp [hb, gX, dotB_zero_left]

private lemma prod_gZ_list (l : List (Fin n)) (b : Bits n) :
    ((l.map (fun j => if b j = 1 then gZ j else 1)).prod)
      = ⟨0, 0, (l.map (fun j => if b j = 1 then eB j else 0)).sum⟩ := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
    by_cases hb : b j = 1 <;> · ext <;> simp [hb, gZ, dotB_zero_right]

private lemma sum_single_eq (b : Bits n) :
    ((List.finRange n).map (fun j => if b j = 1 then eB j else 0)).sum = b := by
  rw [← Fin.sum_univ_def]
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rcases zmod2_cases (b k) with h | h <;> simp [h, eB, Pi.single_apply]
  · intro j _ hj
    by_cases hb : b j = 1 <;> simp [hb, eB, Pi.single_eq_of_ne (Ne.symm hj)]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] lemma genProd_gX (b : Bits n) : genProd gX b = ⟨0, b, 0⟩ := by
  rw [genProd, prod_gX_list, sum_single_eq]

@[simp] lemma genProd_gZ (b : Bits n) : genProd gZ b = ⟨0, 0, b⟩ := by
  rw [genProd, prod_gZ_list, sum_single_eq]

/-- Every symbolic Pauli factors as a phase times a product of `X` generators times a product
of `Z` generators. -/
lemma ps_factor (p : PS n) :
    p = (⟨p.ph, 0, 0⟩ : PS n) * genProd gX p.x * genProd gZ p.z := by
  ext <;> simp [dotB_zero_left, dotB_zero_right]

/-! ### Conjugation of an arbitrary Pauli is computed by the tableau -/

private lemma conj_gen_list (M : Matrix (Bits n) (Bits n) ℂ) (F G : Fin n → PS n)
    (h : ∀ j, M * rep (F j) = rep (G j) * M) (l : List (Fin n)) (b : Bits n) :
    M * rep ((l.map (fun j => if b j = 1 then F j else 1)).prod)
      = rep ((l.map (fun j => if b j = 1 then G j else 1)).prod) * M := by
  induction l with
  | nil => simp [rep_one]
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, rep_mul]
    have hj : M * rep (if b j = 1 then F j else 1) = rep (if b j = 1 then G j else 1) * M := by
      by_cases hb : b j = 1
      · simpa [hb] using h j
      · simp [hb, rep_one]
    rw [← Matrix.mul_assoc, hj, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

lemma conj_genProd (C : Clifford n) (b : Bits n) :
    C.U * rep (genProd gX b) = rep (genProd C.imX b) * C.U :=
  conj_gen_list C.U gX C.imX C.conjX _ b

lemma conj_genProdZ (C : Clifford n) (b : Bits n) :
    C.U * rep (genProd gZ b) = rep (genProd C.imZ b) * C.U :=
  conj_gen_list C.U gZ C.imZ C.conjZ _ b

/-- **The tableau determines the conjugation action.**  For every Pauli `p`,
`U (rep p) = (rep (conjPS C p)) U`, where `conjPS` is a purely classical computation on the
`2n(2n+2)`-bit tableau of the gate. -/
theorem Clifford.conj_rep (C : Clifford n) (p : PS n) :
    C.U * rep p = rep (conjPS C p) * C.U := by
  have hX := conj_genProd C p.x
  have hZ := conj_genProdZ C p.z
  conv_lhs => rw [ps_factor p]
  simp only [conjPS, rep_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, phase_comm, Matrix.mul_assoc, ← Matrix.mul_assoc C.U, hX,
    Matrix.mul_assoc, hZ]

end QI

