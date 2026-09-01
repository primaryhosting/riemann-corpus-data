import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open Matrix

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

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_p ⊗ Φ` of a linear map `Φ` between matrix algebras:
a `(p × n)`-matrix is viewed as a `p × p` block matrix of `n × n` blocks, and `Φ`
is applied to each block. -/
def amplify (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (p : Type) [Fintype p]
    (A : Matrix (p × n) (p × n) ℂ) : Matrix (p × m) (p × m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.of fun i j => A (x.1, i) (y.1, j)) x.2 y.2

/-- `Φ` is completely positive when all its amplifications `id_p ⊗ Φ` map positive
semidefinite matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (p : Type) [Fintype p] [DecidableEq p] (A : Matrix (p × n) (p × n) ℂ),
    A.PosSemidef → (amplify Φ p A).PosSemidef

/-- The Choi matrix of `Φ`: the block matrix whose `(i, j)` block is `Φ (E i j)`, where
`E i j` is the matrix unit. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.single x.1 y.1 1) x.2 y.2

omit [Fintype m] [DecidableEq m] in
/-- Entries of `Φ X` in terms of the Choi matrix. -/
lemma apply_entry_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (X : Matrix n n ℂ) (k l : m) :
    Φ X k l = ∑ i : n, ∑ j : n, X i j * choiMatrix Φ (i, k) (j, l) := by
  have hsingle : ∀ i j : n, Φ (Matrix.single i j (X i j)) k l
      = X i j * choiMatrix Φ (i, k) (j, l) := by
    intro i j
    rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by simp, map_smul]
    simp [choiMatrix, Matrix.of_apply, smul_eq_mul]
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply, hsingle]

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus representation is completely positive. -/
lemma isCompletelyPositive_of_kraus {ι : Type} [Fintype ι]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (V : ι → Matrix m n ℂ)
    (hV : ∀ X : Matrix n n ℂ, Φ X = ∑ s : ι, V s * X * (V s)ᴴ) :
    IsCompletelyPositive Φ := by
  intro p _ _ A hA
  classical
  set W : ι → Matrix (p × m) (p × n) ℂ :=
    fun s => Matrix.of fun x y => if x.1 = y.1 then V s x.2 y.2 else 0 with hW
  have key : amplify Φ p A = ∑ s : ι, W s * A * (W s)ᴴ := by
    ext x y
    simp only [amplify, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : ∀ v : p × n, ∑ u : p × n, W s x u * A u v
        = ∑ i : n, V s x.2 i * A (x.1, i) v := by
      intro v
      rw [Fintype.sum_prod_type]
      simp only [hW, Matrix.of_apply, ite_mul, zero_mul]
      rw [Finset.sum_eq_single x.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · intro hc
        exact absurd (Finset.mem_univ x.1) hc
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, e1]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single y.1]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hW, Matrix.of_apply]
      rfl
    · intro d _ hd
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hW, Ne.symm hd]
    · intro hd
      exact absurd (Finset.mem_univ y.1) hd
  rw [key]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro s _
  exact hA.mul_mul_conjTranspose_same (W s)

open scoped MatrixOrder in
/-- Key intermediate step: if the Choi matrix of `Φ` is positive semidefinite, then `Φ`
admits a Kraus representation `Φ X = ∑ s, V s * X * (V s)ᴴ`. -/
lemma exists_kraus_of_choiMatrix_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) :
    ∃ V : (n × m) → Matrix m n ℂ, ∀ X : Matrix n n ℂ, Φ X = ∑ s, V s * X * (V s)ᴴ := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (n × m) (n × m) ℂ, choiMatrix Φ = Bᴴ * B :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr h)
  refine ⟨fun s => Matrix.of fun k i => star (B s (i, k)), fun X => ?_⟩
  ext k l
  rw [apply_entry_eq_sum_choi Φ X k l, hB]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_star, Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ i : n, ∑ j : n, ∑ s : n × m, X i j * (star (B s (i, k)) * B s (j, l))
      = ∑ s : n × m, ∑ j : n, X i j * (star (B s (i, k)) * B s (j, l)) :=
    fun i => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix is the image, under the amplification `id_n ⊗ Φ`, of the (unnormalized)
maximally entangled state. -/
lemma choiMatrix_posSemidef_of_isCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  set w : (n × n) → ℂ := fun x => if x.1 = x.2 then (1 : ℂ) else 0 with hw
  set Ω : Matrix (n × n) (n × n) ℂ := Matrix.of fun x y => w x * w y with hΩdef
  have hΩ : Ω.PosSemidef := by
    have hfac : Ω = (Matrix.of fun (_ : Unit) (x : n × n) => w x)ᴴ *
        (Matrix.of fun (_ : Unit) (x : n × n) => w x) := by
      ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_singleton, hΩdef]
      have : star (w x) = w x := by
        simp only [hw]
        split <;> simp
      rw [this]
    rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hEq : amplify Φ n Ω = choiMatrix Φ := by
    ext x y
    have hblock : (Matrix.of fun i j => Ω (x.1, i) (y.1, j)) = Matrix.single x.1 y.1 (1 : ℂ) := by
      ext i j
      simp only [Matrix.of_apply, hΩdef, hw, Matrix.single]
      by_cases hi : x.1 = i <;> by_cases hj : y.1 = j <;> simp [hi, hj]
    simp only [amplify, choiMatrix, Matrix.of_apply, hblock]
  exact hEq ▸ h n Ω hΩ

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  refine ⟨choiMatrix_posSemidef_of_isCompletelyPositive Φ, fun h => ?_⟩
  obtain ⟨V, hV⟩ := exists_kraus_of_choiMatrix_posSemidef Φ h
  exact isCompletelyPositive_of_kraus Φ V hV

end QI

