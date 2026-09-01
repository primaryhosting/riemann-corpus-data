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

namespace QI

open Matrix
open scoped ComplexOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`.
It is the block matrix `∑ i j, Eᵢⱼ ⊗ Φ Eᵢⱼ`, written entrywise as
`choiMatrix Φ (i, a) (j, b) = Φ (single i j 1) a b`. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- A linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ` is *completely positive* if for every
finite index type `k` the amplified map
`Φ ⊗ id : Matrix (n × k) (n × k) ℂ → Matrix (m × k) (m × k) ℂ`
maps positive semidefinite matrices to positive semidefinite matrices.  The amplification is
written out entrywise: the `k`-blocks of the argument are the matrices `i j ↦ A (i, s) (j, t)`. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] [DecidableEq k] (A : Matrix (n × k) (n × k) ℂ), A.PosSemidef →
    (Matrix.of fun p q : m × k => Φ (Matrix.of fun i j => A (i, p.2) (j, q.2)) p.1 q.1).PosSemidef

omit [Fintype m] [DecidableEq m] in
/-- A linear map on matrices is determined by its values on the matrix units. -/
lemma apply_entry_eq_sum (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ) (a b : m) :
    Φ X a b = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  have h : ∀ i j : n, Matrix.single i j (X i j) = X i j • Matrix.single (α := ℂ) i j 1 := by
    intro i j
    ext p q
    simp [Matrix.single_apply]
  simp only [h, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq n] [DecidableEq m] in
/-- A map given by a Kraus decomposition `Φ X = ∑ s, K s * X * (K s)ᴴ` is completely positive. -/
lemma isCompletelyPositive_of_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {r : Type} [Fintype r] (K : r → Matrix m n ℂ)
    (hK : ∀ X : Matrix n n ℂ, Φ X = ∑ s, K s * X * (K s)ᴴ) : IsCompletelyPositive Φ := by
  intro k _ _ A hA
  set M : r → Matrix (m × k) (n × k) ℂ :=
    fun s => Matrix.of fun p q => if p.2 = q.2 then K s p.1 q.1 else 0 with hMdef
  have key : (Matrix.of fun p q : m × k => Φ (Matrix.of fun i j => A (i, p.2) (j, q.2)) p.1 q.1)
      = ∑ s, M s * A * (M s)ᴴ := by
    ext p q
    obtain ⟨a, s0⟩ := p
    obtain ⟨b, t0⟩ := q
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, hK, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hMdef, Matrix.of_apply,
      Fintype.sum_prod_type, ite_mul, zero_mul, apply_ite (star : ℂ → ℂ), star_zero, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]
  exact Finset.sum_induction _ _ (fun x y hx hy => hx.add hy) Matrix.PosSemidef.zero
    (fun s _ => hA.mul_mul_conjTranspose_same (M s))

omit [DecidableEq m] in
/-- If the Choi matrix of `Φ` is positive semidefinite, then `Φ` admits a Kraus decomposition. -/
lemma exists_kraus_of_choiMatrix_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) :
    ∃ (N : ℕ) (K : Fin N → Matrix m n ℂ), ∀ X : Matrix n n ℂ, Φ X = ∑ s, K s * X * (K s)ᴴ := by
  obtain ⟨N, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp h
  refine ⟨N, fun s => Matrix.of fun a i => v s (i, a), fun X => ?_⟩
  ext a b
  have hentry : ∀ i j : n, Φ (Matrix.single i j 1) a b
      = ∑ s : Fin N, v s (i, a) * star (v s (j, b)) := by
    intro i j
    have h2 := congrArg (fun M => M (i, a) (j, b)) hv
    simpa only [choiMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply] using h2
  have hRHS : ∀ s : Fin N, ((Matrix.of fun a i => v s (i, a) : Matrix m n ℂ) * X *
        (Matrix.of fun a i => v s (i, a) : Matrix m n ℂ)ᴴ) a b
      = ∑ i, ∑ j, X i j * (v s (i, a) * star (v s (j, b))) := by
    intro s
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hswap : ∑ s : Fin N, ∑ i, ∑ j, X i j * (v s (i, a) * star (v s (j, b)))
      = ∑ i, ∑ j, ∑ s : Fin N, X i j * (v s (i, a) * star (v s (j, b))) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [apply_entry_eq_sum Φ X a b, Matrix.sum_apply]
  simp only [hRHS]
  rw [hswap]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hentry i j, Finset.mul_sum]

/-- The (unnormalized) maximally entangled state `|ω⟩⟨ω|`, `ω = ∑ i, eᵢ ⊗ eᵢ`, is positive
semidefinite. -/
lemma posSemidef_maxEntangled :
    (Matrix.of fun p q : n × n => (if p.1 = p.2 then (1 : ℂ) else 0) *
      (if q.1 = q.2 then (1 : ℂ) else 0)).PosSemidef := by
  have h : (Matrix.of fun p q : n × n => (if p.1 = p.2 then (1 : ℂ) else 0) *
      (if q.1 = q.2 then (1 : ℂ) else 0))
      = (Matrix.of fun (p : n × n) (_ : Unit) => (if p.1 = p.2 then (1 : ℂ) else 0)) *
        (Matrix.of fun (p : n × n) (_ : Unit) => (if p.1 = p.2 then (1 : ℂ) else 0))ᴴ := by
    ext p q
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

omit [DecidableEq m] in
/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · intro hCP
    have h := hCP n _ posSemidef_maxEntangled
    have hEq : choiMatrix Φ =
        (Matrix.of fun p q : m × n => Φ (Matrix.of fun i j =>
          (if i = p.2 then (1 : ℂ) else 0) * (if j = q.2 then (1 : ℂ) else 0)) p.1 q.1).submatrix
          Prod.swap Prod.swap := by
      ext p q
      have hsingle : ∀ s t : n, (Matrix.of fun i j : n =>
          (if i = s then (1 : ℂ) else 0) * (if j = t then (1 : ℂ) else 0))
          = Matrix.single s t 1 := by
        intro s t
        ext i j
        simp only [Matrix.of_apply, Matrix.single_apply, ite_and]
        by_cases hi : i = s
        · by_cases hj : j = t
          · simp [hi, hj]
          · simp [hi, hj, Ne.symm hj]
        · by_cases hj : j = t <;> simp [hi, hj, Ne.symm hi]
      simp only [choiMatrix, Matrix.submatrix_apply, Matrix.of_apply,
        Prod.fst_swap, Prod.snd_swap, hsingle]
    rw [hEq]
    exact h.submatrix _
  · intro h
    obtain ⟨N, K, hK⟩ := exists_kraus_of_choiMatrix_posSemidef Φ h
    exact isCompletelyPositive_of_kraus Φ K hK

end QI

#print axioms QI.choi_jamiolkowski

