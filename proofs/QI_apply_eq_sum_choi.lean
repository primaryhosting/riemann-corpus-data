import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C(Φ) (i, α) (j, β) = Φ (Eᵢⱼ) α β`, where `Eᵢⱼ` is the matrix unit. -/
def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The ampliation `idₖ ⊗ Φ` of `Φ`, described blockwise: a matrix indexed by `k × n`
is viewed as a `k × k` array of `n × n` blocks, and `Φ` is applied to each block. -/
def ampliation (k : Type) [Fintype k] [DecidableEq k]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix (k × n) (k × n) ℂ) :
    Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: for every `k`, the ampliation `id_{Fin k} ⊗ Φ` maps
positive semidefinite matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ),
    X.PosSemidef → (ampliation (Fin k) Φ X).PosSemidef

/-- `Φ` admits a Kraus decomposition `Φ X = ∑ a, Kₐ X Kₐᴴ`. -/
def HasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix m n ℂ), ∀ X : Matrix n n ℂ, Φ X = ∑ a, K a * X * (K a)ᴴ

omit [Fintype m] [DecidableEq m] in
/-- Every linear map is determined by its Choi matrix. -/
theorem apply_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ)
    (α β : m) : Φ X α β = ∑ i, ∑ j, X i j * choi Φ (i, α) (j, β) := by
  have key : ∀ i j : n, Φ (Matrix.single i j (X i j)) = X i j • Φ (Matrix.single i j 1) := by
    intro i j
    rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, key, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, choi,
    Matrix.of_apply]

/-- Auxiliary: collapsing a Kronecker-delta double sum. -/
theorem sum_prod_delta {k n' : Type} [Fintype k] [Fintype n'] [DecidableEq k] (p : k)
    (c : k → n' → ℂ) : ∑ r, ∑ i, (if p = r then c r i else 0) = ∑ i, c p i := by
  rw [Finset.sum_comm]; simp

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Entries of `A * X * Aᴴ` where `A` is the block-diagonal ampliation `I ⊗ K` of `K`. -/
theorem blockDiag_mul_mul_conjTranspose_apply {k : Type} [Fintype k] [DecidableEq k]
    (K : Matrix m n ℂ) (X : Matrix (k × n) (k × n) ℂ) (p q : k × m) :
    ((Matrix.of fun (p : k × m) (q : k × n) => if p.1 = q.1 then K p.2 q.2 else 0) * X *
      (Matrix.of fun (p : k × m) (q : k × n) => if p.1 = q.1 then K p.2 q.2 else 0)ᴴ) p q
      = ∑ i, ∑ j, K p.2 i * X (p.1, i) (q.1, j) * star (K q.2 j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, sum_prod_delta,
    apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- The ampliation, expressed via the Kraus operators of `Φ`. -/
theorem ampliation_kraus {k : Type} [Fintype k] [DecidableEq k]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {r : ℕ} {K : Fin r → Matrix m n ℂ}
    (hK : ∀ X : Matrix n n ℂ, Φ X = ∑ a, K a * X * (K a)ᴴ)
    (X : Matrix (k × n) (k × n) ℂ) :
    ampliation k Φ X = ∑ a, (Matrix.of fun (p : k × m) (q : k × n) =>
      if p.1 = q.1 then K a p.2 q.2 else 0) * X *
      (Matrix.of fun (p : k × m) (q : k × n) => if p.1 = q.1 then K a p.2 q.2 else 0)ᴴ := by
  ext p q
  simp only [ampliation, Matrix.of_apply, hK, Matrix.sum_apply,
    blockDiag_mul_mul_conjTranspose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus decomposition is completely positive. -/
theorem HasKraus.isCompletelyPositive {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : HasKraus Φ) : IsCompletelyPositive Φ := by
  obtain ⟨r, K, hK⟩ := h
  intro k X hX
  rw [ampliation_kraus Φ hK X]
  exact Matrix.posSemidef_sum _ fun a _ => hX.mul_mul_conjTranspose_same _

omit [Fintype m] [DecidableEq m] in
/-- A completely positive map has positive semidefinite Choi matrix. -/
theorem IsCompletelyPositive.choi_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : IsCompletelyPositive Φ) : (choi Φ).PosSemidef := by
  classical
  set N := Fintype.card n with hN
  set e : n ≃ Fin N := Fintype.equivFin n with he
  -- the (unnormalised) maximally entangled state `Ω = |ω⟩⟨ω|`
  set v : (Fin N × n) → ℂ := fun x => if e.symm x.1 = x.2 then 1 else 0 with hv
  set A : Matrix (Fin N × n) Unit ℂ := Matrix.of fun x _ => v x with hA
  set Ω : Matrix (Fin N × n) (Fin N × n) ℂ := A * Aᴴ with hΩ
  have hΩpsd : Ω.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (Aᴴ)
    simpa [hΩ] using this
  have key : ampliation (Fin N) Φ Ω =
      (choi Φ).submatrix (fun x => (e.symm x.1, x.2)) (fun x => (e.symm x.1, x.2)) := by
    ext p q
    have hblock : (Matrix.of fun i j => Ω (p.1, i) (q.1, j))
        = Matrix.single (e.symm p.1) (e.symm q.1) (1 : ℂ) := by
      ext i j
      simp only [hΩ, hA, hv, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
        Matrix.single_apply, Finset.univ_unique, Finset.sum_const, Finset.card_singleton,
        one_smul]
      split_ifs with h1 <;> simp_all
    simp only [ampliation, choi, Matrix.submatrix_apply, Matrix.of_apply, hblock]
  have hamp := h N Ω hΩpsd
  rw [key] at hamp
  have h2 := hamp.submatrix (fun x : n × m => (e x.1, x.2))
  rw [Matrix.submatrix_submatrix] at h2
  simpa [Function.comp_def] using h2

open scoped MatrixOrder in
/-- A map with positive semidefinite Choi matrix admits a Kraus decomposition. -/
theorem hasKraus_of_choi_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : (choi Φ).PosSemidef) : HasKraus Φ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  set K : (n × m) → Matrix m n ℂ := fun c => Matrix.of fun α i => star (B c (i, α)) with hKdef
  have main : ∀ X : Matrix n n ℂ, Φ X = ∑ c, K c * X * (K c)ᴴ := by
    intro X
    ext α β
    rw [apply_eq_sum_choi Φ X α β]
    simp only [hKdef, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, hB, Matrix.star_eq_conjTranspose, star_star, Finset.sum_mul,
      Finset.mul_sum]
    have inner : ∀ i : n, (∑ j : n, ∑ c : n × m, X i j * (star (B c (i, α)) * B c (j, β)))
        = ∑ c : n × m, ∑ j : n, X i j * (star (B c (i, α)) * B c (j, β)) :=
      fun i => Finset.sum_comm
    rw [Finset.sum_congr rfl fun i _ => inner i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨Fintype.card (n × m), fun a => K ((Fintype.equivFin (n × m)).symm a), fun X => ?_⟩
  rw [main X]
  exact (Equiv.sum_comp (Fintype.equivFin (n × m)).symm fun c => K c * X * (K c)ᴴ).symm

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choi Φ).PosSemidef :=
  ⟨fun h => h.choi_posSemidef, fun h => (hasKraus_of_choi_posSemidef h).isCompletelyPositive⟩

/-- Complete positivity is also equivalent to the existence of a Kraus decomposition. -/
theorem isCompletelyPositive_iff_hasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ HasKraus Φ :=
  ⟨fun h => hasKraus_of_choi_posSemidef h.choi_posSemidef,
    fun h => h.isCompletelyPositive⟩

/-- The identity map is completely positive. -/
theorem isCompletelyPositive_id :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  HasKraus.isCompletelyPositive ⟨1, fun _ => 1, fun X => by simp⟩

/-- Sanity check that the notion is not vacuous: `-id` is not completely positive. -/
theorem not_isCompletelyPositive_neg_id :
    ¬ IsCompletelyPositive (-LinearMap.id : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ]
      Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [choi_jamiolkowski]
  intro h
  have h1 := h.diag_nonneg (i := (0, 0))
  simp only [choi, Matrix.of_apply, LinearMap.neg_apply, LinearMap.id_apply, Matrix.neg_apply,
    Matrix.single_apply, and_self, if_true, Left.nonneg_neg_iff] at h1
  exact absurd h1 (by norm_num)

end QI

