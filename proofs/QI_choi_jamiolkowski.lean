import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped MatrixOrder ComplexOrder

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The ampliation `id_d ⊗ Φ` of a linear map `Φ` between matrix algebras, described
blockwise: the `(a, b)` block of the output is `Φ` applied to the `(a, b)` block of the input. -/
def amp (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {d : Type} (M : Matrix (d × n) (d × n) ℂ) :
    Matrix (d × m) (d × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: every ampliation `id_d ⊗ Φ` maps positive semidefinite
matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (d : Type) [Fintype d] (M : Matrix (d × n) (d × n) ℂ), M.PosSemidef → (amp Φ M).PosSemidef

/-- The Choi matrix of `Φ`, i.e. `(id ⊗ Φ)` applied to (an unnormalized) maximally
entangled state: its `((i,s),(j,t))` entry is `Φ (Eᵢⱼ) s t`. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The unnormalized maximally entangled state `∑ᵢⱼ Eᵢⱼ ⊗ Eᵢⱼ`, as a matrix indexed by `n × n`. -/
def maxEnt (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => (if p.1 = p.2 then 1 else 0) * (if q.1 = q.2 then 1 else 0)

lemma maxEnt_posSemidef : (maxEnt n).PosSemidef := by
  have : maxEnt n = (Matrix.of fun (_ : Unit) (p : n × n) => (if p.1 = p.2 then (1 : ℂ) else 0))ᴴ *
      (Matrix.of fun (_ : Unit) (p : n × n) => (if p.1 = p.2 then (1 : ℂ) else 0)) := by
    ext p q
    simp [maxEnt, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype m] [DecidableEq m] in
lemma amp_maxEnt (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    amp Φ (maxEnt n) = choiMatrix Φ := by
  ext p q
  have h : (Matrix.of fun i j => maxEnt n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 1 := by
    ext i j
    simp only [maxEnt, Matrix.single_apply, Matrix.of_apply, ite_and]
    split_ifs with h1 h2 h3 <;> simp_all [eq_comm]
  simp only [amp, choiMatrix, Matrix.of_apply, h]

omit [Fintype m] [DecidableEq m] in
/-- Expansion of `Φ A` via linearity in the standard matrix basis. -/
lemma apply_eq_sum (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (A : Matrix n n ℂ) (s t : m) :
    Φ A s t = ∑ i : n, ∑ j : n, A i j * Φ (Matrix.single i j 1) s t := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
    ext a b; simp [Matrix.single_apply]
  rw [this, map_smul]
  simp

omit [DecidableEq n] [DecidableEq m] in
/-- If `Φ` has a Kraus decomposition then it is completely positive. -/
lemma isCompletelyPositive_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} {K : Type}
    [Fintype K] (V : K → Matrix m n ℂ) (hV : ∀ A, Φ A = ∑ k, V k * A * (V k)ᴴ) :
    IsCompletelyPositive Φ := by
  classical
  intro d _ M hM
  have hsum : ∀ (d' : Type) [Fintype d'] (h : d' → n → ℂ) (a : d'),
      (∑ c : d', ∑ i : n, if a = c then h c i else 0) = ∑ i : n, h a i := by
    intro d' _ h a
    rw [Finset.sum_comm]
    simp
  have key : amp Φ M = ∑ k : K,
      (Matrix.of fun (p : d × m) (q : d × n) => if p.1 = q.1 then V k p.2 q.2 else 0) * M *
      (Matrix.of fun (p : d × m) (q : d × n) => if p.1 = q.1 then V k p.2 q.2 else 0)ᴴ := by
    ext p q
    simp only [amp, Matrix.of_apply, Matrix.sum_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, ite_mul, zero_mul,
      apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero]
    simp only [hsum]
  rw [key]
  exact Matrix.posSemidef_sum _ fun k _ => hM.mul_mul_conjTranspose_same _

/-- If the Choi matrix is positive semidefinite, `Φ` admits a Kraus decomposition. -/
lemma exists_kraus_of_posSemidef_choi {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : (choiMatrix Φ).PosSemidef) :
    ∃ V : (n × m) → Matrix m n ℂ, ∀ A, Φ A = ∑ k, V k * A * (V k)ᴴ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun k => Matrix.of fun s i => star (B k (i, s)), fun A => ?_⟩
  ext s t
  rw [apply_eq_sum Φ A s t]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hc : ∀ i j : n, Φ (Matrix.single i j 1) s t
      = ∑ k : n × m, star (B k (i, s)) * B k (j, t) := by
    intro i j
    have := congrFun (congrFun hB (i, s)) (j, t)
    simpa [choiMatrix, Matrix.mul_apply, Matrix.star_apply] using this
  have triple : ∀ f : n → n → (n × m) → ℂ,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
    intro f
    have step1 : ∀ j : n, (∑ i, ∑ k, f i j k) = ∑ k, ∑ i, f i j k := fun _ => Finset.sum_comm
    rw [Finset.sum_comm]
    simp_rw [step1]
    rw [Finset.sum_comm]
  simp only [hc, Finset.mul_sum, star_star, Finset.sum_mul]
  rw [triple]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · intro h
    have := h n (maxEnt n) maxEnt_posSemidef
    rwa [amp_maxEnt] at this
  · intro h
    obtain ⟨V, hV⟩ := exists_kraus_of_posSemidef_choi h
    exact isCompletelyPositive_of_kraus V hV

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

