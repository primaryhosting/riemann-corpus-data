import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
it applies `Φ` to each `n × n` block of a `(k × n) × (k × n)` matrix. -/
def amplify (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (k : Type) [Fintype k]
    (M : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: every amplification `id_k ⊗ Φ` maps positive
semidefinite matrices to positive semidefinite matrices. -/
def IsCP (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] (M : Matrix (k × n) (k × n) ℂ),
    M.PosSemidef → (amplify Φ k M).PosSemidef

/-- `Φ` is trace preserving. -/
def IsTP (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ ρ : Matrix n n ℂ, (Φ ρ).trace = ρ.trace

omit [Fintype n] [DecidableEq n] in
/-- Sanity check: the identity channel is completely positive, so the hypotheses of
`QI.stinespring` are satisfiable. -/
theorem id_isCP : IsCP (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  intro k _ M hM
  have h : amplify (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) k M = M := by
    ext p q; simp [amplify]
  rw [h]; exact hM

omit [DecidableEq n] in
/-- Sanity check: the identity channel is trace preserving. -/
theorem id_isTP : IsTP (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := fun _ => rfl

private lemma sum_triple_rev {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [show (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c from
    Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

section Kraus

variable {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}

/-- The (unnormalized) maximally entangled state `|Ω⟩⟨Ω|` on `n ⊗ n`, written as
`WᴴW` so that it is manifestly positive semidefinite. -/
noncomputable def omegaMat (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  (Matrix.of fun (_ : Unit) (p : n × n) => if p.1 = p.2 then (1 : ℂ) else 0)ᴴ *
    (Matrix.of fun (_ : Unit) (p : n × n) => if p.1 = p.2 then (1 : ℂ) else 0)

lemma omegaMat_posSemidef : (omegaMat n).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The `(i, j)`-block of `|Ω⟩⟨Ω|` is the matrix unit `Eᵢⱼ`. -/
lemma omegaMat_block (i j : n) :
    (Matrix.of fun a b => omegaMat n (i, a) (j, b)) = Matrix.single i j (1 : ℂ) := by
  ext a b
  simp [omegaMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/-- **Kraus decomposition.** A completely positive map between matrix algebras has the
form `ρ ↦ ∑ c, A c * ρ * (A c)ᴴ`. This is obtained from the positive semidefiniteness
of the Choi matrix `(id ⊗ Φ) |Ω⟩⟨Ω|`. -/
theorem exists_kraus (hCP : IsCP Φ) :
    ∃ A : n × m → Matrix m n ℂ, ∀ ρ : Matrix n n ℂ, Φ ρ = ∑ c, A c * ρ * (A c)ᴴ := by
  have hJ : (amplify Φ n (omegaMat n)).PosSemidef := hCP n (omegaMat n) omegaMat_posSemidef
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  set A : n × m → Matrix m n ℂ := fun c => Matrix.of fun x i => star (B c (i, x)) with hA
  have hchoi : ∀ (p q : n) (x y : m),
      Φ (Matrix.single p q 1) x y = ∑ c, A c x p * star (A c y q) := by
    intro p q x y
    have h1 : amplify Φ n (omegaMat n) (p, x) (q, y) = Φ (Matrix.single p q 1) x y := by
      rw [amplify]; simp only [Matrix.of_apply]; rw [omegaMat_block]
    rw [← h1, hB]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hA, mul_comm]
  refine ⟨A, fun ρ => ?_⟩
  ext x y
  have hL : Φ ρ x y = ∑ p, ∑ q, ρ p q * Φ (Matrix.single p q 1) x y := by
    conv_lhs => rw [matrix_eq_sum_single ρ]
    simp only [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [show Matrix.single p q (ρ p q) = ρ p q • Matrix.single p q (1 : ℂ) by
      simp [Matrix.smul_single], map_smul]
    simp
  have hR : (∑ c, A c * ρ * (A c)ᴴ) x y
      = ∑ p, ∑ q, ρ p q * (∑ c, A c x p * star (A c y q)) := by
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [sum_triple_rev (fun c q p => A c x p * ρ p q * star (A c y q))]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun c _ => by ring
  rw [hL, hR]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hchoi]

omit [DecidableEq m] in
/-- Trace preservation turns the Kraus operators into a resolution of the identity. -/
theorem kraus_sum_eq_one (hTP : IsTP Φ) {A : n × m → Matrix m n ℂ}
    (hA : ∀ ρ : Matrix n n ℂ, Φ ρ = ∑ c, A c * ρ * (A c)ᴴ) :
    ∑ c, (A c)ᴴ * A c = 1 := by
  have key : ∀ ρ : Matrix n n ℂ, ((∑ c, (A c)ᴴ * A c) * ρ).trace = ρ.trace := by
    intro ρ
    have h1 : ((∑ c, (A c)ᴴ * A c) * ρ).trace = ∑ c, (A c * ρ * (A c)ᴴ).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun c _ => (Matrix.trace_mul_cycle (A c) ρ (A c)ᴴ).symm
    rw [h1, ← Matrix.trace_sum, ← hA ρ, hTP ρ]
  ext i j
  have h := key (Matrix.single j i 1)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.single_apply,
    mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  simpa [Matrix.one_apply, eq_comm] using h

end Kraus

/-- **Stinespring dilation.** Every completely positive trace preserving (CPTP) map
`Φ` from `n × n` complex matrices to `m × m` complex matrices admits an environment
`E`, an isometry `V : ℂⁿ → ℂᵐ ⊗ ℂᴱ` (i.e. `Vᴴ V = 1`) such that `Φ ρ` is the partial
trace over `E` of `V ρ Vᴴ`, and `V` is the corner of a unitary `U` acting on the
larger space `(m × E) ⊕ n`: `U` maps the subspace `ℂⁿ` (the second summand) exactly
onto the image of `V` inside `ℂᵐ ⊗ ℂᴱ` (the first summand). -/
theorem stinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (hCP : IsCP Φ) (hTP : IsTP Φ) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (V : Matrix (m × E) n ℂ)
      (U : Matrix ((m × E) ⊕ n) ((m × E) ⊕ n) ℂ),
      Vᴴ * V = 1 ∧
      U ∈ Matrix.unitaryGroup ((m × E) ⊕ n) ℂ ∧
      U.submatrix Sum.inl Sum.inr = V ∧
      U.submatrix Sum.inr Sum.inr = 0 ∧
      ∀ (ρ : Matrix n n ℂ) (x y : m), Φ ρ x y = ∑ e : E, (V * ρ * Vᴴ) (x, e) (y, e) := by
  obtain ⟨A, hA⟩ := exists_kraus hCP
  have hone : ∑ c, (A c)ᴴ * A c = 1 := kraus_sum_eq_one hTP hA
  set V : Matrix (m × (n × m)) n ℂ := Matrix.of fun p i => A p.2 p.1 i with hV
  have hVV : Vᴴ * V = 1 := by
    ext i j
    have : (Vᴴ * V) i j = ∑ c : n × m, ((A c)ᴴ * A c) i j := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hV, Matrix.of_apply,
        Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [this, ← Matrix.sum_apply, hone]
  refine ⟨n × m, inferInstance, inferInstance, V,
    Matrix.fromBlocks (1 - V * Vᴴ) V (-Vᴴ) 0, hVV, ?_, ?_, ?_, ?_⟩
  · have e1 : V * Vᴴ * V = V := by rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    have e2 : Vᴴ * V * Vᴴ = Vᴴ := by rw [hVV, Matrix.one_mul]
    have hPh : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    have hPV : (1 - V * Vᴴ) * V = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, e1, sub_self]
    have hVP : Vᴴ * (1 - V * Vᴴ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, e2, sub_self]
    have hP2 : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPV, Matrix.zero_mul, sub_zero]
    have hVh : (-Vᴴ)ᴴ = -V := by simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    have h1 : (1 - V * Vᴴ) * (1 - V * Vᴴ)ᴴ + V * Vᴴ = 1 := by
      rw [hPh, hP2, sub_add_cancel]
    have h2 : (1 - V * Vᴴ) * (-Vᴴ)ᴴ + V * (0 : Matrix n n ℂ)ᴴ = 0 := by
      rw [hVh, Matrix.mul_neg, hPV]
      simp
    have h3 : (-Vᴴ) * (1 - V * Vᴴ)ᴴ + (0 : Matrix n n ℂ) * Vᴴ = 0 := by
      rw [hPh, Matrix.neg_mul, hVP]
      simp
    have h4 : (-Vᴴ) * (-Vᴴ)ᴴ + (0 : Matrix n n ℂ) * (0 : Matrix n n ℂ)ᴴ = 1 := by
      rw [hVh, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hVV]
      simp
    rw [h1, h2, h3, h4, Matrix.fromBlocks_one]
  · ext p i; simp [Matrix.submatrix_apply, Matrix.fromBlocks]
  · ext p i; simp [Matrix.submatrix_apply, Matrix.fromBlocks]
  · intro ρ x y
    rw [hA ρ]
    simp only [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hV]

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

