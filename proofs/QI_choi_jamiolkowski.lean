import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]

/-- The amplification (ampliation) `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras.
A matrix indexed by `k × n` is viewed as a `k × k` array of `n × n` blocks; the amplification
applies `Φ` to each block. -/
def amp (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {k : Type} [Fintype k]
    (M : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun pa qb => Φ (Matrix.of fun i j => M (pa.1, i) (qb.1, j)) pa.2 qb.2

/-- `Φ` is completely positive: every amplification `id_k ⊗ Φ` maps positive semidefinite
matrices to positive semidefinite matrices. -/
def IsCP (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] (M : Matrix (k × n) (k × n) ℂ), M.PosSemidef → (amp Φ M).PosSemidef

/-- The Choi matrix of `Φ`: the block matrix whose `(i,j)` block is `Φ (Eᵢⱼ)`. -/
def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun ia jb => Φ (Matrix.single ia.1 jb.1 1) ia.2 jb.2

/-- Every positive semidefinite matrix factors as `Bᴴ * B`. -/
lemma posSemidef_exists_factor {N : Type} [Fintype N] {A : Matrix N N ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix N N ℂ, A = Bᴴ * B := by
  classical
  exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg

omit [Fintype m] in
/-- Expansion of `Φ X` in terms of the Choi matrix. -/
lemma apply_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ)
    (a b : m) : Φ X a b = ∑ i, ∑ j, X i j * choi Φ (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsm : Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) := by
    ext p q; simp [Matrix.single_apply]
  rw [hsm, map_smul]
  simp [choi]

/-- The purely combinatorial rearrangement behind the hard direction. -/
lemma sum_four_swap {K T I J : Type} [Fintype K] [Fintype T] [Fintype I] [Fintype J]
    (f : K → I → ℂ) (g : K → J → ℂ) (u : T → I → ℂ) (v : T → J → ℂ) :
    ∑ i, ∑ j, (∑ s, f s i * g s j) * (∑ t, u t i * v t j)
      = ∑ s, ∑ t, (∑ i, f s i * u t i) * (∑ j, g s j * v t j) := by
  have sum4 : ∀ F : I → J → K → T → ℂ,
      ∑ i, ∑ j, ∑ s, ∑ t, F i j s t = ∑ s, ∑ t, ∑ i, ∑ j, F i j s t := by
    intro F
    rw [show (∑ i, ∑ j, ∑ s, ∑ t, F i j s t) = ∑ x : (I × J) × (K × T),
          F x.1.1 x.1.2 x.2.1 x.2.2 by simp [Fintype.sum_prod_type]]
    rw [show (∑ s, ∑ t, ∑ i, ∑ j, F i j s t) = ∑ y : (K × T) × (I × J),
          F y.2.1 y.2.2 y.1.1 y.1.2 by simp [Fintype.sum_prod_type]]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl
  simp_rw [Finset.sum_mul_sum]
  rw [sum4 fun i j s t => (f s i * g s j) * (u t i * v t j)]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCP Φ ↔ (choi Φ).PosSemidef := by
  constructor
  · -- CP implies the Choi matrix (the image of the maximally entangled state) is PSD
    intro h
    set w : Matrix Unit (n × n) ℂ :=
      Matrix.of fun _ pi => if pi.1 = pi.2 then (1 : ℂ) else 0 with hw
    have hOmega : (choi Φ) = amp Φ (k := n) (wᴴ * w) := by
      ext ⟨p, a⟩ ⟨q, b⟩
      have hblk : (Matrix.of fun i j => (wᴴ * w) (p, i) (q, j)) = Matrix.single p q (1 : ℂ) := by
        ext i j
        simp only [hw, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.single_apply, Finset.univ_unique, Finset.sum_singleton]
        split_ifs <;> simp_all
      simp only [amp, choi, Matrix.of_apply, hblk]
    rw [hOmega]
    exact h n _ (Matrix.posSemidef_conjTranspose_mul_self _)
  · -- A PSD Choi matrix yields a completely positive map
    intro hC k _ M hM
    obtain ⟨D, hD⟩ := posSemidef_exists_factor hC
    obtain ⟨B, hB⟩ := posSemidef_exists_factor hM
    have key : amp Φ M =
        (Matrix.of fun (st : (k × n) × (n × m)) (pa : k × m) =>
          ∑ i, B st.1 (pa.1, i) * D st.2 (i, pa.2))ᴴ *
        (Matrix.of fun (st : (k × n) × (n × m)) (pa : k × m) =>
          ∑ i, B st.1 (pa.1, i) * D st.2 (i, pa.2)) := by
      ext ⟨p, a⟩ ⟨q, b⟩
      have hlhs : amp Φ M (p, a) (q, b)
          = ∑ i, ∑ j, (∑ s, (starRingEnd ℂ) (B s (p, i)) * B s (q, j)) *
              (∑ t, (starRingEnd ℂ) (D t (i, a)) * D t (j, b)) := by
        simp only [amp, Matrix.of_apply]
        rw [apply_eq_sum_choi]
        simp only [Matrix.of_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [show M (p, i) (q, j) = ∑ s, (starRingEnd ℂ) (B s (p, i)) * B s (q, j) by
              rw [hB]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]]
        rw [show choi Φ (i, a) (j, b) = ∑ t, (starRingEnd ℂ) (D t (i, a)) * D t (j, b) by
              rw [hD]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]]
      rw [hlhs, sum_four_swap (fun s i => (starRingEnd ℂ) (B s (p, i)))
        (fun s j => B s (q, j)) (fun t i => (starRingEnd ℂ) (D t (i, a)))
        (fun t j => D t (j, b))]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, star_sum, star_mul', Complex.star_def]
    rw [key]
    exact Matrix.posSemidef_conjTranspose_mul_self _

end QI

