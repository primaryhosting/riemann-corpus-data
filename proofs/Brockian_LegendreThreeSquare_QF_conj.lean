import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/
def QF {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) : ℤ := v ⬝ᵥ A.mulVec v

/-- Positive definiteness of an integral quadratic form. -/
def PosDefZ {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  ∀ v : Fin k → ℤ, v ≠ 0 → 0 < QF A v

lemma QF_conj {k : ℕ} (A U : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) :
    QF (Uᵀ * A * U) v = QF A (U.mulVec v) := by
  simp only [QF]
  simp only [Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc]
  have h : (Uᵀ * (A * U)) *ᵥ v = Uᵀ *ᵥ ((A * U) *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
  rw [h]
  have key : ∀ (x y : Fin k → ℤ) (M : Matrix (Fin k) (Fin k) ℤ), x ⬝ᵥ (Mᵀ *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
    intro x y M
    simp [Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1 with i
    simp [mul_comm, Finset.mul_sum]
    ring_nf
  exact key v _ U

lemma exists_inv_of_det_one {k : ℕ} (S : Matrix (Fin k) (Fin k) ℤ) (h : S.det = 1) :
    ∃ T : Matrix (Fin k) (Fin k) ℤ, S * T = 1 ∧ T * S = 1 := by
  use S⁻¹
  have hu : IsUnit S.det := by rw [h]; exact isUnit_one
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩

lemma conj_isSymm {k : ℕ} (A U : Matrix (Fin k) (Fin k) ℤ) (hsym : A.IsSymm) :
    (Uᵀ * A * U).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsym.eq,
    Matrix.mul_assoc]

lemma conj_det {k : ℕ} (A U : Matrix (Fin k) (Fin k) ℤ) (hU : U.det = 1) :
    (Uᵀ * A * U).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU]
  ring

lemma conj_posDef {k : ℕ} (A U : Matrix (Fin k) (Fin k) ℤ) (hpos : PosDefZ A) (hU : U.det = 1) :
    PosDefZ (Uᵀ * A * U) := by
  intro v hv
  rw [QF_conj]
  apply hpos
  intro heq
  obtain ⟨T, hTU, hUT⟩ := exists_inv_of_det_one U hU
  have key : v = T *ᵥ (U *ᵥ v) := by
    have h1 : (T * U) *ᵥ v = T *ᵥ (U *ᵥ v) := (Matrix.mulVec_mulVec v T U).symm
    rw [hUT] at h1
    simp [h1.symm]
  rw [heq] at key
  simp at key
  exact hv key

lemma conj_entry00_2 (C U : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) (hU : ∀ i, U i 0 = v i) :
    (Uᵀ * C * U) 0 0 = QF C v := by
  simp [QF, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hU]
  ring

lemma conj_entry00_3 (A U : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) (hU : ∀ i, U i 0 = v i) :
    (Uᵀ * A * U) 0 0 = QF A v := by
  simp [QF, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hU]
  ring

lemma factor_of_conj {k : ℕ} (A S N : Matrix (Fin k) (Fin k) ℤ) (hS : S.det = 1)
    (h : Sᵀ * A * S = Nᵀ * N) : ∃ M : Matrix (Fin k) (Fin k) ℤ, A = Mᵀ * M := by
  obtain ⟨T, hST, hTS⟩ := exists_inv_of_det_one S hS
  use N * T
  have key : Tᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, hST, Matrix.transpose_one]
  calc A = 1 * A * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
    _ = (Tᵀ * Sᵀ) * A * (S * T) := by rw [key, hST]
    _ = Tᵀ * (Sᵀ * A * S) * T := by simp [Matrix.mul_assoc]
    _ = Tᵀ * (Nᵀ * N) * T := by rw [h]
    _ = (N * T)ᵀ * (N * T) := by rw [Matrix.transpose_mul]; simp [Matrix.mul_assoc]

/-! ## Minkowski's convex body theorem -/

/-- Minkowski's convex body theorem for the lattice spanned by a basis of `Fin k → ℝ`. -/
lemma convex_ellipsoid (k : ℕ) (r : ℝ) : Convex ℝ {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hle : ∀ i ∈ Finset.univ,
      ((s • x + t • y : Fin k → ℝ) i) ^ 2 ≤ s * (x i) ^ 2 + t * (y i) ^ 2 := by
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [sq_nonneg (x i - y i), mul_nonneg hs ht]
  have hrr : s * r + t * r = r := by rw [← add_mul, hst, one_mul]
  have key : s * (∑ i, (x i) ^ 2) + t * (∑ i, (y i) ^ 2) < r := by
    rcases lt_or_eq_of_le hs with hs' | hs'
    · have h1 : s * (∑ i, (x i) ^ 2) < s * r := mul_lt_mul_of_pos_left hx hs'
      have h2 : t * (∑ i, (y i) ^ 2) ≤ t * r := mul_le_mul_of_nonneg_left hy.le ht
      linarith
    · have hs0 : s = 0 := hs'.symm
      have ht1 : t = 1 := by linarith
      rw [hs0, ht1]; simpa using hy
  calc ∑ i, ((s • x + t • y : Fin k → ℝ) i) ^ 2
      ≤ ∑ i, (s * (x i) ^ 2 + t * (y i) ^ 2) := Finset.sum_le_sum hle
    _ = s * (∑ i, (x i) ^ 2) + t * (∑ i, (y i) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ < r := key

/-- Minkowski's convex body theorem for the lattice spanned by a basis of `Fin k → ℝ`. -/
theorem minkowski_basis {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (S : Set (Fin k → ℝ)) (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S)
    (hvol : ENNReal.ofReal |(Matrix.of ⇑b).det| * 2 ^ k < volume S) :
    ∃ c : Fin k → ℤ, c ≠ 0 ∧ ∑ i, c i • b i ∈ S := by
  classical
  have hcount : Countable ↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup := by
    have hsur : Function.Surjective (fun c : Fin k → ℤ => (⟨∑ i, c i • b i, by
        refine Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩ :
        ↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup)) := by
      rintro ⟨x, hx⟩
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, hc⟩ := hx
      exact ⟨c, Subtype.ext (by simpa using hc)⟩
    exact Function.Surjective.countable hsur
  have hfd : IsAddFundamentalDomain (↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup)
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain b volume
  have hvol' : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |(Matrix.of ⇑b).det| :=
    ZSpan.volume_fundamentalDomain b
  have hrank : Module.finrank ℝ (Fin k → ℝ) = k := by simp
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfd hsymm hconv
      (by rw [hvol', hrank]; exact hvol)
  have hxmem : (x : Fin k → ℝ) ∈ Submodule.span ℤ (Set.range ⇑b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxmem
  refine ⟨c, ?_, ?_⟩
  · intro h
    apply hx0
    have hx : (x : Fin k → ℝ) = 0 := by rw [← hc, h]; simp
    exact Subtype.ext hx
  · rw [hc]; exact hxS

lemma ball_set_eq (k : ℕ) (r : ℝ) (hr : 0 < r) :
    {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = {x : Fin k → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < r} := by
  ext x
  have h1 : (∑ i, |x i| ^ (2 : ℝ)) = ∑ i, (x i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h1, ← Real.sqrt_eq_rpow,
    show r = Real.sqrt (r ^ 2) by rw [Real.sqrt_sq hr.le],
    Real.sqrt_lt_sqrt_iff hnn, Real.sq_sqrt (by positivity)]

theorem volume_ellipsoid3 :
    (8 : ℝ≥0∞) < volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < 19 / 10} := by
  have hr : (0 : ℝ) < Real.sqrt (19 / 10) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt (19 / 10) ^ 2 = 19 / 10 := Real.sq_sqrt (by norm_num)
  have hset : {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < 19 / 10}
      = {x : Fin 3 → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < Real.sqrt (19 / 10)} := by
    rw [← ball_set_eq 3 _ hr, hsq]
  rw [hset, MeasureTheory.volume_sum_rpow_lt (Fin 3) (by norm_num)]
  simp only [Fintype.card_fin]
  have g1 : Real.Gamma (1 / (2 : ℝ) + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have g2 : Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) = 3 * Real.sqrt Real.pi / 4 := by
    rw [show (((3 : ℕ) : ℝ) / 2 + 1) = (1 / 2 + 1) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [g1, g2]
  have hpi : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hconst : (2 * (Real.sqrt Real.pi / 2)) ^ 3 / (3 * Real.sqrt Real.pi / 4)
      = 4 * Real.pi / 3 := by
    field_simp
    nlinarith [hsqpi, hpi]
  rw [hconst, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity),
    show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  set s := Real.sqrt (19 / 10)
  have h3 : s ^ 3 > 2.6 := by nlinarith [Real.sqrt_nonneg (19 / 10 : ℝ)]
  nlinarith [Real.pi_gt_three, h3]

theorem volume_ellipsoid2 :
    (4 : ℝ≥0∞) < volume {x : Fin 2 → ℝ | ∑ i, (x i) ^ 2 < 13 / 10} := by
  have hr : (0 : ℝ) < Real.sqrt (13 / 10) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt (13 / 10) ^ 2 = 13 / 10 := Real.sq_sqrt (by norm_num)
  have hset : {x : Fin 2 → ℝ | ∑ i, (x i) ^ 2 < 13 / 10}
      = {x : Fin 2 → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < Real.sqrt (13 / 10)} := by
    rw [← ball_set_eq 2 _ hr, hsq]
  rw [hset, MeasureTheory.volume_sum_rpow_lt (Fin 2) (by norm_num)]
  simp only [Fintype.card_fin]
  have g1 : Real.Gamma (1 / (2 : ℝ) + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have g2 : Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) = 1 := by
    rw [show (((2 : ℕ) : ℝ) / 2 + 1) = (1 : ℝ) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one]
    ring
  rw [g1, g2]
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hconst : (2 * (Real.sqrt Real.pi / 2)) ^ 2 / 1 = Real.pi := by
    field_simp
    exact hsqpi
  rw [hconst, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity),
    show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ENNReal.ofReal_lt_ofReal_iff (by positivity), hsq]
  nlinarith [Real.pi_gt_d2]

theorem minkowski_matrix {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hdet : M.det = 1) (r : ℝ)
    (hvol : (2 : ℝ≥0∞) ^ k < volume {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r}) :
    ∃ v : Fin k → ℤ, v ≠ 0 ∧ ∑ i, (M.mulVec (fun j => (v j : ℝ)) i) ^ 2 < r := by
  classical
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  set b : Module.Basis (Fin k) ℝ (Fin k → ℝ) :=
    (Pi.basisFun ℝ (Fin k)).map (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin k)) M hu) with hbdef
  have hb : ∀ i j, b i j = M j i := by
    intro i j
    simp only [hbdef, Module.Basis.map_apply, Pi.basisFun_apply, Matrix.toLinearEquiv_apply]
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdetb : |(Matrix.of ⇑b).det| = 1 := by
    have h : (Matrix.of ⇑b) = Mᵀ := by ext i j; simpa using hb i j
    rw [h, Matrix.det_transpose, hdet, abs_one]
  obtain ⟨c, hc0, hcS⟩ := minkowski_basis b {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r}
    (convex_ellipsoid k r) (by intro x hx; simpa using hx) (by rw [hdetb]; simpa using hvol)
  refine ⟨c, hc0, ?_⟩
  have h2 : (∑ i, c i • b i) = M.mulVec (fun j => (c j : ℝ)) := by
    funext j
    simp only [Finset.sum_apply, zsmul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun x _ => by simp [hb x j]; ring
  rwa [h2] at hcS

theorem minkowski3 (M : Matrix (Fin 3) (Fin 3) ℝ) (hdet : M.det = 1) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧ ∑ i, (M.mulVec (fun j => (v j : ℝ)) i) ^ 2 < 19 / 10 :=
  minkowski_matrix M hdet (19 / 10) (by norm_num; exact volume_ellipsoid3)

theorem minkowski2 (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1) :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ ∑ i, (M.mulVec (fun j => (v j : ℝ)) i) ^ 2 < 13 / 10 :=
  minkowski_matrix M hdet (13 / 10)
    (by rw [show ((2 : ℝ≥0∞) ^ 2) = 4 by norm_num]; exact volume_ellipsoid2)

/-! ## Cholesky decompositions -/

/-- Explicit Cholesky factor of a positive definite binary integral form of determinant `1`. -/
noncomputable def chol2Mat (C : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt (C 0 0), (C 0 1 : ℝ) / Real.sqrt (C 0 0);
     0, 1 / Real.sqrt (C 0 0)]

/-- Explicit Cholesky factor of a positive definite ternary integral form of determinant `1`. -/
noncomputable def chol3Mat (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt (A 0 0), (A 0 1 : ℝ) / Real.sqrt (A 0 0), (A 0 2 : ℝ) / Real.sqrt (A 0 0);
     0, Real.sqrt (((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ) / (A 0 0 : ℝ)),
        ((A 0 0 * A 1 2 - A 0 1 * A 0 2 : ℤ) : ℝ) /
          Real.sqrt ((A 0 0 : ℝ) * ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ));
     0, 0, 1 / Real.sqrt ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ)]

lemma chol2_det (C : Matrix (Fin 2) (Fin 2) ℤ) (h00 : 0 < C 0 0) :
    (chol2Mat C).det = 1 := by
  have h1 : (0 : ℝ) < (C 0 0 : ℝ) := by exact_mod_cast h00
  have hs : Real.sqrt (C 0 0) > 0 := Real.sqrt_pos.mpr h1
  simp [chol2Mat, Matrix.det_fin_two]
  field_simp

lemma chol2_apply (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (h00 : 0 < C 0 0)
    (hdet : C.det = 1) (v : Fin 2 → ℤ) :
    ((QF C v : ℤ) : ℝ) = ∑ i, ((chol2Mat C).mulVec (fun j => (v j : ℝ)) i) ^ 2 := by
  have h1 : (0 : ℝ) < (C 0 0 : ℝ) := by exact_mod_cast h00
  have hs : Real.sqrt (C 0 0) > 0 := Real.sqrt_pos.mpr h1
  have hsq : Real.sqrt (C 0 0) ^ 2 = (C 0 0 : ℝ) := Real.sq_sqrt h1.le
  have hsym10 : C 1 0 = C 0 1 := by
    have := congr_fun (congr_fun hsym 1) 0; simpa using this.symm
  have hd : (C 0 0 : ℝ) * (C 1 1 : ℝ) - (C 0 1 : ℝ) * (C 0 1 : ℝ) = 1 := by
    have h3 : C.det = C 0 0 * C 1 1 - C 0 1 * C 1 0 := by simp [Matrix.det_fin_two]
    rw [hsym10] at h3
    have h2 : C 0 0 * C 1 1 - C 0 1 * C 0 1 = 1 := by rw [← h3, hdet]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
  simp only [QF, chol2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul]
  push_cast [hsym10]
  field_simp
  rw [hsq]
  linear_combination ((v 1 : ℝ)) ^ 2 * hd

lemma chol3_det (A : Matrix (Fin 3) (Fin 3) ℤ) (h00 : 0 < A 0 0)
    (hd2 : 0 < A 0 0 * A 1 1 - A 0 1 ^ 2) (hdet : A.det = 1) :
    (chol3Mat A).det = 1 := by
  have h1 : (A 0 0 : ℝ) > 0 := by exact_mod_cast h00
  have h2 : ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ) > 0 := by exact_mod_cast hd2
  unfold chol3Mat
  simp [Matrix.det_fin_three]
  have h3 : Real.sqrt (↑(A 0 0)) * Real.sqrt ((↑(A 0 0) * ↑(A 1 1) - ↑(A 0 1) ^ 2) / ↑(A 0 0)) =
      Real.sqrt (↑(A 0 0 * A 1 1 - A 0 1 ^ 2)) := by
    rw [← Real.sqrt_mul h1.le]
    congr 1
    rw [mul_div_cancel₀ _ (ne_of_gt h1)]
    norm_cast
  rw [h3]
  field_simp
  norm_cast
  rw [div_self (ne_of_gt (Real.sqrt_pos.mpr h2))]

lemma chol3_apply (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (h00 : 0 < A 0 0)
    (hd2 : 0 < A 0 0 * A 1 1 - A 0 1 ^ 2) (hdet : A.det = 1) (v : Fin 3 → ℤ) :
    ((QF A v : ℤ) : ℝ) = ∑ i, ((chol3Mat A).mulVec (fun j => (v j : ℝ)) i) ^ 2 := by
  have ha : (0 : ℝ) < (A 0 0 : ℝ) := by exact_mod_cast h00
  have hd : (0 : ℝ) < ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ) := by exact_mod_cast hd2
  have h10 : A 1 0 = A 0 1 := by have := congr_fun (congr_fun hsym 1) 0; simpa using this.symm
  have h20 : A 2 0 = A 0 2 := by have := congr_fun (congr_fun hsym 2) 0; simpa using this.symm
  have h21 : A 2 1 = A 1 2 := by have := congr_fun (congr_fun hsym 2) 1; simpa using this.symm
  have hdetR : (A 0 0 : ℝ) * (A 1 1 : ℝ) * (A 2 2 : ℝ)
      + 2 * (A 0 1 : ℝ) * (A 0 2 : ℝ) * (A 1 2 : ℝ) - (A 0 0 : ℝ) * (A 1 2 : ℝ) ^ 2
      - (A 1 1 : ℝ) * (A 0 2 : ℝ) ^ 2 - (A 2 2 : ℝ) * (A 0 1 : ℝ) ^ 2 = 1 := by
    have hh : A.det = 1 := hdet
    rw [Matrix.det_fin_three] at hh
    have h2 : A 0 0 * A 1 1 * A 2 2 + 2 * A 0 1 * A 0 2 * A 1 2
        - A 0 0 * A 1 2 ^ 2 - A 1 1 * A 0 2 ^ 2 - A 2 2 * A 0 1 ^ 2 = 1 := by
      rw [h10, h20, h21] at hh; linarith [hh]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
  simp only [QF, chol3Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [Real.sqrt_div hd.le, Real.sqrt_mul ha.le]
  push_cast [h10, h20, h21]
  set sa := Real.sqrt (A 0 0 : ℝ) with hsadef
  set sd := Real.sqrt ((A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2) with hsddef
  have hsa2 : sa ^ 2 = (A 0 0 : ℝ) := Real.sq_sqrt ha.le
  have hdpos : (0 : ℝ) < (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := by push_cast at hd; linarith
  have hsd2 : sd ^ 2 = (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := Real.sq_sqrt hdpos.le
  have hsa4 : sa ^ 4 = (A 0 0 : ℝ) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsa2]
  have hsd4 : sd ^ 4 = ((A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsd2]
  have hsa : sa ≠ 0 := by rw [hsadef]; positivity
  have hsd : sd ≠ 0 := by rw [hsddef]; positivity
  field_simp
  ring_nf
  rw [hsa4, hsd4, hsa2, hsd2]
  ring_nf
  linear_combination ((A 0 0 : ℝ) * (v 2 : ℝ) ^ 2) * hdetR

/-! ## Leading minors of a positive definite integral form -/

lemma minor1_pos2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hpos : PosDefZ C) : 0 < C 0 0 := by
  have := hpos ![1, 0] (by decide)
  simpa [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

lemma minor1_pos3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hpos : PosDefZ A) : 0 < A 0 0 := by
  have := hpos ![1, 0, 0] (by decide)
  simpa [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this

lemma minor2_pos3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (hpos : PosDefZ A) :
    0 < A 0 0 * A 1 1 - A 0 1 ^ 2 := by
  -- First, use that A 0 0 > 0 (from positive definiteness with v = ![1, 0, 0])
  have h00 : 0 < A 0 0 := by
    have := hpos ![1, 0, 0] (by decide)
    simp [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    exact this
  -- Use vector v = ![A 0 1, -A 0 0, 0]
  -- QF A v = A 0 0 * (A 0 1)^2 + 2 * A 0 1 * A 0 1 * (-A 0 0) + A 1 1 * (A 0 0)^2
  --        = A 0 0 * (A 0 0 * A 1 1 - A 0 1 ^ 2)
  let v : Fin 3 → ℤ := ![A 0 1, -A 0 0, 0]
  have hv_ne : v ≠ 0 := by
    intro hv_eq
    have := congrFun hv_eq 1
    simp [v] at this
    linarith
  have hv_pos := hpos v hv_ne
  simp [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hv_pos
  simp [v] at hv_pos
  -- hv_pos should now be: 0 < A 0 1 * (A 0 0 * A 0 1 + A 0 1 * (-A 0 0)) + (-A 0 0) * (A 1 0 * A 0 1 + A 1 1 * (-A 0 0))
  -- Simplifies to: 0 < A 0 1 * (A 0 0 * A 0 1 - A 0 1 * A 0 0) + (-A 0 0) * (A 1 0 * A 0 1 - A 1 1 * A 0 0)
  -- = 0 < 0 + (-A 0 0) * (A 1 0 * A 0 1 - A 1 1 * A 0 0)
  -- = 0 < A 0 0 * (A 1 1 * A 0 0 - A 1 0 * A 0 1)
  -- Since A is symmetric, A 1 0 = A 0 1, so:
  -- = 0 < A 0 0 * (A 1 1 * A 0 0 - A 0 1 * A 0 1)
  -- = 0 < A 0 0 * (A 0 0 * A 1 1 - A 0 1 ^ 2)
  have hsym01 : A 1 0 = A 0 1 := by
    have : Aᵀ = A := hsym
    have := congr_fun (congr_fun this 1) 0
    simp at this
    exact this.symm
  -- At this point hv_pos : 0 < (-A 0 0) * (A 1 0 * A 0 1 + A 1 1 * (-A 0 0))
  -- which equals A 0 0 * (A 0 0 * A 1 1 - A 0 1 * A 1 0)
  rw [hsym01] at hv_pos
  nlinarith

/-! ## Forms of determinant one represent `1` -/

theorem exists_QF_eq_one2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (hpos : PosDefZ C)
    (hdet : C.det = 1) : ∃ v : Fin 2 → ℤ, QF C v = 1 := by
  have h00 : 0 < C 0 0 := minor1_pos2 C hpos
  obtain ⟨c, hc_ne, hc_mem⟩ := minkowski2 (chol2Mat C) (chol2_det C h00)
  refine ⟨c, ?_⟩
  have hpos_val : 0 < QF C c := hpos c hc_ne
  have hreal : ((QF C c : ℤ) : ℝ) = ∑ i, ((chol2Mat C).mulVec (fun j => (c j : ℝ)) i) ^ 2 :=
    chol2_apply C hsym h00 hdet c
  have hlt : (QF C c : ℝ) < 13 / 10 := by rwa [hreal]
  have hle : QF C c ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have : (QF C c : ℝ) ≥ 2 := by exact_mod_cast hcon
    linarith
  omega

theorem exists_QF_eq_one3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (hpos : PosDefZ A)
    (hdet : A.det = 1) : ∃ v : Fin 3 → ℤ, QF A v = 1 := by
  -- Get that the leading minors are positive
  have h00 : 0 < A 0 0 := minor1_pos3 A hpos
  have hd2 : 0 < A 0 0 * A 1 1 - A 0 1 ^ 2 := minor2_pos3 A hsym hpos
  -- chol3Mat A has det = 1
  have hdet_chol : (chol3Mat A).det = 1 := chol3_det A h00 hd2 hdet
  -- Use minkowski3 with chol3Mat A
  obtain ⟨c, hc_ne, hc_mem⟩ := minkowski3 (chol3Mat A) hdet_chol
  -- Show QF A c = 1
  use c
  have hpos_val : 0 < QF A c := hpos c hc_ne
  have hreal : ((QF A c : ℤ) : ℝ) = ∑ i, ((chol3Mat A).mulVec (fun j => (c j : ℝ)) i) ^ 2 := by
    apply chol3_apply A hsym h00 hd2 hdet
  -- Since QF A c is a positive integer < 19/10, it must be 1
  have hlt : (QF A c : ℝ) < 19 / 10 := by rwa [hreal]
  have hint : QF A c ≤ 1 := by
    by_contra h
    push_neg at h
    have : (QF A c : ℝ) ≥ 2 := by exact_mod_cast h
    linarith
  omega

/-! ## Completing a primitive vector to a basis -/

theorem exists_unimodular_col2 (v : Fin 2 → ℤ) (w : Fin 2 → ℤ) (h : w ⬝ᵥ v = 1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ ∀ i, U i 0 = v i := by
  use !![v 0, -w 1; v 1, w 0]
  refine ⟨?_, fun i => by fin_cases i <;> rfl⟩
  simp [Matrix.det_fin_two]
  linarith [show w 0 * v 0 + w 1 * v 1 = 1 from by simpa [dotProduct, Fin.sum_univ_two] using h]

theorem exists_unimodular_col3 (v : Fin 3 → ℤ) (w : Fin 3 → ℤ) (h : w ⬝ᵥ v = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ ∀ i, U i 0 = v i := by
  have hdot : w 0 * v 0 + w 1 * v 1 + w 2 * v 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using h
  by_cases hg : (Int.gcd (v 1) (v 2) : ℤ) = 0
  · -- Degenerate case: the last two coordinates vanish, so `v 0 = ±1`.
    obtain ⟨h1, h2⟩ := Int.gcd_eq_zero_iff.mp (by exact_mod_cast hg)
    have h0 : v 0 * v 0 = 1 := by
      rw [h1, h2] at hdot
      have hvw : v 0 * w 0 = 1 := by linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hvw with h' | h' <;> rw [h'] <;> ring
    refine ⟨!![v 0, 0, 0; 0, 1, 0; 0, 0, v 0], ?_, ?_⟩
    · simp [Matrix.det_fin_three]
      linear_combination h0
    · intro i; fin_cases i <;> simp [h1, h2]
  · -- Main case: write `v 1 = g * a`, `v 2 = g * b` with `g = gcd (v 1) (v 2)`.
    obtain ⟨a, ha⟩ : ((Int.gcd (v 1) (v 2) : ℤ)) ∣ v 1 := Int.gcd_dvd_left _ _
    obtain ⟨b, hb⟩ : ((Int.gcd (v 1) (v 2) : ℤ)) ∣ v 2 := Int.gcd_dvd_right _ _
    set g : ℤ := (Int.gcd (v 1) (v 2) : ℤ) with hgdef
    set s : ℤ := Int.gcdA (v 1) (v 2) with hs
    set t : ℤ := Int.gcdB (v 1) (v 2) with ht
    have hst : v 1 * s + v 2 * t = g := (Int.gcd_eq_gcd_ab (v 1) (v 2)).symm
    have hab : a * s + b * t = 1 := by
      have hcan : g * (a * s + b * t) = g * 1 := by
        rw [ha, hb] at hst; linarith [hst]
      exact mul_left_cancel₀ hg hcan
    refine ⟨!![v 0, -(w 1 * a + w 2 * b), 0; v 1, a * w 0, -t; v 2, b * w 0, s], ?_, ?_⟩
    · rw [ha, hb] at hdot
      rw [ha, hb]
      simp [Matrix.det_fin_three]
      linear_combination (v 0 * w 0 + (w 1 * a + w 2 * b) * g) * hab + hdot
    · intro i; fin_cases i <;> simp

/-! ## Clearing the first row and column -/

lemma clear_first2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (h00 : C 0 0 = 1) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℤ, V.det = 1 ∧ Vᵀ * C * V = !![1, 0; 0, C 1 1 - C 0 1 ^ 2] := by
  have hsym10 : C 1 0 = C 0 1 := by
    have := congr_fun (congr_fun hsym 1) 0; simpa using this.symm
  refine ⟨!![1, -C 0 1; 0, 1], by simp [Matrix.det_fin_two], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, hsym10] <;> ring

lemma clear_first3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (h00 : A 0 0 = 1) :
    ∃ V : Matrix (Fin 3) (Fin 3) ℤ, V.det = 1 ∧ Vᵀ * A * V =
      !![1, 0, 0;
         0, A 1 1 - A 0 1 ^ 2, A 1 2 - A 0 1 * A 0 2;
         0, A 1 2 - A 0 1 * A 0 2, A 2 2 - A 0 2 ^ 2] := by
  use !![1, -A 0 1, -A 0 2; 0, 1, 0; 0, 0, 1]
  have sym01 : A 1 0 = A 0 1 := by have := congrFun (congrFun hsym 1) 0; simp at this; exact this.symm
  have sym02 : A 2 0 = A 0 2 := by have := congrFun (congrFun hsym 2) 0; simp at this; exact this.symm
  have sym12 : A 2 1 = A 1 2 := by have := congrFun (congrFun hsym 2) 1; simp at this; exact this.symm
  refine ⟨by simp [Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, sym01, sym02, sym12, h00] <;> ring_nf

lemma block_det (p q r : ℤ) :
    (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ).det = p * r - q ^ 2 := by
  simp [Matrix.det_fin_three]; ring

lemma block_isSymm (p q r : ℤ) :
    (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma block_posDef (p q r : ℤ) (h : PosDefZ (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ)) :
    PosDefZ (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro v hv_ne
  -- Extend v to a 3-vector by prepending 0
  let w : Fin 3 → ℤ := ![0, v 0, v 1]
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    apply hv_ne
    funext i
    fin_cases i <;> have := congrFun hw_eq 1 <;> have := congrFun hw_eq 2 <;> simp [w] at * <;> linarith
  have hw_pos := h w hw_ne
  -- Now show QF of 3x3 on w equals QF of 2x2 on v
  simp [QF, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hw_pos ⊢
  simp [w] at hw_pos ⊢
  ring_nf at hw_pos ⊢
  exact hw_pos

lemma block_factor (p q r : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ) = Nᵀ * N) :
    ∃ N' : Matrix (Fin 3) (Fin 3) ℤ,
      (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ) = N'ᵀ * N' := by
  refine ⟨!![1, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1], ?_⟩
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linarith

/-! ## Classification of unimodular positive definite forms -/

theorem classify2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (hpos : PosDefZ C)
    (hdet : C.det = 1) : ∃ N : Matrix (Fin 2) (Fin 2) ℤ, C = Nᵀ * N := by
  obtain ⟨v, hv⟩ := exists_QF_eq_one2 C hsym hpos hdet
  -- w = C.mulVec v satisfies w ⬝ᵥ v = QF C v = 1
  let w := C.mulVec v
  have hwv : w ⬝ᵥ v = 1 := by
    have h := hv
    simp [QF, dotProduct] at h
    convert h using 1
    simp [w, Matrix.mulVec]
    ring
  obtain ⟨U, hUdet, hUcol⟩ := exists_unimodular_col2 v w hwv
  -- (Uᵀ * C * U) 0 0 = QF C v = 1
  have h00 : (Uᵀ * C * U) 0 0 = 1 := by
    have := conj_entry00_2 C U v hUcol
    simp [this, hv]
  -- Apply clear_first2
  obtain ⟨V, hVdet, hV⟩ := clear_first2 (Uᵀ * C * U) (conj_isSymm C U hsym) h00
  -- W = U * V, so Wᵀ * C * W = !![1, 0; 0, d]
  let W := U * V
  have hWdet : W.det = 1 := by simp [W, hUdet, hVdet]
  have hW : Wᵀ * C * W = !![1, 0; 0, (Uᵀ * C * U) 1 1 - (Uᵀ * C * U) 0 1 ^ 2] := by
    have : Wᵀ * C * W = Vᵀ * (Uᵀ * C * U) * V := by simp [W, Matrix.mul_assoc]
    rw [this, hV]
  -- The (1,1) entry equals 1 since det is preserved
  let d := (Uᵀ * C * U) 1 1 - (Uᵀ * C * U) 0 1 ^ 2
  have hd : d = 1 := by
    have hdet' := conj_det C W hWdet
    rw [hW] at hdet'
    simp [Matrix.det_fin_two] at hdet'
    have hCdet : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 1 := by simp [Matrix.det_fin_two] at hdet; linarith [hsym.eq]
    linarith
  -- Wᵀ * C * W = 1, so C = (W⁻¹)ᵀ * W⁻¹
  have hWone : Wᵀ * C * W = 1 := by
    rw [hW]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith [hd]
  -- Use exists_inv_of_det_one to get W⁻¹
  obtain ⟨Winv, hWWinv, hWinvW⟩ := exists_inv_of_det_one W hWdet
  use Winv
  -- C = Winvᵀ * Winv because Wᵀ * C * W = 1
  calc C = 1 * C * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
    _ = (Winvᵀ * Wᵀ) * C * (W * Winv) := by rw [← Matrix.transpose_mul, hWWinv]; simp
    _ = Winvᵀ * (Wᵀ * C * W) * Winv := by simp [Matrix.mul_assoc]
    _ = Winvᵀ * Winv := by rw [hWone]; simp

theorem classify3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (hpos : PosDefZ A)
    (hdet : A.det = 1) : ∃ N : Matrix (Fin 3) (Fin 3) ℤ, A = Nᵀ * N := by
  obtain ⟨v, hv⟩ := exists_QF_eq_one3 A hsym hpos hdet
  have hwv : (A.mulVec v) ⬝ᵥ v = 1 := by
    rw [dotProduct_comm]; exact hv
  obtain ⟨U, hUdet, hUcol⟩ := exists_unimodular_col3 v (A.mulVec v) hwv
  set A1 := Uᵀ * A * U with hA1
  have hA1sym : A1.IsSymm := conj_isSymm A U hsym
  have hA1pos : PosDefZ A1 := conj_posDef A U hpos hUdet
  have h00 : A1 0 0 = 1 := by rw [hA1, conj_entry00_3 A U v hUcol]; exact hv
  obtain ⟨V, hVdet, hV⟩ := clear_first3 A1 hA1sym h00
  set W := U * V with hWdef
  have hWdet : W.det = 1 := by rw [hWdef, Matrix.det_mul, hUdet, hVdet, one_mul]
  set p := A1 1 1 - A1 0 1 ^ 2 with hp
  set q := A1 1 2 - A1 0 1 * A1 0 2 with hq
  set r := A1 2 2 - A1 0 2 ^ 2 with hr
  have hW : Wᵀ * A * W = !![1, 0, 0; 0, p, q; 0, q, r] := by
    have hexp : Wᵀ * A * W = Vᵀ * A1 * V := by
      rw [hWdef, hA1, Matrix.transpose_mul]
      simp [Matrix.mul_assoc]
    rw [hexp, hV]
  have hbdet : (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := by
    rw [← hW, conj_det A W hWdet, hdet]
  have hbpos : PosDefZ (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ) := by
    rw [← hW]; exact conj_posDef A W hpos hWdet
  have h2det : (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have hb := block_det p q r
    rw [hbdet] at hb
    rw [Matrix.det_fin_two_of]
    nlinarith [hb]
  have h2sym : (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨N2, hN2⟩ := classify2 _ h2sym (block_posDef p q r hbpos) h2det
  obtain ⟨N3, hN3⟩ := block_factor p q r N2 hN2
  exact factor_of_conj A W N3 hWdet (by rw [hW, hN3])

/-! ## The auxiliary ternary form -/

/-- The ternary form used to represent `n`. -/
def auxMat (n x c m : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![n, 1, 0; 1, c, -x; 0, -x, m]

lemma auxMat_isSymm (n x c m : ℤ) : (auxMat n x c m).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma auxMat_det (n x c m : ℤ) (hrel : n * (c * m - x ^ 2) - m = 1) :
    (auxMat n x c m).det = 1 := by
  simp [auxMat, Matrix.det_fin_three]
  linarith [hrel]

lemma auxMat_key (n x c m : ℤ) (hrel : n * (c * m - x ^ 2) - m = 1) (u v w : ℤ) :
    n * (n * c - 1) * QF (auxMat n x c m) ![u, v, w]
      = (n * c - 1) * (n * u + v) ^ 2 + ((n * c - 1) * v - n * x * w) ^ 2 + n * w ^ 2 := by
  simp [QF, dotProduct, auxMat, Fin.sum_univ_three, Matrix.mulVec, Matrix.of_apply]
  have h1 : m * (n * c - 1) = n * x ^ 2 + 1 := by linarith
  linear_combination n * w ^ 2 * h1

lemma auxMat_posDef (n x c m : ℤ) (hn : 0 < n) (hc : 0 < n * c - 1)
    (hrel : n * (c * m - x ^ 2) - m = 1) : PosDefZ (auxMat n x c m) := by
  intro v hv
  have hv3 : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [hv3]
  have hkey := auxMat_key n x c m hrel (v 0) (v 1) (v 2)
  set t := n * c - 1 with ht
  have hA : 0 ≤ t * (n * v 0 + v 1) ^ 2 := by positivity
  have hB : 0 ≤ (t * v 1 - n * x * v 2) ^ 2 := sq_nonneg _
  have hC : 0 ≤ n * (v 2) ^ 2 := by positivity
  have hpos : 0 < t * (n * v 0 + v 1) ^ 2 + (t * v 1 - n * x * v 2) ^ 2 + n * (v 2) ^ 2 := by
    rcases eq_or_ne (v 2) 0 with h2 | h2
    · rcases eq_or_ne (v 1) 0 with h1 | h1
      · have h0 : v 0 ≠ 0 := by
          intro h0; apply hv; funext i; fin_cases i <;> simp [h0, h1, h2]
        have hne : n * v 0 + v 1 ≠ 0 := by
          rw [h1, add_zero]; exact mul_ne_zero (by omega) h0
        have hpp : 0 < t * (n * v 0 + v 1) ^ 2 := by positivity
        linarith
      · have hne : t * v 1 - n * x * v 2 ≠ 0 := by
          rw [h2]; simpa using mul_ne_zero (by omega) h1
        have hpp : 0 < (t * v 1 - n * x * v 2) ^ 2 := by positivity
        linarith
    · have hpp : 0 < n * (v 2) ^ 2 := by positivity
      linarith
  have hnt : 0 < n * t := mul_pos hn hc
  nlinarith [hkey, hpos, hnt]

/-! ## From the arithmetic data to three squares -/

theorem sum_three_squares_of_matrix (n : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) (h00 : A 0 0 = (n : ℤ))
    (hsym : A.IsSymm) (hpos : PosDefZ A) (hdet : A.det = 1) :
    ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨N, hN⟩ := classify3 A hsym hpos hdet
  have hentry : A 0 0 = (N 0 0) ^ 2 + (N 1 0) ^ 2 + (N 2 0) ^ 2 := by
    rw [hN]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h00] at hentry
  refine ⟨Int.natAbs (N 0 0), Int.natAbs (N 1 0), Int.natAbs (N 2 0), ?_⟩
  have h1 : ((N 0 0).natAbs : ℤ) ^ 2 = (N 0 0) ^ 2 := by simp [sq_abs]
  have h2 : ((N 1 0).natAbs : ℤ) ^ 2 = (N 1 0) ^ 2 := by simp [sq_abs]
  have h3 : ((N 2 0).natAbs : ℤ) ^ 2 = (N 2 0) ^ 2 := by simp [sq_abs]
  push_cast at h1 h2 h3 ⊢
  linarith

/-- From `n ∣ m + 1` and `m ∣ y ^ 2 + n` one produces the entries of the auxiliary form. -/
theorem exists_aux_data (n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hdvd : n ∣ m + 1) (y : ℤ)
    (hy : (m : ℤ) ∣ y ^ 2 + n) :
    ∃ x c : ℤ, 0 < (n : ℤ) * c - 1 ∧ (n : ℤ) * (c * (m : ℤ) - x ^ 2) - (m : ℤ) = 1 := by
  have hnz : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  obtain ⟨D, hD⟩ : ∃ D : ℤ, (m : ℤ) + 1 = (n : ℤ) * D := by
    obtain ⟨d, hd⟩ := hdvd
    exact ⟨(d : ℤ), by exact_mod_cast congrArg (fun z : ℕ => (z : ℤ)) hd⟩
  have hDpos : 0 < D := by nlinarith
  obtain ⟨e, he⟩ := hy
  have hdvd2 : (m : ℤ) ∣ (y * D) ^ 2 + D := by
    refine ⟨D * D * e - D, ?_⟩
    have hexp : (y * D) ^ 2 + D = D * (D * (y ^ 2 + n) - (m : ℤ)) := by linear_combination D * hD
    rw [hexp, he]; ring
  obtain ⟨c, hc⟩ := hdvd2
  have hcpos : 0 < c := by nlinarith [sq_nonneg (y * D)]
  refine ⟨y * D, c, by nlinarith, ?_⟩
  have hcm : c * (m : ℤ) = (y * D) ^ 2 + D := by linarith [hc]
  rw [hcm]
  linarith [hD]

theorem three_squares_of_modulus (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hm : 0 < m) (hdvd : n ∣ m + 1)
    (y : ℤ) (hy : (m : ℤ) ∣ y ^ 2 + n) : ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨x, c, hc1, hrel⟩ := exists_aux_data n m hn hm hdvd y hy
  have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
  refine sum_three_squares_of_matrix n (auxMat (n : ℤ) x c (m : ℤ)) ?_
    (auxMat_isSymm _ _ _ _) (auxMat_posDef _ _ _ _ hnz hc1 hrel) (auxMat_det _ _ _ _ hrel)
  simp [auxMat]

/-! ## Dirichlet's theorem and quadratic reciprocity -/

lemma exists_prime_mod (M : ℕ) (hM : 0 < M) (r : ℕ) (hr : Nat.Coprime r M) (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p % M = r % M := by
  by_cases hM0 : M = 0
  · simp [hM0] at hM
  have h : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ r [MOD M]} := by
    exact Nat.infinite_setOf_prime_and_modEq hM0 hr
  obtain ⟨p, hp, hpN⟩ := h.exists_gt N
  exact ⟨p, hp.1, hpN, by simpa using hp.2⟩

lemma jacobi_p_mod_n (n p : ℕ) (hpn : (p + 1) % n = 0) :
    jacobiSym (p : ℤ) n = jacobiSym (-1) n := by
  have h : (p : ℤ) ≡ -1 [ZMOD n] := by
    have hdvd : (n : ℤ) ∣ (p + 1) := by norm_cast; exact Nat.dvd_of_mod_eq_zero hpn
    exact Int.ModEq.symm (Int.modEq_of_dvd <| by simpa using hdvd)
  rw [jacobiSym.mod_left p n]
  rw [jacobiSym.mod_left (-1) n]
  simp [Int.ModEq] at h
  rw [h]

lemma jacobi_two_p_mod_n (n p : ℕ) (hpn : (2 * p + 1) % n = 0) :
    jacobiSym (2 * p : ℤ) n = jacobiSym (-1) n := by
  have h : (2 * p : ℤ) ≡ -1 [ZMOD n] := by
    have hdvd : (n : ℤ) ∣ (2 * (p : ℤ) + 1) := by
      have h2 : (n : ℤ) ∣ ((2 * p + 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hpn)
      push_cast at h2; exact h2
    exact Int.ModEq.symm (Int.modEq_of_dvd <| by simpa using hdvd)
  rw [jacobiSym.mod_left (2 * p : ℤ) n, jacobiSym.mod_left (-1) n]
  simp [Int.ModEq] at h
  rw [h]

/-- Case `n ≡ 1 [MOD 4]`. -/
lemma jacobi_case1 (n p : ℕ) (hn : n % 4 = 1) (hn3 : 3 ≤ n) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpn : (p + 1) % n = 0) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hnodd : Odd n := by rw [Nat.odd_iff]; omega
  have hchi4n : ZMod.χ₄ (n : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ n % 2 = 0), if_pos hn]
  have hchi4p : ZMod.χ₄ (p : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_pos hp4]
  have hpn1 : jacobiSym (p : ℤ) n = 1 := by
    rw [jacobi_p_mod_n n p hpn, jacobiSym.at_neg_one hnodd, hchi4n]
  have hrec : jacobiSym (n : ℤ) p = (-1) ^ (n / 2 * (p / 2)) * jacobiSym (p : ℤ) n :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hneg : jacobiSym (-(n : ℤ)) p = jacobiSym (-1) p * jacobiSym (n : ℤ) p := by
    rw [← jacobiSym.mul_left]; ring_nf
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hpd : p / 2 = 2 * k := by omega
  rw [hneg, hrec, hpn1, jacobiSym.at_neg_one hpodd, hchi4p,
    show ((-1 : ℤ) ^ (n / 2 * (p / 2))) = 1 from
      Even.neg_one_pow (by rw [hpd]; exact ⟨n / 2 * k, by ring⟩)]
  ring

/-- Case `n ≡ 3 [MOD 8]`. -/
lemma jacobi_case2 (n p : ℕ) (hn : n % 8 = 3) (hn3 : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 * p + 1) % n = 0) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hnodd : Odd n := by rw [Nat.odd_iff]; omega
  obtain ⟨b, hb⟩ : ∃ b, n = 8 * b + 3 := ⟨n / 8, by omega⟩
  have hn2 : n / 2 = 4 * b + 1 := by omega
  have hchi4n : ZMod.χ₄ (n : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ n % 2 = 0), if_neg (by omega : ¬ n % 4 = 1)]
  have hchi8n : ZMod.χ₈ (n : ZMod 8) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [if_neg (by omega : ¬ n % 2 = 0), if_neg (by omega : ¬ (n % 8 = 1 ∨ n % 8 = 7))]
  have hpn1 : jacobiSym (p : ℤ) n = 1 := by
    have h1 : jacobiSym (2 * p : ℤ) n = jacobiSym (-1) n := jacobi_two_p_mod_n n p hpn
    rw [show ((2 * p : ℤ)) = (2 : ℤ) * (p : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_two hnodd, jacobiSym.at_neg_one hnodd, hchi4n, hchi8n] at h1
    linarith [h1]
  have hrec : jacobiSym (n : ℤ) p = (-1) ^ (n / 2 * (p / 2)) * jacobiSym (p : ℤ) n :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hneg : jacobiSym (-(n : ℤ)) p = jacobiSym (-1) p * jacobiSym (n : ℤ) p := by
    rw [← jacobiSym.mul_left]; ring_nf
  rw [hneg, hrec, hpn1, jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_eq_if_mod_four]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by rw [Nat.odd_iff] at hpodd; omega
  rcases hp4 with h4 | h4
  · obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
    have hpd : p / 2 = 2 * k := by omega
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_pos h4]
    rw [show ((-1 : ℤ) ^ (n / 2 * (p / 2))) = 1 from
      Even.neg_one_pow (by rw [hn2, hpd]; exact ⟨(4 * b + 1) * k, by ring⟩)]
    ring
  · obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    have hpd : p / 2 = 2 * k + 1 := by omega
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_neg (by omega : ¬ p % 4 = 1)]
    rw [show ((-1 : ℤ) ^ (n / 2 * (p / 2))) = -1 from
      Odd.neg_one_pow (by rw [hn2, hpd]; exact ⟨(4 * b + 1) * k + 2 * b, by ring⟩)]
    ring

/-- Case `n ≡ 2 [MOD 8]`, `n = 2 * n'`. -/
lemma jacobi_case3 (n' p : ℕ) (hn : n' % 4 = 1) (hn3 : 1 ≤ n') (hp : p.Prime) (hp8 : p % 8 = 1)
    (hpn : (p + 1) % n' = 0) : jacobiSym (-(2 * n' : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hnodd : Odd n' := by rw [Nat.odd_iff]; omega
  have hchi4n : ZMod.χ₄ (n' : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ n' % 2 = 0), if_pos hn]
  have hchi4p : ZMod.χ₄ (p : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_pos (by omega : p % 4 = 1)]
  have hchi8p : ZMod.χ₈ (p : ZMod 8) = 1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_pos (Or.inl hp8)]
  have hpn1 : jacobiSym (p : ℤ) n' = 1 := by
    rw [jacobi_p_mod_n n' p hpn, jacobiSym.at_neg_one hnodd, hchi4n]
  have hrec : jacobiSym (n' : ℤ) p = (-1) ^ (n' / 2 * (p / 2)) * jacobiSym (p : ℤ) n' :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hsplit : jacobiSym (-(2 * n' : ℤ)) p
      = jacobiSym (-1) p * (jacobiSym 2 p * jacobiSym (n' : ℤ) p) := by
    rw [← jacobiSym.mul_left, ← jacobiSym.mul_left]; ring_nf
  obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 1 := ⟨p / 8, by omega⟩
  have hpd : p / 2 = 4 * k := by omega
  rw [hsplit, hrec, hpn1, jacobiSym.at_neg_one hpodd, jacobiSym.at_two hpodd, hchi4p, hchi8p,
    show ((-1 : ℤ) ^ (n' / 2 * (p / 2))) = 1 from
      Even.neg_one_pow (by rw [hpd]; exact ⟨n' / 2 * (2 * k), by ring⟩)]
  ring

/-- Case `n ≡ 6 [MOD 8]`, `n = 2 * n'`. -/
lemma jacobi_case4 (n' p : ℕ) (hn : n' % 4 = 3) (hn3 : 3 ≤ n') (hp : p.Prime) (hp8 : p % 8 = 3)
    (hpn : (p + 1) % n' = 0) : jacobiSym (-(2 * n' : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hnodd : Odd n' := by rw [Nat.odd_iff]; omega
  have hchi4n : ZMod.χ₄ (n' : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ n' % 2 = 0), if_neg (by omega : ¬ n' % 4 = 1)]
  have hchi4p : ZMod.χ₄ (p : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_neg (by omega : ¬ p % 4 = 1)]
  have hchi8p : ZMod.χ₈ (p : ZMod 8) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_neg (by omega : ¬ (p % 8 = 1 ∨ p % 8 = 7))]
  have hpn1 : jacobiSym (p : ℤ) n' = -1 := by
    rw [jacobi_p_mod_n n' p hpn, jacobiSym.at_neg_one hnodd, hchi4n]
  have hrec : jacobiSym (n' : ℤ) p = (-1) ^ (n' / 2 * (p / 2)) * jacobiSym (p : ℤ) n' :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hsplit : jacobiSym (-(2 * n' : ℤ)) p
      = jacobiSym (-1) p * (jacobiSym 2 p * jacobiSym (n' : ℤ) p) := by
    rw [← jacobiSym.mul_left, ← jacobiSym.mul_left]; ring_nf
  obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, n' = 4 * c + 3 := ⟨n' / 4, by omega⟩
  have hpd : p / 2 = 4 * k + 1 := by omega
  have hnd : n' / 2 = 2 * c + 1 := by omega
  rw [hsplit, hrec, hpn1, jacobiSym.at_neg_one hpodd, jacobiSym.at_two hpodd, hchi4p, hchi8p,
    show ((-1 : ℤ) ^ (n' / 2 * (p / 2))) = -1 from
      Odd.neg_one_pow (by rw [hpd, hnd]; exact ⟨(2 * c + 1) * (2 * k) + c, by ring⟩)]
  ring

lemma sq_of_jacobi_eq_one (p : ℕ) (hp : p.Prime) (a : ℤ) (hpa : ¬ (p : ℤ) ∣ a)
    (h : jacobiSym a p = 1) : ∃ y : ℤ, (p : ℤ) ∣ y ^ 2 - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p a = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have hne : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hpa
  obtain ⟨z, hz⟩ := (legendreSym.eq_one_iff p hne).1 hleg
  refine ⟨(z.val : ℤ), ?_⟩
  have hcast : ((((z.val : ℤ)) ^ 2 - a : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, hz]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcast

lemma nat_coprime_of_bezout (r M : ℕ) (u v : ℤ) (h : u * (r : ℤ) + v * (M : ℤ) = 1) :
    Nat.Coprime r M := by
  rw [← Nat.isCoprime_iff_coprime]; exact ⟨u, v, h⟩

lemma not_dvd_neg_of_lt (n p : ℕ) (hn : 0 < n) (hp : n < p) : ¬ (p : ℤ) ∣ (-(n : ℤ)) := by
  intro hd
  have hd2 : (p : ℤ) ∣ (n : ℤ) := dvd_neg.mp hd
  have := Int.le_of_dvd (by exact_mod_cast hn) hd2
  omega

lemma good_case1 (n : ℕ) (hn : 3 ≤ n) (h : n % 4 = 1) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  have hcop : Nat.Coprime (2 * n - 1) (4 * n) := by
    refine nat_coprime_of_bezout _ _ (2 * (n : ℤ) - 1) (-((n : ℤ) - 1)) ?_
    have hc : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by
      have h1 : 1 ≤ 2 * n := by omega
      push_cast [Nat.cast_sub h1]; ring
    rw [hc]; push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod (4 * n) (by omega) (2 * n - 1) hcop n
  have hmod : p % (4 * n) = 2 * n - 1 := by rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / (4 * n) with hq
  set X := 4 * n * q with hX
  have hpk : p = X + (2 * n - 1) := by
    conv_lhs => rw [← Nat.div_add_mod p (4 * n), hmod]
  have hXdvd4 : 4 ∣ X := ⟨n * q, by rw [hX]; ring⟩
  have hXdvdn : n ∣ X := ⟨4 * q, by rw [hX]; ring⟩
  have hp4 : p % 4 = 1 := by obtain ⟨t, ht⟩ := hXdvd4; omega
  have hdvd : n ∣ p + 1 := by
    have hp1 : p + 1 = X + 2 * n := by omega
    rw [hp1]
    exact Nat.dvd_add hXdvdn ⟨2, by ring⟩
  have hpn : (p + 1) % n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd |> fun _ => Nat.mod_eq_zero_of_dvd hdvd
  refine ⟨p, hp.pos, hdvd, ?_⟩
  obtain ⟨y, hy⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt)
    (jacobi_case1 n p h hn hp hp4 hpn)
  exact ⟨y, by simpa using hy⟩

lemma good_case2 (n : ℕ) (hn : 3 ≤ n) (h : n % 8 = 3) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  obtain ⟨b, hb⟩ : ∃ b, n = 8 * b + 3 := ⟨n / 8, by omega⟩
  have hcop : Nat.Coprime (4 * b + 1) n := by
    refine nat_coprime_of_bezout _ _ (-2) 1 ?_
    rw [hb]; push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod n (by omega) (4 * b + 1) hcop n
  have hmod : p % n = 4 * b + 1 := by rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / n with hq
  have hpk : p = n * q + (4 * b + 1) := by conv_lhs => rw [← Nat.div_add_mod p n, hmod]
  have h2p : n ∣ 2 * p + 1 := ⟨2 * q + 1, by rw [hpk, hb]; ring⟩
  have hpn : (2 * p + 1) % n = 0 := Nat.mod_eq_zero_of_dvd h2p
  have hp2 : p ≠ 2 := by omega
  have hja := jacobi_case2 n p h hn hp hp2 hpn
  obtain ⟨y0, hy0⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt) hja
  have hy0' : (p : ℤ) ∣ y0 ^ 2 + n := by simpa using hy0
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨y, hyodd, hyp⟩ : ∃ y : ℤ, Odd y ∧ (p : ℤ) ∣ y ^ 2 + n := by
    rcases Int.even_or_odd y0 with he | ho
    · refine ⟨y0 + p, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := he
        obtain ⟨j, hj⟩ := hpodd
        exact ⟨k + j, by push_cast [hk, hj]; ring⟩
      · obtain ⟨d, hd⟩ := hy0'
        exact ⟨d + 2 * y0 + p, by rw [show (y0 + p) ^ 2 + (n : ℤ) = (y0 ^ 2 + n) + p * (2 * y0 + p) by ring, hd]; ring⟩
    · exact ⟨y0, ho, hy0'⟩
  refine ⟨2 * p, by omega, by omega, y, ?_⟩
  have h2dvd : (2 : ℤ) ∣ y ^ 2 + n := by
    obtain ⟨j, hj⟩ := hyodd
    refine ⟨2 * j ^ 2 + 2 * j + 4 * b + 2, ?_⟩
    rw [hj, hb]; push_cast; ring
  have hcop2 : IsCoprime (2 : ℤ) (p : ℤ) := by
    obtain ⟨j, hj⟩ := hpodd
    exact ⟨-(j : ℤ), 1, by rw [hj]; push_cast; ring⟩
  have := hcop2.mul_dvd h2dvd hyp
  push_cast
  exact this

lemma good_case3 (n : ℕ) (hn : 3 ≤ n) (h : n % 8 = 2) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  obtain ⟨a, ha⟩ : ∃ a, n = 8 * a + 2 := ⟨n / 8, by omega⟩
  have hcop : Nat.Coprime (8 * a + 1) (8 * (4 * a + 1)) := by
    refine nat_coprime_of_bezout _ _ (8 * (a : ℤ) + 1) (-(2 * (a : ℤ))) ?_
    push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod (8 * (4 * a + 1)) (by omega) (8 * a + 1) hcop n
  have hmod : p % (8 * (4 * a + 1)) = 8 * a + 1 := by
    rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / (8 * (4 * a + 1)) with hq
  set X := 8 * (4 * a + 1) * q with hX
  have hpk : p = X + (8 * a + 1) := by
    conv_lhs => rw [← Nat.div_add_mod p (8 * (4 * a + 1)), hmod]
  have hXdvd8 : 8 ∣ X := ⟨(4 * a + 1) * q, by rw [hX]; ring⟩
  have hp8 : p % 8 = 1 := by obtain ⟨t, ht⟩ := hXdvd8; omega
  have hdvdn : n ∣ p + 1 := by
    refine ⟨4 * q + 1, ?_⟩
    have : p + 1 = X + (8 * a + 2) := by omega
    rw [this, hX, ha]; ring
  have hdvdn' : (4 * a + 1) ∣ p + 1 := by
    refine ⟨8 * q + 2, ?_⟩
    have : p + 1 = X + (8 * a + 2) := by omega
    rw [this, hX]; ring
  have hpn : (p + 1) % (4 * a + 1) = 0 := Nat.mod_eq_zero_of_dvd hdvdn'
  have hja : jacobiSym (-(n : ℤ)) p = 1 := by
    have h3 := jacobi_case3 (4 * a + 1) p (by omega) (by omega) hp hp8 hpn
    rw [show ((n : ℤ)) = 2 * ((4 * a + 1 : ℕ) : ℤ) by rw [ha]; push_cast; ring]
    exact h3
  obtain ⟨y, hy⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt) hja
  exact ⟨p, hp.pos, hdvdn, y, by simpa using hy⟩

lemma good_case4 (n : ℕ) (hn : 3 ≤ n) (h : n % 8 = 6) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  obtain ⟨b, hb⟩ : ∃ b, n = 8 * b + 6 := ⟨n / 8, by omega⟩
  have hcop : Nat.Coprime (16 * b + 11) (8 * (4 * b + 3)) := by
    refine nat_coprime_of_bezout _ _ (16 * (b : ℤ) + 11) (-(2 * (4 * (b : ℤ) + 3) - 1)) ?_
    push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod (8 * (4 * b + 3)) (by omega) (16 * b + 11) hcop n
  have hmod : p % (8 * (4 * b + 3)) = 16 * b + 11 := by
    rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / (8 * (4 * b + 3)) with hq
  set X := 8 * (4 * b + 3) * q with hX
  have hpk : p = X + (16 * b + 11) := by
    conv_lhs => rw [← Nat.div_add_mod p (8 * (4 * b + 3)), hmod]
  have hXdvd8 : 8 ∣ X := ⟨(4 * b + 3) * q, by rw [hX]; ring⟩
  have hp8 : p % 8 = 3 := by obtain ⟨t, ht⟩ := hXdvd8; omega
  have hdvdn : n ∣ p + 1 := by
    refine ⟨4 * q + 2, ?_⟩
    have h2 : p + 1 = X + (16 * b + 12) := by omega
    rw [h2, hX, hb]; ring
  have hdvdn' : (4 * b + 3) ∣ p + 1 := by
    refine ⟨8 * q + 4, ?_⟩
    have h2 : p + 1 = X + (16 * b + 12) := by omega
    rw [h2, hX]; ring
  have hpn : (p + 1) % (4 * b + 3) = 0 := Nat.mod_eq_zero_of_dvd hdvdn'
  have hja : jacobiSym (-(n : ℤ)) p = 1 := by
    have h4 := jacobi_case4 (4 * b + 3) p (by omega) (by omega) hp hp8 hpn
    rw [show ((n : ℤ)) = 2 * ((4 * b + 3 : ℕ) : ℤ) by rw [hb]; push_cast; ring]
    exact h4
  obtain ⟨y, hy⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt) hja
  exact ⟨p, hp.pos, hdvdn, y, by simpa using hy⟩

theorem exists_good_modulus (n : ℕ) (hn : 3 ≤ n) (h4 : n % 4 ≠ 0) (h8 : n % 8 ≠ 7) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  have h8' : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6 := by omega
  rcases h8' with h | h | h | h | h
  · exact good_case1 n hn (by omega)
  · exact good_case3 n hn h
  · exact good_case2 n hn h
  · exact good_case1 n hn (by omega)
  · exact good_case4 n hn h

/-! ## The two directions -/

theorem not_sum_three_squares (k m a b c : ℕ) : 4 ^ k * (8 * m + 7) ≠ a ^ 2 + b ^ 2 + c ^ 2 := by
  induction k generalizing a b c with
  | zero =>
    intro h
    simp at h
    have key' : ∀ x : Fin 8, ∀ y : Fin 8, ∀ z : Fin 8, (x.val ^ 2 + y.val ^ 2 + z.val ^ 2) % 8 ≠ 7 := by decide
    have ha : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
    have hb : b ^ 2 % 8 = (b % 8) ^ 2 % 8 := Nat.pow_mod b 2 8
    have hc : c ^ 2 % 8 = (c % 8) ^ 2 % 8 := Nat.pow_mod c 2 8
    have := key' ⟨a % 8, Nat.mod_lt a (by norm_num)⟩ ⟨b % 8, Nat.mod_lt b (by norm_num)⟩ ⟨c % 8, Nat.mod_lt c (by norm_num)⟩
    have derive : (8 * m + 7) % 8 = 7 := by norm_num
    rw [h] at derive
    simp_all [Nat.add_mod]
  | succ k ih =>
    intro h
    have h4 : 4 ∣ 4 ^ (k + 1) * (8 * m + 7) := ⟨4 ^ k * (8 * m + 7), by ring⟩
    rw [h] at h4
    have hsq4 : ∀ x : Fin 4, x.val ^ 2 % 4 = 0 ∨ x.val ^ 2 % 4 = 1 := by decide
    have hsum : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    have sqmod : ∀ x : ℕ, x ^ 2 % 4 = (x % 4) ^ 2 % 4 := fun x => by rw [Nat.pow_mod]
    have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      rw [sqmod]; exact hsq4 ⟨a % 4, Nat.mod_lt a (by norm_num)⟩
    have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
      rw [sqmod]; exact hsq4 ⟨b % 4, Nat.mod_lt b (by norm_num)⟩
    have hc : c ^ 2 % 4 = 0 ∨ c ^ 2 % 4 = 1 := by
      rw [sqmod]; exact hsq4 ⟨c % 4, Nat.mod_lt c (by norm_num)⟩
    have ha0 : a ^ 2 % 4 = 0 := by omega
    have hb0 : b ^ 2 % 4 = 0 := by omega
    have hc0 : c ^ 2 % 4 = 0 := by omega
    have ha_even : 2 ∣ a := by
      rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> ring_nf at ha0 ⊢ <;> omega
    have hb_even : 2 ∣ b := by
      rcases Nat.even_or_odd' b with ⟨b', rfl | rfl⟩ <;> ring_nf at hb0 ⊢ <;> omega
    have hc_even : 2 ∣ c := by
      rcases Nat.even_or_odd' c with ⟨c', rfl | rfl⟩ <;> ring_nf at hc0 ⊢ <;> omega
    obtain ⟨a', rfl⟩ := ha_even
    obtain ⟨b', rfl⟩ := hb_even
    obtain ⟨c', rfl⟩ := hc_even
    have : 4 ^ k * (8 * m + 7) = a' ^ 2 + b' ^ 2 + c' ^ 2 := by
      have := h
      ring_nf at this ⊢
      linarith [pow_pos (by norm_num : (0 : ℕ) < 4) k]
    exact ih a' b' c' this

theorem core (n : ℕ) (h4 : n % 4 ≠ 0) (h8 : n % 8 ≠ 7) : ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n
    · omega
    · exact ⟨1, 0, 0, by norm_num⟩
    · exact ⟨1, 1, 0, by norm_num⟩
  · obtain ⟨m, hm, hdvd, y, hy⟩ := exists_good_modulus n hge h4 h8
    exact three_squares_of_modulus n hge m hm hdvd y hy

theorem hard_direction (n : ℕ) (h : ¬ ∃ k m : ℕ, n = 4 ^ k * (8 * m + 7)) :
    ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  -- Handle n = 0
  by_cases hn0 : n = 0
  · exact ⟨0, 0, 0, by simp [hn0]⟩
  -- Induction on n: if n % 4 = 0, reduce to n/4; otherwise apply core
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : n % 4 = 0
    · -- n % 4 = 0: write n = 4 * (n/4), apply IH
      let m := n / 4
      have hm_lt : m < n := by simp [m]; omega
      have hm_pos : 0 < m := by simp [m]; omega
      have hm_nh0 : m ≠ 0 := ne_of_gt hm_pos
      have hm_h : ¬∃ k m_1, m = 4 ^ k * (8 * m_1 + 7) := by
        intro ⟨k, m_1, hm_eq⟩
        have hn_eq : n = 4 ^ (k + 1) * (8 * m_1 + 7) := by
          have : 4 ^ (k + 1) * (8 * m_1 + 7) = 4 * (4 ^ k * (8 * m_1 + 7)) := by ring
          rw [this]
          rw [← hm_eq]
          have : n = 4 * (n / 4) := by omega
          exact this
        exact h ⟨k + 1, m_1, hn_eq⟩
      obtain ⟨a', b', c', hm_eq⟩ := ih m hm_lt hm_h hm_nh0 hm_pos
      use 2 * a', 2 * b', 2 * c'
      have hn_eq : n = 4 * m := by simp [m]; omega
      rw [hn_eq, hm_eq]
      ring
    · -- n % 4 ≠ 0: need to show n % 8 ≠ 7 and apply core
      have h8 : n % 8 ≠ 7 := by
        intro h7
        exact h ⟨0, n / 8, by omega⟩
      exact core n h4 h8

/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/
theorem sum_three_squares_iff (n : ℕ) :
    (∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2) ↔ ¬ ∃ k m : ℕ, n = 4 ^ k * (8 * m + 7) := by
  constructor
  · rintro ⟨a, b, c, habc⟩ ⟨k, m, hkm⟩
    exact not_sum_three_squares k m a b c (hkm ▸ habc)
  · exact hard_direction n

end Brockian.LegendreThreeSquare

