import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/
noncomputable def logM (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- A (faithful) density matrix: positive definite with unit trace. -/
def IsDensity (ρ : Matrix n n ℂ) : Prop := ρ.PosDef ∧ ρ.trace = 1

/-- The Umegaki relative entropy `D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * logM ρ)).re - (Matrix.trace (ρ * logM σ)).re

/-! ### Functional calculus lemmas -/

theorem isSelfAdjoint_conj (u : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ}
    (hA : IsSelfAdjoint A) :
    IsSelfAdjoint ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)) := by
  rw [isSelfAdjoint_iff, StarMul.star_mul, StarMul.star_mul, star_star, hA.star_eq, mul_assoc]

theorem cfc_conj_unitary (f : ℝ → ℝ) (u : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ}
    (hA : IsSelfAdjoint A) :
    cfc f ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * cfc f A * star (u : Matrix n n ℂ) := by
  have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) u) f A
    (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
    (by
      show Continuous fun X : Matrix n n ℂ =>
        (u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ)
      fun_prop)
    hA (by simpa [Unitary.conjStarAlgAut_apply] using isSelfAdjoint_conj u hA)
  simp only [Unitary.conjStarAlgAut_apply] at h
  exact h.symm

/-- `Matrix.diagonal` as an `ℝ`-algebra homomorphism. -/
noncomputable def diagAlgHom (n : Type*) [Fintype n] [DecidableEq n] :
    (n → ℂ) →ₐ[ℝ] Matrix n n ℂ where
  toFun := Matrix.diagonal
  map_one' := by simp
  map_mul' x y := by simp [Matrix.diagonal_mul_diagonal]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.diagonal_add]
  commutes' r := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal, Algebra.algebraMap_eq_smul_one]

theorem aeval_diagonal (p : Polynomial ℝ) (d : n → ℝ) :
    (Polynomial.aeval (Matrix.diagonal (fun i => (d i : ℂ)))) p
      = Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  have h : Matrix.diagonal (fun i => (d i : ℂ)) = diagAlgHom n (fun i => (d i : ℂ)) := rfl
  rw [h, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext i
  have h1 := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : n => ℂ) i)
    (fun i => (d i : ℂ)) p
  simp only [Pi.evalAlgHom_apply] at h1
  rw [← h1]
  simpa using (Polynomial.aeval_algebraMap_apply ℂ (d i) p)

omit [Fintype n] in
theorem isSelfAdjoint_diagonal (d : n → ℝ) :
    IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp [Pi.star_def]

theorem spectrum_diagonal_subset (d : n → ℝ) :
    spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro r hr
  by_contra hcon
  apply hr
  have h1 : algebraMap ℝ (Matrix n n ℂ) r - Matrix.diagonal (fun i => (d i : ℂ))
      = Matrix.diagonal (fun i => ((r : ℂ) - d i)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [resolventSet, Set.mem_setOf_eq, h1, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  simp only [sub_ne_zero]
  intro h
  exact hcon ⟨i, by exact_mod_cast h.symm⟩

theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ)))
      = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S : Finset ℝ := Finset.image d Finset.univ with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hnode : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f
      (Set.injOn_of_injective Function.injective_id) hx
  have heq : Set.EqOn f (fun x => p.eval x)
      (spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ)))) := by
    intro x hx
    obtain ⟨i, rfl⟩ := spectrum_diagonal_subset d hx
    exact (hnode _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)).symm
  rw [cfc_congr heq, cfc_polynomial p _ (isSelfAdjoint_diagonal d), aeval_diagonal]
  congr 1
  funext i
  rw [hnode _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)]

/-- The workhorse: the matrix logarithm of `U D U*` with `D` diagonal real. -/
theorem logM_conj_diagonal (u : unitary (Matrix n n ℂ)) (d : n → ℝ) :
    logM ((u : Matrix n n ℂ) * Matrix.diagonal (fun i => (d i : ℂ))
        * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * Matrix.diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ))
        * star (u : Matrix n n ℂ) := by
  rw [logM, cfc_conj_unitary _ _ (isSelfAdjoint_diagonal d), cfc_diagonal]

/-! ### Trace computations -/

theorem trace_conj_diag_mul_conj_diag (u v : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    Matrix.trace (((u : Matrix n n ℂ) * Matrix.diagonal (fun i => (a i : ℂ))
        * star (u : Matrix n n ℂ)) *
        ((v : Matrix n n ℂ) * Matrix.diagonal (fun i => (b i : ℂ))
        * star (v : Matrix n n ℂ)))
      = ((∑ i, ∑ j, a i * b j *
          Complex.normSq ((star (u : Matrix n n ℂ) * (v : Matrix n n ℂ)) i j) : ℝ) : ℂ) := by
  set U := (u : Matrix n n ℂ) with hUdef
  set V := (v : Matrix n n ℂ) with hVdef
  set A := Matrix.diagonal (fun i => (a i : ℂ)) with hA
  set B := Matrix.diagonal (fun i => (b i : ℂ)) with hB
  set M := star U * V with hM
  have e1 : U * A * star U * (V * B * star V) = U * (A * star U * V * B * star V) := by
    noncomm_ring
  have e2 : A * star U * V * B * star V * U = A * M * B * star M := by
    rw [hM, Matrix.star_mul, star_star]
    noncomm_ring
  have e4 : ∀ i j, (A * M * B) i j = (a i : ℂ) * M i j * (b j : ℂ) := by
    intro i j
    rw [hA, hB, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e1, Matrix.trace_mul_comm, e2, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, e4, Matrix.star_apply, RCLike.star_def]
  push_cast [← Complex.mul_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The row sums of the doubly stochastic matrix `|M i j|²` of a unitary `M`. -/
theorem normSq_row_sum (M : Matrix n n ℂ) (h : M * star M = 1) (i : n) :
    ∑ j, Complex.normSq (M i j) = 1 := by
  have h2 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h2
  have h3 : ∀ j : n, M i j * (starRingEnd ℂ) (M i j) = ((Complex.normSq (M i j) : ℝ) : ℂ) :=
    fun j => Complex.mul_conj _
  rw [Finset.sum_congr rfl (fun j _ => h3 j)] at h2
  exact_mod_cast h2

/-- The column sums of the doubly stochastic matrix `|M i j|²` of a unitary `M`. -/
theorem normSq_col_sum (M : Matrix n n ℂ) (h : star M * M = 1) (j : n) :
    ∑ i, Complex.normSq (M i j) = 1 := by
  have h2 := congrFun (congrFun h j) j
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h2
  have h3 : ∀ i : n, (starRingEnd ℂ) (M i j) * M i j = ((Complex.normSq (M i j) : ℝ) : ℂ) :=
    fun i => by rw [mul_comm]; exact Complex.mul_conj _
  rw [Finset.sum_congr rfl (fun i _ => h3 i)] at h2
  exact_mod_cast h2

theorem mul_star_conj_unitary (u v : unitary (Matrix n n ℂ)) :
    (star (u : Matrix n n ℂ) * (v : Matrix n n ℂ))
      * star (star (u : Matrix n n ℂ) * (v : Matrix n n ℂ)) = 1 := by
  rw [Matrix.star_mul, star_star, mul_assoc, ← mul_assoc (v : Matrix n n ℂ),
    show (v : Matrix n n ℂ) * star (v : Matrix n n ℂ) = 1 from Unitary.coe_mul_star_self v,
    one_mul, Unitary.coe_star_mul_self]

theorem star_mul_conj_unitary (u v : unitary (Matrix n n ℂ)) :
    star (star (u : Matrix n n ℂ) * (v : Matrix n n ℂ))
      * (star (u : Matrix n n ℂ) * (v : Matrix n n ℂ)) = 1 := by
  rw [Matrix.star_mul, star_star, mul_assoc, ← mul_assoc (u : Matrix n n ℂ),
    show (u : Matrix n n ℂ) * star (u : Matrix n n ℂ) = 1 from Unitary.coe_mul_star_self u,
    one_mul, Unitary.coe_star_mul_self]

/-! ### The classical inequality behind Klein's inequality -/

omit [DecidableEq n] in
theorem sum_mul_log_le {r s : n → ℝ} {P : n → n → ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) (hcol : ∀ j, ∑ i, P i j = 1)
    (hr : ∀ i, 0 < r i) (hs : ∀ j, 0 < s j) (hrsum : ∑ i, r i = 1) (hssum : ∑ j, s j = 1) :
    ∑ i, ∑ j, r i * P i j * Real.log (s j) ≤ ∑ i, r i * Real.log (r i) := by
  set t : n → ℝ := fun i => ∑ j, P i j * s j with ht
  have htpos : ∀ i, 0 < t i := by
    intro i
    have hex : ∃ j, 0 < P i j := by
      by_contra h
      push_neg at h
      have hz : ∑ j, P i j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hP i j)
      rw [hrow i] at hz
      norm_num at hz
    obtain ⟨j, hj⟩ := hex
    calc (0 : ℝ) < P i j * s j := mul_pos hj (hs j)
      _ ≤ ∑ j, P i j * s j :=
        Finset.single_le_sum (f := fun j => P i j * s j)
          (fun j _ => mul_nonneg (hP i j) (hs j).le) (Finset.mem_univ j)
  have hA : ∀ i, ∑ j, P i j * Real.log (s j) ≤ Real.log (t i) := by
    intro i
    have key : ∀ j ∈ Finset.univ, P i j * Real.log (s j) - P i j * Real.log (t i)
        ≤ P i j * (s j / t i - 1) := by
      intro j _
      have h1 : Real.log (s j / t i) ≤ s j / t i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hs j) (htpos i))
      have h2 : Real.log (s j / t i) = Real.log (s j) - Real.log (t i) :=
        Real.log_div (ne_of_gt (hs j)) (ne_of_gt (htpos i))
      rw [h2] at h1
      nlinarith [hP i j]
    have hsum := Finset.sum_le_sum key
    have hL : ∑ j, (P i j * Real.log (s j) - P i j * Real.log (t i))
        = (∑ j, P i j * Real.log (s j)) - Real.log (t i) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow i, one_mul]
    have hR : ∑ j, P i j * (s j / t i - 1) = 0 := by
      have h : ∑ j, P i j * (s j / t i - 1) = (∑ j, P i j * s j) / t i - ∑ j, P i j := by
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
      have h2 : (∑ j, P i j * s j) = t i := by rw [ht]
      rw [h, h2, hrow i, div_self (htpos i).ne', sub_self]
    rw [hL, hR] at hsum
    linarith
  have hB : ∑ i, r i * Real.log (t i) ≤ ∑ i, r i * Real.log (r i) := by
    have htsum : ∑ i, t i = 1 := by
      simp only [ht]
      rw [Finset.sum_comm]
      calc ∑ j, ∑ i, P i j * s j = ∑ j, (∑ i, P i j) * s j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
        _ = 1 := by simp [hcol, hssum]
    have key : ∀ i ∈ Finset.univ, r i * Real.log (t i) - r i * Real.log (r i) ≤ t i - r i := by
      intro i _
      have h1 : Real.log (t i / r i) ≤ t i / r i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (htpos i) (hr i))
      have h2 : Real.log (t i / r i) = Real.log (t i) - Real.log (r i) :=
        Real.log_div (ne_of_gt (htpos i)) (ne_of_gt (hr i))
      rw [h2] at h1
      have hri := hr i
      have h3 : r i * (Real.log (t i) - Real.log (r i)) ≤ r i * (t i / r i - 1) :=
        mul_le_mul_of_nonneg_left h1 hri.le
      have hrr : r i * (t i / r i - 1) = t i - r i := by field_simp
      nlinarith
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htsum, hrsum] at hsum
    linarith
  calc ∑ i, ∑ j, r i * P i j * Real.log (s j)
      = ∑ i, r i * (∑ j, P i j * Real.log (s j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, r i * Real.log (t i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA i) (hr i).le
    _ ≤ ∑ i, r i * Real.log (r i) := hB

/-! ### Spectral computations of the relative entropy -/

theorem spectral_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ)
      * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
      * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem logM_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    logM A = (hA.eigenvectorUnitary : Matrix n n ℂ)
      * Matrix.diagonal (fun i => ((Real.log (hA.eigenvalues i) : ℝ) : ℂ))
      * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [spectral_decomp hA]
  exact logM_conj_diagonal _ _

/-- The "cross term" `Tr(ρ log σ)` expressed through the eigenvalues of `ρ` and `σ` and the
doubly stochastic matrix relating their eigenbases. -/
theorem trace_mul_logM_re {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (Matrix.trace (ρ * logM σ)).re
      = ∑ i, ∑ j, hρ.eigenvalues i * Real.log (hσ.eigenvalues j) *
          Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix n n ℂ)
            * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  have h : Matrix.trace (ρ * logM σ)
      = ((∑ i, ∑ j, hρ.eigenvalues i * Real.log (hσ.eigenvalues j) *
          Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix n n ℂ)
            * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) : ℝ) : ℂ) := by
    conv_lhs => rw [logM_of_isHermitian hσ, spectral_decomp hρ]
    exact trace_conj_diag_mul_conj_diag _ _ _ _
  rw [h, Complex.ofReal_re]

theorem trace_mul_logM_self_re {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (Matrix.trace (ρ * logM ρ)).re
      = ∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
  rw [trace_mul_logM_re hρ hρ]
  rw [Unitary.coe_star_mul_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Klein's inequality -/

/-- **Klein's inequality**: the quantum relative entropy of two faithful states is nonnegative. -/
theorem relEntropy_nonneg {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    0 ≤ relEntropy ρ σ := by
  obtain ⟨hρpd, hρtr⟩ := hρ
  obtain ⟨hσpd, hσtr⟩ := hσ
  have hρh : ρ.IsHermitian := hρpd.1
  have hσh : σ.IsHermitian := hσpd.1
  have hrsum : ∑ i, hρh.eigenvalues i = 1 := by
    have h1 := hρh.trace_eq_sum_eigenvalues
    rw [hρtr] at h1
    have h2 : ((∑ i, hρh.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  have hssum : ∑ i, hσh.eigenvalues i = 1 := by
    have h1 := hσh.trace_eq_sum_eigenvalues
    rw [hσtr] at h1
    have h2 : ((∑ i, hσh.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  have hkey := sum_mul_log_le
    (r := hρh.eigenvalues) (s := hσh.eigenvalues)
    (P := fun i j => Complex.normSq ((star (hρh.eigenvectorUnitary : Matrix n n ℂ)
      * (hσh.eigenvectorUnitary : Matrix n n ℂ)) i j))
    (fun i j => Complex.normSq_nonneg _)
    (fun i => normSq_row_sum _ (mul_star_conj_unitary _ _) i)
    (fun j => normSq_col_sum _ (star_mul_conj_unitary _ _) j)
    (fun i => hρpd.eigenvalues_pos i) (fun j => hσpd.eigenvalues_pos j) hrsum hssum
  rw [relEntropy, trace_mul_logM_self_re hρh, trace_mul_logM_re hρh hσh, sub_nonneg]
  refine le_trans (le_of_eq ?_) hkey
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Unitary invariance -/

theorem trace_conj_eq (u : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    Matrix.trace ((u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ)) = Matrix.trace X := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

theorem conj_mul_conj (u : unitary (Matrix n n ℂ)) (X Y : Matrix n n ℂ) :
    ((u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ))
      * ((u : Matrix n n ℂ) * Y * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * (X * Y) * star (u : Matrix n n ℂ) := by
  have h : star (u : Matrix n n ℂ) * (u : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self u
  calc ((u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ))
        * ((u : Matrix n n ℂ) * Y * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * X * (star (u : Matrix n n ℂ) * (u : Matrix n n ℂ)) * Y
        * star (u : Matrix n n ℂ) := by noncomm_ring
    _ = (u : Matrix n n ℂ) * (X * Y) * star (u : Matrix n n ℂ) := by
        rw [h]; noncomm_ring

/-- The relative entropy is invariant under unitary channels. -/
theorem relEntropy_unitary_conj (u : unitary (Matrix n n ℂ)) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ((u : Matrix n n ℂ) * ρ * star (u : Matrix n n ℂ))
      ((u : Matrix n n ℂ) * σ * star (u : Matrix n n ℂ)) = relEntropy ρ σ := by
  have hρ' : IsSelfAdjoint ρ := hρ
  have hσ' : IsSelfAdjoint σ := hσ
  have hlρ : logM ((u : Matrix n n ℂ) * ρ * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * logM ρ * star (u : Matrix n n ℂ) := cfc_conj_unitary _ _ hρ'
  have hlσ : logM ((u : Matrix n n ℂ) * σ * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * logM σ * star (u : Matrix n n ℂ) := cfc_conj_unitary _ _ hσ'
  rw [relEntropy, relEntropy, hlρ, hlσ, conj_mul_conj, conj_mul_conj, trace_conj_eq,
    trace_conj_eq]

/-! ### Data processing -/

/-- **Data processing inequality** for a trace-self-adjoint map `E` (a conditional expectation)
which fixes `σ`, together with the logarithms occurring in the statement. -/
theorem data_processing_condExp {E : Matrix n n ℂ → Matrix n n ℂ} {ρ σ : Matrix n n ℂ}
    (hsa : ∀ X Y, Matrix.trace (E X * Y) = Matrix.trace (X * E Y))
    (hρ : IsDensity ρ) (hEρ : IsDensity (E ρ))
    (hEσ : E σ = σ) (hlogσ : E (logM σ) = logM σ) (hlogEρ : E (logM (E ρ)) = logM (E ρ)) :
    relEntropy (E ρ) (E σ) ≤ relEntropy ρ σ := by
  have h1 : Matrix.trace (E ρ * logM (E ρ)) = Matrix.trace (ρ * logM (E ρ)) := by
    rw [hsa ρ (logM (E ρ)), hlogEρ]
  have h2 : Matrix.trace (E ρ * logM σ) = Matrix.trace (ρ * logM σ) := by
    rw [hsa ρ (logM σ), hlogσ]
  have hklein : (0 : ℝ) ≤ (Matrix.trace (ρ * logM ρ)).re - (Matrix.trace (ρ * logM (E ρ))).re :=
    relEntropy_nonneg hρ hEρ
  rw [hEσ, relEntropy, h1, h2, relEntropy]
  linarith

/-! ### The completely dephasing channel -/

/-- The completely dephasing channel in the computational basis: it keeps the diagonal of a
matrix and erases all off-diagonal entries. -/
def dephase (X : Matrix n n ℂ) : Matrix n n ℂ := Matrix.diagonal (fun i => X i i)

/-- A map between matrix algebras is CPTP when it admits a Kraus representation whose Kraus
operators satisfy the trace-preservation condition `∑ K† K = 1`. -/
def IsCPTP {m : Type u} [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ → Matrix m m ℂ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (K : ι → Matrix m n ℂ),
    (∑ a, (K a)ᴴ * K a = 1) ∧ ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ

omit [Fintype n] in
theorem single_eq_diagonal (i : n) :
    Matrix.single i i (1 : ℂ) = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · by_cases h : i = a <;> simp [h, eq_comm]
  · rcases eq_or_ne i a with rfl | hia
    · simp [hab]
    · simp [hab, hia]

theorem dephase_isCPTP : IsCPTP (n := n) dephase := by
  refine ⟨n, inferInstance, fun i => Matrix.single i i 1, ?_, ?_⟩
  · have h : ∀ i : n, (Matrix.single i i (1 : ℂ))ᴴ * Matrix.single i i 1
        = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
      intro i
      rw [single_eq_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases h : i = a <;> simp [Pi.single_apply, h]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    ext a b
    rw [Matrix.sum_apply]
    by_cases hab : a = b
    · subst hab
      simp [Pi.single_apply, Finset.sum_ite_eq]
    · simp [hab]
  · intro X
    have h : ∀ i : n, Matrix.single i i (1 : ℂ) * X * (Matrix.single i i (1 : ℂ))ᴴ
        = Matrix.diagonal (Pi.single i (1 : ℂ)) * X * Matrix.diagonal (Pi.single i (1 : ℂ)) := by
      intro i
      rw [single_eq_diagonal, Matrix.diagonal_conjTranspose]
      congr 2
      funext a
      by_cases h : i = a <;> simp [Pi.single_apply, h]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, dephase, Matrix.diagonal_apply,
      Pi.single_apply]
    by_cases hab : a = b
    · subst hab
      simp [Finset.sum_ite_eq]
    · simp [hab]

theorem unitary_conj_isCPTP (u : unitary (Matrix n n ℂ)) :
    IsCPTP (fun X : Matrix n n ℂ => (u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ)) := by
  refine ⟨PUnit, inferInstance, fun _ => (u : Matrix n n ℂ), ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self u
  · intro X
    simp [Matrix.star_eq_conjTranspose]

omit [Fintype n] in
theorem dephase_diagonal (d : n → ℂ) : dephase (Matrix.diagonal d) = Matrix.diagonal d := by
  ext i j
  by_cases h : i = j <;> simp [dephase, Matrix.diagonal, h]

/-- The dephasing channel is self-adjoint for the trace pairing. -/
theorem dephase_trace_selfAdjoint (X Y : Matrix n n ℂ) :
    Matrix.trace (dephase X * Y) = Matrix.trace (X * dephase Y) := by
  simp [dephase, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq,
    apply_ite, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- A positive definite matrix has real positive diagonal entries. -/
theorem posDef_diag_re {A : Matrix n n ℂ} (hA : A.PosDef) (i : n) :
    0 < (A i i).re ∧ A i i = ((A i i).re : ℂ) := by
  have h := hA.diag_pos (i := i)
  rw [Complex.lt_def] at h
  refine ⟨by simpa using h.1, ?_⟩
  apply Complex.ext <;> simp [← h.2]

theorem isDensity_dephase {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) : IsDensity (dephase ρ) := by
  obtain ⟨hpd, htr⟩ := hρ
  constructor
  · have : dephase ρ = Matrix.diagonal (fun i => (((ρ i i).re : ℝ) : ℂ)) := by
      rw [dephase]
      congr 1
      funext i
      exact (posDef_diag_re hpd i).2
    rw [this]
    refine Matrix.PosDef.diagonal fun i => ?_
    rw [Complex.lt_def]
    simpa using (posDef_diag_re hpd i).1
  · rw [dephase, Matrix.trace_diagonal, ← htr, Matrix.trace]
    rfl

/-- **Data processing for the dephasing channel**: for an arbitrary faithful state `ρ` and a
faithful state `σ` which is diagonal in the measurement basis, the relative entropy does not
increase under the (CPTP) completely dephasing channel. -/
theorem data_processing_dephasing {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hdiag : dephase σ = σ) :
    relEntropy (dephase ρ) (dephase σ) ≤ relEntropy ρ σ := by
  have hEρ : IsDensity (dephase ρ) := isDensity_dephase hρ
  -- `σ` and `dephase ρ` are diagonal with positive entries, hence so are their logarithms
  have hlog_diag : ∀ τ : Matrix n n ℂ, IsDensity τ → dephase τ = τ → dephase (logM τ) = logM τ := by
    intro τ hτ hd
    have he : τ = Matrix.diagonal (fun i => (((τ i i).re : ℝ) : ℂ)) := by
      conv_lhs => rw [← hd]
      unfold dephase
      congr 1
      funext i
      exact (posDef_diag_re hτ.1 i).2
    rw [he, logM, cfc_diagonal, dephase_diagonal]
  have hlogσ := hlog_diag σ hσ hdiag
  have hlogEρ := hlog_diag (dephase ρ) hEρ (dephase_diagonal _)
  exact data_processing_condExp dephase_trace_selfAdjoint hρ hEρ hdiag hlogσ hlogEρ

/-! ### Measure-and-prepare (classical) channels -/

/-- The relative entropy of two diagonal states is the classical Kullback-Leibler divergence of
their diagonals. -/
theorem relEntropy_diagonal (p q : n → ℝ) :
    relEntropy (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ)))
      = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  rw [relEntropy, logM, logM, cfc_diagonal, cfc_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.trace_diagonal]
  have h1 : ∑ i, ((p i : ℂ) * (Real.log (p i) : ℂ)) = ((∑ i, p i * Real.log (p i) : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ∑ i, ((p i : ℂ) * (Real.log (q i) : ℂ)) = ((∑ i, p i * Real.log (q i) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, Complex.ofReal_re, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
  rw [Real.log_div one_ne_zero hx.ne', Real.log_one, zero_sub] at h
  linarith

/-- **Classical data processing inequality** (log-sum inequality): the Kullback-Leibler
divergence does not increase under a column-stochastic map `T`. -/
omit [DecidableEq n] in
theorem classical_dpi {m : Type u} [Fintype m] {T : m → n → ℝ} (hT : ∀ j i, 0 ≤ T j i)
    (hTcol : ∀ i, ∑ j, T j i = 1)
    {p q : n → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hTp : ∀ j, 0 < ∑ i, T j i * p i) (hTq : ∀ j, 0 < ∑ i, T j i * q i) :
    ∑ j, (∑ i, T j i * p i) * (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i))
      ≤ ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  have key : ∀ j : m, (∑ i, T j i * p i) *
      (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i))
      ≤ ∑ i, T j i * p i * (Real.log (p i) - Real.log (q i)) := by
    intro j
    set A := ∑ i, T j i * p i with hA
    set B := ∑ i, T j i * q i with hB
    have hApos := hTp j
    have hBpos := hTq j
    have step : ∀ i ∈ Finset.univ, T j i * p i - T j i * q i * (A / B)
        ≤ T j i * p i * (Real.log (p i) - Real.log (q i))
          - T j i * p i * (Real.log A - Real.log B) := by
      intro i _
      rcases eq_or_lt_of_le (hT j i) with h0 | hpos
      · simp [← h0]
      · set a := T j i * p i with ha
        set b := T j i * q i with hb
        have hapos : 0 < a := mul_pos hpos (hp i)
        have hbpos : 0 < b := mul_pos hpos (hq i)
        have hx : 0 < a * B / (b * A) := by positivity
        have hlog := one_sub_inv_le_log hx
        have hexp : Real.log (a * B / (b * A))
            = (Real.log (p i) - Real.log (q i)) - (Real.log A - Real.log B) := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_mul hapos.ne' hBpos.ne',
            Real.log_mul hbpos.ne' hApos.ne', ha, hb,
            Real.log_mul hpos.ne' (hp i).ne', Real.log_mul hpos.ne' (hq i).ne']
          ring
        rw [hexp] at hlog
        have h2 : a * (1 - 1 / (a * B / (b * A))) = a - b * (A / B) := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left hlog hapos.le]
    have hsum := Finset.sum_le_sum step
    have hL : ∑ i, (T j i * p i - T j i * q i * (A / B)) = A - B * (A / B) := by
      rw [Finset.sum_sub_distrib, ← hA, ← Finset.sum_mul, ← hB]
    have hR : ∑ i, (T j i * p i * (Real.log (p i) - Real.log (q i))
        - T j i * p i * (Real.log A - Real.log B))
        = (∑ i, T j i * p i * (Real.log (p i) - Real.log (q i)))
          - A * (Real.log A - Real.log B) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hA]
    rw [hL, hR] at hsum
    have hBA : B * (A / B) = A := by
      rw [mul_comm, div_mul_cancel₀ _ hBpos.ne']
    rw [hBA, sub_self] at hsum
    linarith
  calc ∑ j, (∑ i, T j i * p i) * (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i))
      ≤ ∑ j, ∑ i, T j i * p i * (Real.log (p i) - Real.log (q i)) :=
        Finset.sum_le_sum fun j _ => key j
    _ = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcongr : ∀ j : m, T j i * p i * (Real.log (p i) - Real.log (q i))
            = T j i * (p i * (Real.log (p i) - Real.log (q i))) := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => hcongr j), ← Finset.sum_mul, hTcol i, one_mul]

omit [Fintype n] in
theorem single_conjTranspose {m : Type u} [DecidableEq m] (i : m) (j : n) (c : ℂ) :
    (Matrix.single i j c)ᴴ = Matrix.single j i (star c) := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply, RCLike.star_def]
  by_cases h1 : i = b <;> by_cases h2 : j = a <;> simp [h1, h2]

theorem sum_single_diag (d : n → ℂ) : ∑ i, Matrix.single i i (d i) = Matrix.diagonal d := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp [Finset.sum_ite_eq, eq_comm]
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun i _ => if_neg (by rintro ⟨rfl, rfl⟩; exact hab rfl)

omit [Fintype n] in
theorem sum_single_const {m : Type u} [Fintype m] (i : n) (f : m → ℂ) :
    ∑ j, Matrix.single i i (f j) = Matrix.single i i (∑ j, f j) := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = a ∧ i = b <;> simp [h]

/-- The measure-and-prepare channel attached to a column-stochastic matrix `T`: measure in the
computational basis, then prepare the classical state obtained by pushing the outcome
distribution through `T`. -/
noncomputable def classicalChannel {m : Type u} [Fintype m] [DecidableEq m] (T : m → n → ℝ)
    (X : Matrix n n ℂ) : Matrix m m ℂ :=
  Matrix.diagonal (fun j => ∑ i, (T j i : ℂ) * X i i)

theorem classicalChannel_isCPTP {m : Type u} [Fintype m] [DecidableEq m] {T : m → n → ℝ}
    (hT : ∀ j i, 0 ≤ T j i) (hTcol : ∀ i, ∑ j, T j i = 1) : IsCPTP (classicalChannel T) := by
  refine ⟨m × n, inferInstance,
    fun a => Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ), ?_, ?_⟩
  · have h : ∀ a : m × n,
        (Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ))ᴴ
          * Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ)
        = Matrix.single a.2 a.2 ((T a.1 a.2 : ℝ) : ℂ) := by
      rintro ⟨j, i⟩
      rw [single_conjTranspose, Matrix.single_mul_single_same]
      congr 1
      have : ((Real.sqrt (T j i) : ℝ) : ℂ) * ((Real.sqrt (T j i) : ℝ) : ℂ)
          = ((Real.sqrt (T j i) * Real.sqrt (T j i) : ℝ) : ℂ) := by push_cast; ring
      rw [RCLike.star_def, Complex.conj_ofReal, this, Real.mul_self_sqrt (hT j i)]
    rw [Finset.sum_congr rfl (fun a _ => h a), Fintype.sum_prod_type, Finset.sum_comm]
    have h2 : ∀ i : n, ∑ j : m, Matrix.single i i ((T j i : ℝ) : ℂ)
        = Matrix.single i i (1 : ℂ) := by
      intro i
      rw [sum_single_const]
      congr 1
      rw [← Complex.ofReal_sum, hTcol i, Complex.ofReal_one]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    have := sum_single_diag (n := n) (fun _ => (1 : ℂ))
    rw [this, Matrix.diagonal_one]
  · intro X
    have h : ∀ a : m × n,
        Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ) * X
          * (Matrix.single a.1 a.2 ((Real.sqrt (T a.1 a.2) : ℝ) : ℂ))ᴴ
        = Matrix.single a.1 a.1 (((T a.1 a.2 : ℝ) : ℂ) * X a.2 a.2) := by
      rintro ⟨j, i⟩
      rw [single_conjTranspose, Matrix.single_mul_mul_single]
      congr 1
      have hsq : ((Real.sqrt (T j i) : ℝ) : ℂ) * ((Real.sqrt (T j i) : ℝ) : ℂ)
          = ((T j i : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hT j i)]
      rw [RCLike.star_def, Complex.conj_ofReal]
      calc ((Real.sqrt (T j i) : ℝ) : ℂ) * X i i * ((Real.sqrt (T j i) : ℝ) : ℂ)
          = (((Real.sqrt (T j i) : ℝ) : ℂ) * ((Real.sqrt (T j i) : ℝ) : ℂ)) * X i i := by ring
        _ = ((T j i : ℝ) : ℂ) * X i i := by rw [hsq]
    rw [Finset.sum_congr rfl (fun a _ => h a), Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun j _ => sum_single_const j _)]
    rw [sum_single_diag]
    rfl

/-- **Data processing for measure-and-prepare channels**: for an arbitrary faithful state `ρ`
and a faithful state `σ` which is diagonal in the measurement basis, the relative entropy does
not increase under the CPTP map `classicalChannel T`. -/
theorem data_processing_measure_prepare {m : Type u} [Fintype m] [DecidableEq m] {T : m → n → ℝ}
    (hT : ∀ j i, 0 ≤ T j i) (hTcol : ∀ i, ∑ j, T j i = 1) (hTrow : ∀ j, ∃ i, 0 < T j i)
    {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) (hdiag : dephase σ = σ) :
    relEntropy (classicalChannel T ρ) (classicalChannel T σ) ≤ relEntropy ρ σ := by
  set p : n → ℝ := fun i => (ρ i i).re with hpdef
  set q : n → ℝ := fun i => (σ i i).re with hqdef
  have hp : ∀ i, 0 < p i := fun i => (posDef_diag_re hρ.1 i).1
  have hq : ∀ i, 0 < q i := fun i => (posDef_diag_re hσ.1 i).1
  have hρe : ∀ i, ρ i i = ((p i : ℝ) : ℂ) := fun i => (posDef_diag_re hρ.1 i).2
  have hσe : ∀ i, σ i i = ((q i : ℝ) : ℂ) := fun i => (posDef_diag_re hσ.1 i).2
  have hTp : ∀ j, 0 < ∑ i, T j i * p i := by
    intro j
    obtain ⟨i, hi⟩ := hTrow j
    calc (0 : ℝ) < T j i * p i := mul_pos hi (hp i)
      _ ≤ ∑ i, T j i * p i :=
        Finset.single_le_sum (f := fun i => T j i * p i)
          (fun i _ => mul_nonneg (hT j i) (hp i).le) (Finset.mem_univ i)
  have hTq : ∀ j, 0 < ∑ i, T j i * q i := by
    intro j
    obtain ⟨i, hi⟩ := hTrow j
    calc (0 : ℝ) < T j i * q i := mul_pos hi (hq i)
      _ ≤ ∑ i, T j i * q i :=
        Finset.single_le_sum (f := fun i => T j i * q i)
          (fun i _ => mul_nonneg (hT j i) (hq i).le) (Finset.mem_univ i)
  have hch : ∀ (τ : Matrix n n ℂ) (r : n → ℝ), (∀ i, τ i i = ((r i : ℝ) : ℂ)) →
      classicalChannel T τ = Matrix.diagonal (fun j => (((∑ i, T j i * r i : ℝ)) : ℂ)) := by
    intro τ r hτ
    rw [classicalChannel]
    congr 1
    funext j
    rw [show ((∑ i, T j i * r i : ℝ) : ℂ) = ∑ i, ((T j i * r i : ℝ) : ℂ) from
      Complex.ofReal_sum _ _]
    exact Finset.sum_congr rfl fun i _ => by rw [hτ i, ← Complex.ofReal_mul]
  have hdeρ : dephase ρ = Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) := by
    rw [dephase]
    congr 1
    funext i
    exact hρe i
  have hdeσ : dephase σ = Matrix.diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    rw [dephase]
    congr 1
    funext i
    exact hσe i
  calc relEntropy (classicalChannel T ρ) (classicalChannel T σ)
      = ∑ j, (∑ i, T j i * p i) *
          (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i)) := by
        rw [hch ρ p hρe, hch σ q hσe, relEntropy_diagonal]
    _ ≤ ∑ i, p i * (Real.log (p i) - Real.log (q i)) :=
        classical_dpi hT hTcol hp hq hTp hTq
    _ = relEntropy (dephase ρ) (dephase σ) := by rw [hdeρ, hdeσ, relEntropy_diagonal]
    _ ≤ relEntropy ρ σ := data_processing_dephasing hρ hσ hdiag

/-! ### Measurement in an arbitrary orthonormal basis -/

theorem conj_conj_star_cancel (u : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    star (u : Matrix n n ℂ) * ((u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ))
      * (u : Matrix n n ℂ) = X := by
  have hus : star (u : Matrix n n ℂ) * (u : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self u
  simp only [← mul_assoc]
  rw [hus, one_mul, mul_assoc, hus, mul_one]

theorem conj_star_conj_cancel (u : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    (u : Matrix n n ℂ) * (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ))
      * star (u : Matrix n n ℂ) = X := by
  have hsu : (u : Matrix n n ℂ) * star (u : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self u
  simp only [← mul_assoc]
  rw [hsu, one_mul, mul_assoc, hsu, mul_one]

/-- Conjugation by a unitary maps faithful states to faithful states. -/
theorem isDensity_conj (u : unitary (Matrix n n ℂ)) {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) :
    IsDensity ((u : Matrix n n ℂ) * ρ * star (u : Matrix n n ℂ)) := by
  obtain ⟨hpd, htr⟩ := hρ
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (u : Matrix n n ℂ) := IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self u)
    rw [Matrix.star_eq_conjTranspose]
    exact hpd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)
  · rw [trace_conj_eq, htr]

/-- Measurement in the orthonormal basis formed by the columns of a unitary `u`: the completely
dephasing channel conjugated by `u`. -/
noncomputable def dephaseIn (u : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (u : Matrix n n ℂ) * dephase (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ))
    * star (u : Matrix n n ℂ)

theorem star_conj (u : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    star ((u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * star X * star (u : Matrix n n ℂ) := by
  simp [Matrix.star_mul, mul_assoc]

theorem dephaseIn_isCPTP (u : unitary (Matrix n n ℂ)) : IsCPTP (dephaseIn (n := n) u) := by
  obtain ⟨ι, hι, K, hsum, hrep⟩ := dephase_isCPTP (n := n)
  have hsu : (u : Matrix n n ℂ) * star (u : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self u
  refine ⟨ι, hι, fun a => (u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ), ?_, ?_⟩
  · have key : ∀ a, ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))ᴴ
        * ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))
        = (u : Matrix n n ℂ) * ((K a)ᴴ * K a) * star (u : Matrix n n ℂ) := by
      intro a
      rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_conj,
        conj_mul_conj]
    calc ∑ a, ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))ᴴ
            * ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))
        = ∑ a, (u : Matrix n n ℂ) * ((K a)ᴴ * K a) * star (u : Matrix n n ℂ) :=
          Finset.sum_congr rfl fun a _ => key a
      _ = (u : Matrix n n ℂ) * (∑ a, (K a)ᴴ * K a) * star (u : Matrix n n ℂ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = 1 := by rw [hsum, mul_one, hsu]
  · intro X
    have key : ∀ a, ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ)) * X
          * ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))ᴴ
        = (u : Matrix n n ℂ)
            * (K a * (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ)) * (K a)ᴴ)
            * star (u : Matrix n n ℂ) := by
      intro a
      rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_conj]
      conv_lhs => rw [← conj_star_conj_cancel u X]
      rw [conj_mul_conj, conj_mul_conj]
    rw [dephaseIn, hrep (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ)), Finset.mul_sum,
      Finset.sum_mul]
    exact (Finset.sum_congr rfl fun a _ => key a).symm

/-- **Data processing for a measurement channel in an arbitrary orthonormal basis**: if the
faithful state `σ` is diagonal in the measurement basis, then measuring cannot increase the
relative entropy. -/
theorem data_processing_dephaseIn (u : unitary (Matrix n n ℂ)) {ρ σ : Matrix n n ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hfix : dephaseIn u σ = σ) :
    relEntropy (dephaseIn u ρ) (dephaseIn u σ) ≤ relEntropy ρ σ := by
  have hstar : ((star u : unitary (Matrix n n ℂ)) : Matrix n n ℂ)
      = star (u : Matrix n n ℂ) := rfl
  have hρ' : IsDensity (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)) := by
    have := isDensity_conj (star u) hρ
    rwa [hstar, star_star] at this
  have hσ' : IsDensity (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ)) := by
    have := isDensity_conj (star u) hσ
    rwa [hstar, star_star] at this
  have hfix' : dephase (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ))
      = star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ) := by
    conv_rhs => rw [← hfix]
    rw [dephaseIn, conj_conj_star_cancel]
  have hdρ : IsDensity (dephase (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ))) :=
    isDensity_dephase hρ'
  have hdσ : IsDensity (dephase (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ))) :=
    isDensity_dephase hσ'
  calc relEntropy (dephaseIn u ρ) (dephaseIn u σ)
      = relEntropy (dephase (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)))
          (dephase (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ))) := by
        rw [dephaseIn, dephaseIn, relEntropy_unitary_conj u hdρ.1.1 hdσ.1.1]
    _ ≤ relEntropy (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ))
          (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ)) :=
        data_processing_dephasing hρ' hσ' hfix'
    _ = relEntropy ρ σ := by
        have := relEntropy_unitary_conj (star u) hρ.1.1 hσ.1.1
        rwa [hstar, star_star] at this

/-- A state which is diagonal in the measurement basis is left unchanged by the measurement. -/
theorem dephaseIn_of_conj_diagonal (u : unitary (Matrix n n ℂ)) (d : n → ℂ)
    {σ : Matrix n n ℂ}
    (h : σ = (u : Matrix n n ℂ) * Matrix.diagonal d * star (u : Matrix n n ℂ)) :
    dephaseIn u σ = σ := by
  rw [dephaseIn, h, conj_conj_star_cancel, dephase_diagonal]

/-- Measuring `σ` in its own eigenbasis leaves it unchanged. -/
theorem dephaseIn_eigenbasis_eq_self {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    dephaseIn hσ.eigenvectorUnitary σ = σ :=
  dephaseIn_of_conj_diagonal _ _ (spectral_decomp hσ)

/-- **Data processing for the measurement in the eigenbasis of `σ`**: for arbitrary faithful
states `ρ` and `σ`, measuring `ρ` in an eigenbasis of `σ` (a CPTP channel, see
`dephaseIn_isCPTP`) cannot increase the relative entropy with respect to `σ`. -/
theorem data_processing_measure_eigenbasis {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ)
    (hσ : IsDensity σ) :
    relEntropy (dephaseIn hσ.1.1.eigenvectorUnitary ρ) σ ≤ relEntropy ρ σ := by
  have hfix : dephaseIn hσ.1.1.eigenvectorUnitary σ = σ := dephaseIn_eigenbasis_eq_self hσ.1.1
  have h := data_processing_dephaseIn hσ.1.1.eigenvectorUnitary hρ hσ hfix
  rwa [hfix] at h

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

/-
Full data processing inequality for the Umegaki relative entropy under CPTP maps.

The proof follows an integral representation of the relative entropy: for positive definite
`P`, `Q` of unit trace,

  `D(P‖Q) = ∫_0^∞ χ_t(P,Q) / (1+t)^2 dt`,

where `χ_t(P,Q) = ⟨Δ, 𝕄_t^{-1} Δ⟩` with `Δ = P - Q` and `𝕄_t` the (positive definite)
superoperator `X ↦ t • P X + X Q`.  Each `χ_t` is monotone under CPTP maps by a variational
argument together with the Kadison-Schwarz inequality for the (unital, completely positive)
adjoint channel, and the data processing inequality follows by integration.
-/
import RequestProject.QuantumRelativeEntropy

namespace QI

open Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

universe u

variable {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Traces of products of positive semidefinite matrices -/

omit [DecidableEq n] in
theorem trace_mul_posSemidef_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, hC⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hB
  have h1 : Matrix.trace (A * B) = Matrix.trace (C * A * Cᴴ) := by
    rw [hC, ← mul_assoc, Matrix.trace_mul_comm (A * Cᴴ) C, mul_assoc]
  have h3 := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [h1]
  simpa using (Complex.le_def.mp h3).1

/-! ### Kraus channels and their adjoints -/

/-- The channel attached to a Kraus family. -/
noncomputable def krausMap {ι : Type u} [Fintype ι] (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) :
    Matrix m m ℂ := ∑ a, K a * X * (K a)ᴴ

/-- The adjoint (Heisenberg picture) map attached to a Kraus family. -/
noncomputable def krausAdj {ι : Type u} [Fintype ι] (K : ι → Matrix m n ℂ) (Y : Matrix m m ℂ) :
    Matrix n n ℂ := ∑ a, (K a)ᴴ * Y * K a

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem krausMap_sub {ι : Type u} [Fintype ι] (K : ι → Matrix m n ℂ) (X Y : Matrix n n ℂ) :
    krausMap K (X - Y) = krausMap K X - krausMap K Y := by
  simp only [krausMap, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem krausAdj_conjTranspose {ι : Type u} [Fintype ι] (K : ι → Matrix m n ℂ)
    (Y : Matrix m m ℂ) : (krausAdj K Y)ᴴ = krausAdj K Yᴴ := by
  simp only [krausAdj, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
/-- Trace duality between a Kraus channel and its adjoint. -/
theorem trace_krausMap_mul {ι : Type u} [Fintype ι] (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ)
    (Y : Matrix m m ℂ) :
    Matrix.trace (krausMap K X * Y) = Matrix.trace (X * krausAdj K Y) := by
  simp only [krausMap, krausAdj, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_assoc X]

omit [DecidableEq m] in
/-- **Kadison-Schwarz inequality** for the adjoint of a trace preserving Kraus channel. -/
theorem krausAdj_schwarz {ι : Type u} [Fintype ι] {K : ι → Matrix m n ℂ}
    (hK : ∑ a, (K a)ᴴ * K a = 1) (Y : Matrix m m ℂ) :
    (krausAdj K (Yᴴ * Y) - (krausAdj K Y)ᴴ * krausAdj K Y).PosSemidef := by
  set R := krausAdj K Y with hR
  have h2 : ∑ a, (K a)ᴴ * Y * K a = R := rfl
  have h1 : ∑ a, (K a)ᴴ * Yᴴ * K a = Rᴴ := by rw [hR, krausAdj_conjTranspose]; rfl
  have h3 : krausAdj K (Yᴴ * Y) = ∑ a, (K a)ᴴ * (Yᴴ * Y) * K a := rfl
  have key : krausAdj K (Yᴴ * Y) - Rᴴ * R
      = ∑ a, (Y * K a - K a * R)ᴴ * (Y * K a - K a * R) := by
    have expand : ∀ a : ι, (Y * K a - K a * R)ᴴ * (Y * K a - K a * R)
        = (K a)ᴴ * (Yᴴ * Y) * K a - ((K a)ᴴ * Yᴴ * K a) * R - Rᴴ * ((K a)ᴴ * Y * K a)
          + Rᴴ * ((K a)ᴴ * K a) * R := by
      intro a
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [Finset.sum_congr rfl fun a _ => expand a]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [h1, h2, hK, Matrix.mul_one, h3]
    abel
  rw [key]
  exact Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_conjTranspose_mul_self _

/-! ### The Sylvester equation `t • P W + W Q = P - Q` -/

/-- The solution of the Sylvester equation `t • (P * W) + W * Q = D`, written in terms of a pair
of diagonalising unitaries. -/
noncomputable def sylvAux (t : ℝ) (U V : Matrix n n ℂ) (p q : n → ℝ) (D : Matrix n n ℂ) :
    Matrix n n ℂ :=
  U * Matrix.of (fun j k => (star U * D * V) j k / ((t * p j + q k : ℝ) : ℂ)) * star V

private theorem aux_entry (r d : ℝ) (z : ℂ) :
    star ((r : ℂ) * z) * ((r : ℂ) * z / (d : ℂ)) = (((r ^ 2 / d) * Complex.normSq z : ℝ) : ℂ) := by
  have h1 : star ((r : ℂ) * z) = (r : ℂ) * star z := by rw [star_mul']; simp
  have h2 : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [h1]
  push_cast
  rw [div_mul_eq_mul_div, ← h2]
  ring

theorem sylvAux_sylvester {t : ℝ} (ht : 0 < t) {U V : Matrix n n ℂ} (hU : star U * U = 1)
    (hUU : U * star U = 1) (hV : star V * V = 1) (hVV : V * star V = 1) {p q : n → ℝ}
    (hp : ∀ j, 0 < p j) (hq : ∀ k, 0 < q k) {P Q : Matrix n n ℂ}
    (hPd : P = U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U)
    (hQd : Q = V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V) :
    (t : ℂ) • (P * sylvAux t U V p q (P - Q)) + sylvAux t U V p q (P - Q) * Q = P - Q := by
  set C := star U * (P - Q) * V with hC
  set M : Matrix n n ℂ := Matrix.of (fun j k => C j k / ((t * p j + q k : ℝ) : ℂ)) with hM
  have hdiag : (t : ℂ) • (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * M)
      + M * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) = C := by
    ext j k
    have hpos : (0 : ℝ) < t * p j + q k := by
      have h1 : 0 < t * p j := mul_pos ht (hp j)
      have h2 := hq k
      linarith
    have hne : ((t * p j + q k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      hM, Matrix.of_apply, smul_eq_mul]
    field_simp
    push_cast
    ring
  calc (t : ℂ) • (P * (U * M * star V)) + (U * M * star V) * Q
      = U * ((t : ℂ) • (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * M)
          + M * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ))) * star V := by
        rw [hPd, hQd, Matrix.mul_add, Matrix.add_mul]
        congr 1
        · rw [Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          calc U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U * (U * M * star V)
              = U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * (star U * U) * M * star V := by
                noncomm_ring
            _ = U * (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * M) * star V := by
                rw [hU]; noncomm_ring
        · calc U * M * star V * (V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V)
              = U * M * (star V * V) * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V := by
                noncomm_ring
            _ = U * (M * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ))) * star V := by
                rw [hV]; noncomm_ring
    _ = U * C * star V := by rw [hdiag]
    _ = P - Q := by
        rw [hC]
        calc U * (star U * (P - Q) * V) * star V
            = (U * star U) * (P - Q) * (V * star V) := by noncomm_ring
          _ = P - Q := by rw [hUU, hVV, one_mul, mul_one]

theorem trace_mul_sylvAux_re {t : ℝ} {U V : Matrix n n ℂ} (hU : star U * U = 1)
    (hV : star V * V = 1) {p q : n → ℝ} {P Q : Matrix n n ℂ}
    (hPd : P = U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U)
    (hQd : Q = V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V) :
    (Matrix.trace ((P - Q)ᴴ * sylvAux t U V p q (P - Q))).re
      = ∑ j, ∑ k, (p j - q k) ^ 2 / (t * p j + q k) * Complex.normSq ((star U * V) j k) := by
  set C := star U * (P - Q) * V with hC
  set M : Matrix n n ℂ := Matrix.of (fun j k => C j k / ((t * p j + q k : ℝ) : ℂ)) with hM
  have hWdef : sylvAux t U V p q (P - Q) = U * M * star V := rfl
  have hCeq : C = Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * (star U * V)
      - (star U * V) * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) := by
    rw [hC, hPd, hQd]
    calc star U * (U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U
            - V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V) * V
        = (star U * U) * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * (star U * V)
          - (star U * V) * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * (star V * V) := by
          noncomm_ring
      _ = _ := by rw [hU, hV, one_mul, mul_one]
  have hCentry : ∀ j k, C j k = ((p j - q k : ℝ) : ℂ) * (star U * V) j k := by
    intro j k
    rw [hCeq]
    simp [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have htr : Matrix.trace ((P - Q)ᴴ * (U * M * star V)) = Matrix.trace (Cᴴ * M) := by
    have h1 : Cᴴ = star V * (P - Q)ᴴ * U := by
      rw [hC]
      simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [h1]
    calc Matrix.trace ((P - Q)ᴴ * (U * M * star V))
        = Matrix.trace (star V * ((P - Q)ᴴ * (U * M))) := by
          rw [← Matrix.mul_assoc ((P - Q)ᴴ) (U * M) (star V), Matrix.trace_mul_comm]
      _ = Matrix.trace (star V * (P - Q)ᴴ * U * M) := by simp only [Matrix.mul_assoc]
  have hval : Matrix.trace (Cᴴ * M)
      = ((∑ k, ∑ j, (p j - q k) ^ 2 / (t * p j + q k)
          * Complex.normSq ((star U * V) j k) : ℝ) : ℂ) := by
    rw [Matrix.trace, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, hM]
    simp only [Matrix.of_apply]
    rw [hCentry j k]
    exact aux_entry _ _ _
  rw [hWdef, htr, hval, Complex.ofReal_re, Finset.sum_comm]

/-- The solution of the Sylvester equation `t • (P * W) + W * Q = P - Q`, written in the
eigenbases of `P` and `Q`. -/
noncomputable def sylv (t : ℝ) {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    Matrix n n ℂ :=
  sylvAux t (hP.eigenvectorUnitary : Matrix n n ℂ) (hQ.eigenvectorUnitary : Matrix n n ℂ)
    hP.eigenvalues hQ.eigenvalues (P - Q)

/-- The quantity `χ_t(P,Q) = ⟨Δ, 𝕄_t^{-1} Δ⟩`, `Δ = P - Q`. -/
noncomputable def chi (t : ℝ) {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ℝ := (Matrix.trace ((P - Q)ᴴ * sylv t hP hQ)).re

theorem sylv_sylvester {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef)
    (hQ : Q.PosDef) :
    (t : ℂ) • (P * sylv t hP.1 hQ.1) + sylv t hP.1 hQ.1 * Q = P - Q :=
  sylvAux_sylvester ht (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _)
    (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _) hP.eigenvalues_pos
    hQ.eigenvalues_pos (spectral_decomp hP.1) (spectral_decomp hQ.1)

/-- The spectral expression of `χ_t`. -/
theorem chi_eq_sum {t : ℝ} {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    chi t hP hQ = ∑ j, ∑ k,
      (hP.eigenvalues j - hQ.eigenvalues k) ^ 2 / (t * hP.eigenvalues j + hQ.eigenvalues k) *
        Complex.normSq ((star (hP.eigenvectorUnitary : Matrix n n ℂ)
          * (hQ.eigenvectorUnitary : Matrix n n ℂ)) j k) :=
  trace_mul_sylvAux_re (Unitary.coe_star_mul_self _) (Unitary.coe_star_mul_self _)
    (spectral_decomp hP) (spectral_decomp hQ)

/-! ### The variational bound -/

/-- The quadratic form `Y ↦ ⟨Y, 𝕄_t Y⟩`. -/
noncomputable def quadForm (t : ℝ) (P Q Y : Matrix n n ℂ) : ℝ :=
  t * (Matrix.trace (Yᴴ * P * Y)).re + (Matrix.trace (Yᴴ * Y * Q)).re

omit [DecidableEq n] in
theorem trace_conjT_re (A B : Matrix n n ℂ) :
    (Matrix.trace (Aᴴ * B)).re = (Matrix.trace (Bᴴ * A)).re := by
  have h := Matrix.trace_conjTranspose (Aᴴ * B)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  rw [h]
  simp

omit [DecidableEq n] in
theorem quadForm_nonneg {t : ℝ} (ht : 0 ≤ t) {P Q : Matrix n n ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (Y : Matrix n n ℂ) : 0 ≤ quadForm t P Q Y := by
  have h1 : (Matrix.trace (Yᴴ * P * Y)).re = (Matrix.trace (P * (Y * Yᴴ))).re := by
    congr 1
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have h2 : (Matrix.trace (Yᴴ * Y * Q)).re = (Matrix.trace (Q * (Yᴴ * Y))).re := by
    congr 1
    rw [Matrix.trace_mul_comm]
  rw [quadForm, h1, h2]
  have p1 := trace_mul_posSemidef_nonneg hP (Matrix.posSemidef_self_mul_conjTranspose Y)
  have p2 := trace_mul_posSemidef_nonneg hQ (Matrix.posSemidef_conjTranspose_mul_self Y)
  have := mul_nonneg ht p1
  linarith

omit [DecidableEq n] in
/-- Expansion of the quadratic form along a difference. -/
theorem quadForm_sub (t : ℝ) {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (Y W : Matrix n n ℂ) :
    quadForm t P Q (Y - W) = quadForm t P Q Y
      - 2 * (t * (Matrix.trace (Yᴴ * (P * W))).re + (Matrix.trace (Yᴴ * (W * Q))).re)
      + quadForm t P Q W := by
  unfold quadForm
  have e1 : (Y - W)ᴴ * P * (Y - W) = Yᴴ * P * Y - Yᴴ * P * W - Wᴴ * P * Y + Wᴴ * P * W := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
  have e2 : (Y - W)ᴴ * (Y - W) * Q = Yᴴ * Y * Q - Yᴴ * W * Q - Wᴴ * Y * Q + Wᴴ * W * Q := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
  have c1 : (Matrix.trace (Wᴴ * (P * Y))).re = (Matrix.trace (Yᴴ * (P * W))).re := by
    rw [trace_conjT_re W (P * Y), Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  have c2 : (Matrix.trace (Wᴴ * (Y * Q))).re = (Matrix.trace (Yᴴ * (W * Q))).re := by
    rw [trace_conjT_re W (Y * Q), Matrix.conjTranspose_mul, hQ.eq]
    congr 1
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc]
  rw [e1, e2]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, Matrix.mul_assoc]
  rw [c1, c2]
  ring

/-- The bilinear pairing of an arbitrary `Y` with the Sylvester solution. -/
theorem pairing_sylv {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (Y : Matrix n n ℂ) :
    t * (Matrix.trace (Yᴴ * (P * sylv t hP.1 hQ.1))).re
        + (Matrix.trace (Yᴴ * (sylv t hP.1 hQ.1 * Q))).re
      = (Matrix.trace (Yᴴ * (P - Q))).re := by
  have hsyl := sylv_sylvester ht hP hQ
  have h : Matrix.trace (Yᴴ * (P - Q))
      = (t : ℂ) * Matrix.trace (Yᴴ * (P * sylv t hP.1 hQ.1))
        + Matrix.trace (Yᴴ * (sylv t hP.1 hQ.1 * Q)) := by
    rw [← hsyl, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  rw [h]
  simp [Complex.add_re]

/-- The value of the quadratic form at the Sylvester solution is `χ_t`. -/
theorem quadForm_sylv {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    quadForm t P Q (sylv t hP.1 hQ.1) = chi t hP.1 hQ.1 := by
  have h := pairing_sylv ht hP hQ (sylv t hP.1 hQ.1)
  rw [chi, trace_conjT_re (P - Q) (sylv t hP.1 hQ.1), ← h, quadForm]
  simp only [Matrix.mul_assoc]

/-- The variational upper bound: `χ_t` dominates `2⟨Y,Δ⟩ - ⟨Y, 𝕄_t Y⟩` for every `Y`. -/
theorem le_chi {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (Y : Matrix n n ℂ) :
    2 * (Matrix.trace (Yᴴ * (P - Q))).re - quadForm t P Q Y ≤ chi t hP.1 hQ.1 := by
  have h0 : 0 ≤ quadForm t P Q (Y - sylv t hP.1 hQ.1) :=
    quadForm_nonneg ht.le hP.posSemidef hQ.posSemidef _
  have hexp := quadForm_sub t hP.1 hQ.1 Y (sylv t hP.1 hQ.1)
  rw [pairing_sylv ht hP hQ Y, quadForm_sylv ht hP hQ] at hexp
  linarith

/-- The variational bound is attained at the solution of the Sylvester equation. -/
theorem chi_eq {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    chi t hP.1 hQ.1
      = 2 * (Matrix.trace ((sylv t hP.1 hQ.1)ᴴ * (P - Q))).re
        - quadForm t P Q (sylv t hP.1 hQ.1) := by
  have h1 : (Matrix.trace ((sylv t hP.1 hQ.1)ᴴ * (P - Q))).re = chi t hP.1 hQ.1 :=
    (trace_conjT_re (P - Q) (sylv t hP.1 hQ.1)).symm
  rw [h1, quadForm_sylv ht hP hQ]
  ring

/-! ### Monotonicity of `χ_t` under CPTP maps -/

omit [DecidableEq n] in
theorem trace_mul_mono {P X X' : Matrix n n ℂ} (hP : P.PosSemidef) (h : (X' - X).PosSemidef) :
    (Matrix.trace (P * X)).re ≤ (Matrix.trace (P * X')).re := by
  have h2 := trace_mul_posSemidef_nonneg hP h
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h2
  linarith

theorem chi_monotone {t : ℝ} (ht : 0 < t) {ι : Type u} [Fintype ι] {K : ι → Matrix m n ℂ}
    (hK : ∑ a, (K a)ᴴ * K a = 1) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hKP : (krausMap K P).PosDef) (hKQ : (krausMap K Q).PosDef) :
    chi t hKP.1 hKQ.1 ≤ chi t hP.1 hQ.1 := by
  set W := sylv t hKP.1 hKQ.1 with hW
  set Y := krausAdj K W with hY
  have hYH : Yᴴ = krausAdj K Wᴴ := krausAdj_conjTranspose K W
  have ha : (Matrix.trace (Wᴴ * (krausMap K P - krausMap K Q))).re
      = (Matrix.trace (Yᴴ * (P - Q))).re := by
    rw [← krausMap_sub, Matrix.trace_mul_comm, trace_krausMap_mul, ← hYH, Matrix.trace_mul_comm]
  have hb1 : (Matrix.trace (Yᴴ * P * Y)).re ≤ (Matrix.trace (Wᴴ * krausMap K P * W)).re := by
    have e1 : (Matrix.trace (Yᴴ * P * Y)).re = (Matrix.trace (P * (Y * Yᴴ))).re := by
      congr 1
      rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    have e2 : (Matrix.trace (Wᴴ * krausMap K P * W)).re
        = (Matrix.trace (P * krausAdj K (W * Wᴴ))).re := by
      congr 1
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm, trace_krausMap_mul]
    have hpsd : (krausAdj K (W * Wᴴ) - Y * Yᴴ).PosSemidef := by
      have h := krausAdj_schwarz hK Wᴴ
      rw [Matrix.conjTranspose_conjTranspose, ← hYH, Matrix.conjTranspose_conjTranspose] at h
      exact h
    rw [e1, e2]
    exact trace_mul_mono hP.posSemidef hpsd
  have hb2 : (Matrix.trace (Yᴴ * Y * Q)).re ≤ (Matrix.trace (Wᴴ * W * krausMap K Q)).re := by
    have e1 : (Matrix.trace (Yᴴ * Y * Q)).re = (Matrix.trace (Q * (Yᴴ * Y))).re := by
      congr 1
      rw [Matrix.trace_mul_comm]
    have e2 : (Matrix.trace (Wᴴ * W * krausMap K Q)).re
        = (Matrix.trace (Q * krausAdj K (Wᴴ * W))).re := by
      congr 1
      rw [Matrix.trace_mul_comm, trace_krausMap_mul]
    have hpsd : (krausAdj K (Wᴴ * W) - Yᴴ * Y).PosSemidef := by
      have h := krausAdj_schwarz hK W
      rw [← hY] at h
      exact h
    rw [e1, e2]
    exact trace_mul_mono hQ.posSemidef hpsd
  have hb : quadForm t P Q Y ≤ quadForm t (krausMap K P) (krausMap K Q) W := by
    unfold quadForm
    have := mul_le_mul_of_nonneg_left hb1 ht.le
    linarith
  have hce := chi_eq ht hKP hKQ
  have hle := le_chi ht hP hQ Y
  rw [← hW] at hce
  rw [hce, ha]
  linarith

/-! ### The scalar integral -/

/-- The antiderivative of the scalar integrand. -/
private noncomputable def scalarPrim (p q s : ℝ) : ℝ :=
  p * Real.log (s * p + q) - p * Real.log (1 + s) + (p - q) / (1 + s)

private theorem hasDerivAt_scalarPrim {p q : ℝ} (hq : 0 < q) {t : ℝ} (ht : 0 < t)
    (hp : 0 < p) :
    HasDerivAt (scalarPrim p q) ((p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2)) t := by
  have hd1 : (0 : ℝ) < t * p + q := by nlinarith
  have hd2 : (0 : ℝ) < 1 + t := by linarith
  have h1 : HasDerivAt (fun s : ℝ => s * p + q) p t := by
    simpa using ((hasDerivAt_id t).mul_const p).add_const q
  have h2 : HasDerivAt (fun s : ℝ => Real.log (s * p + q)) ((t * p + q)⁻¹ * p) t := by
    simpa [Function.comp] using (Real.hasDerivAt_log (ne_of_gt hd1)).comp t h1
  have h3 : HasDerivAt (fun s : ℝ => (1 : ℝ) + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have h4 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) ((1 + t)⁻¹ * 1) t := by
    simpa [Function.comp] using (Real.hasDerivAt_log (ne_of_gt hd2)).comp t h3
  have h5 : HasDerivAt (fun s : ℝ => (p - q) / (1 + s))
      ((0 * (1 + t) - (p - q) * 1) / (1 + t) ^ 2) t :=
    (hasDerivAt_const t (p - q)).div h3 (ne_of_gt hd2)
  have h6 := ((h2.const_mul p).sub (h4.const_mul p)).add h5
  convert h6 using 1
  field_simp
  ring

private theorem tendsto_scalarPrim {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (scalarPrim p q) atTop (𝓝 (p * Real.log p)) := by
  have hlim0 : Tendsto (fun s : ℝ => (q - p) / (1 + s)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hlim0' : Tendsto (fun s : ℝ => (p - q) / (1 + s)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hlim1 : Tendsto (fun s : ℝ => p + (q - p) / (1 + s)) atTop (𝓝 p) := by
    simpa using tendsto_const_nhds.add hlim0
  have hlim2 : Tendsto (fun s : ℝ => Real.log (p + (q - p) / (1 + s))) atTop (𝓝 (Real.log p)) :=
    (Real.continuousAt_log (ne_of_gt hp)).tendsto.comp hlim1
  have hlim3 : Tendsto (fun s : ℝ => p * Real.log (p + (q - p) / (1 + s)) + (p - q) / (1 + s))
      atTop (𝓝 (p * Real.log p)) := by
    simpa using (hlim2.const_mul p).add hlim0'
  refine hlim3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hd1 : (0 : ℝ) < s * p + q := by nlinarith
  have hd2 : (0 : ℝ) < 1 + s := by linarith
  have heq : p + (q - p) / (1 + s) = (s * p + q) / (1 + s) := by
    field_simp
    ring
  rw [scalarPrim, heq, Real.log_div (ne_of_gt hd1) (ne_of_gt hd2)]
  ring

private theorem continuousWithinAt_scalarPrim {p q : ℝ} (hq : 0 < q) :
    ContinuousWithinAt (scalarPrim p q) (Set.Ici 0) 0 := by
  have h1 : ContinuousAt (fun s : ℝ => p * Real.log (s * p + q)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
    · fun_prop
    · simpa using ne_of_gt hq
  have h2 : ContinuousAt (fun s : ℝ => p * Real.log (1 + s)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
    · fun_prop
    · norm_num
  have h3 : ContinuousAt (fun s : ℝ => (p - q) / (1 + s)) 0 := by
    refine continuousAt_const.div ?_ ?_
    · fun_prop
    · norm_num
  exact ((h1.sub h2).add h3).continuousWithinAt

private theorem scalar_integrand_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2) := by
  have hd1 : (0 : ℝ) < t * p + q := by nlinarith
  have hd2 : (0 : ℝ) < 1 + t := by linarith
  positivity

theorem integral_scalar_chi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in Set.Ioi (0 : ℝ), (p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2)
      = p * Real.log p - p * Real.log q - p + q := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_scalarPrim hq)
    (fun x hx => hasDerivAt_scalarPrim hq hx hp)
    (fun x hx => scalar_integrand_nonneg hp hq hx) (tendsto_scalarPrim hp hq)]
  simp [scalarPrim]
  ring

theorem integrableOn_scalar_chi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun t : ℝ => (p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2))
      (Set.Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_scalarPrim hq)
    (fun _ hx => hasDerivAt_scalarPrim hq hx hp)
    (fun _ hx => scalar_integrand_nonneg hp hq hx) (tendsto_scalarPrim hp hq)

/-! ### The integral formula for the relative entropy -/

/-- The integrand `χ_t/(1+t)²` as a finite sum of scalar integrands. -/
theorem chi_div_eq_sum (t : ℝ) {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    chi t hP hQ / (1 + t) ^ 2
      = ∑ j, ∑ k, Complex.normSq ((star (hP.eigenvectorUnitary : Matrix n n ℂ)
            * (hQ.eigenvectorUnitary : Matrix n n ℂ)) j k)
          * ((hP.eigenvalues j - hQ.eigenvalues k) ^ 2
              / ((t * hP.eigenvalues j + hQ.eigenvalues k) * (1 + t) ^ 2)) := by
  rw [chi_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem integrableOn_chi {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    IntegrableOn (fun t : ℝ => chi t hP.1 hQ.1 / (1 + t) ^ 2) (Set.Ioi (0 : ℝ)) := by
  simp_rw [fun t => chi_div_eq_sum t hP.1 hQ.1]
  refine integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => ?_
  exact (integrableOn_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)).const_mul _

theorem integral_chi_eq {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    (∫ t in Set.Ioi (0 : ℝ), chi t hP.1 hQ.1 / (1 + t) ^ 2)
      = ∑ j, ∑ k, Complex.normSq ((star (hP.1.eigenvectorUnitary : Matrix n n ℂ)
            * (hQ.1.eigenvectorUnitary : Matrix n n ℂ)) j k)
          * (hP.1.eigenvalues j * Real.log (hP.1.eigenvalues j)
              - hP.1.eigenvalues j * Real.log (hQ.1.eigenvalues k)
              - hP.1.eigenvalues j + hQ.1.eigenvalues k) := by
  simp_rw [fun t => chi_div_eq_sum t hP.1 hQ.1]
  rw [integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ =>
      (integrableOn_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finset_sum _ fun k _ =>
    (integrableOn_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)]

/-- **Integral formula for the relative entropy.** -/
theorem relEntropy_eq_integral {P Q : Matrix n n ℂ} (hP : IsDensity P) (hQ : IsDensity Q) :
    relEntropy P Q = ∫ t in Set.Ioi (0 : ℝ), chi t hP.1.1 hQ.1.1 / (1 + t) ^ 2 := by
  obtain ⟨hPd, hPtr⟩ := hP
  obtain ⟨hQd, hQtr⟩ := hQ
  set p := hPd.1.eigenvalues with hp
  set q := hQd.1.eigenvalues with hq
  set w : n → n → ℝ := fun j k => Complex.normSq ((star (hPd.1.eigenvectorUnitary
    : Matrix n n ℂ) * (hQd.1.eigenvectorUnitary : Matrix n n ℂ)) j k) with hw
  have hrow : ∀ j, ∑ k, w j k = 1 := fun j =>
    normSq_row_sum _ (mul_star_conj_unitary _ _) j
  have hcol : ∀ k, ∑ j, w j k = 1 := fun k =>
    normSq_col_sum _ (star_mul_conj_unitary _ _) k
  have hpsum : ∑ j, p j = 1 := by
    have h1 := hPd.1.trace_eq_sum_eigenvalues
    rw [hPtr] at h1
    have h2 : ((∑ j, p j : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  have hqsum : ∑ k, q k = 1 := by
    have h1 := hQd.1.trace_eq_sum_eigenvalues
    rw [hQtr] at h1
    have h2 : ((∑ k, q k : ℝ) : ℂ) = 1 := by push_cast; exact h1.symm
    simpa using congrArg Complex.re h2
  rw [integral_chi_eq hPd hQd]
  have hsplit : ∀ j k, w j k * (p j * Real.log (p j) - p j * Real.log (q k) - p j + q k)
      = w j k * (p j * Real.log (p j)) - w j k * (p j * Real.log (q k))
        - w j k * p j + w j k * q k := by
    intro j k
    ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hsplit j k]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have e1 : ∑ j, (∑ k, w j k) * (p j * Real.log (p j)) = ∑ j, p j * Real.log (p j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrow j, one_mul]
  have e3 : ∑ j, (∑ k, w j k) * p j = 1 := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hrow j, one_mul]]
    exact hpsum
  have e4 : ∑ j, ∑ k, w j k * q k = 1 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_mul, hcol k, one_mul]]
    exact hqsum
  rw [relEntropy, trace_mul_logM_self_re hPd.1, trace_mul_logM_re hPd.1 hQd.1]
  rw [e1, e3, e4]
  have e2 : ∑ j, ∑ k, p j * Real.log (q k) * w j k
      = ∑ j, ∑ k, w j k * (p j * Real.log (q k)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e2]
  ring

/-! ### The data processing inequality -/

/-- **Data processing inequality**: the Umegaki relative entropy of two faithful states does not
increase under a CPTP map (provided the output states are again faithful). -/
theorem data_processing {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsCPTP Φ)
    {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hΦρ : IsDensity (Φ ρ)) (hΦσ : IsDensity (Φ σ)) :
    relEntropy (Φ ρ) (Φ σ) ≤ relEntropy ρ σ := by
  obtain ⟨ι, hι, K, hK, hrep⟩ := hΦ
  have hr : Φ ρ = krausMap K ρ := hrep ρ
  have hs : Φ σ = krausMap K σ := hrep σ
  have hKρ : (krausMap K ρ).PosDef := hr ▸ hΦρ.1
  have hKσ : (krausMap K σ).PosDef := hs ▸ hΦσ.1
  have hdenρ : IsDensity (krausMap K ρ) := ⟨hKρ, hr ▸ hΦρ.2⟩
  have hdenσ : IsDensity (krausMap K σ) := ⟨hKσ, hs ▸ hΦσ.2⟩
  rw [hr, hs, relEntropy_eq_integral hdenρ hdenσ, relEntropy_eq_integral hρ hσ]
  refine setIntegral_mono_on (integrableOn_chi hdenρ.1 hdenσ.1) (integrableOn_chi hρ.1 hσ.1)
    measurableSet_Ioi fun t ht => ?_
  have htpos : (0 : ℝ) < t := ht
  have hmono := chi_monotone htpos hK hρ.1 hσ.1 hKρ hKσ
  have hden : (0 : ℝ) < (1 + t) ^ 2 := by positivity
  gcongr

end QI

