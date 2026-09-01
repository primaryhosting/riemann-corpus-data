import Brockian.UnbalancedPentagon

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

import Brockian.UnbalancedPentagon.Basic
import Brockian.UnbalancedPentagon.Operators
import Brockian.UnbalancedPentagon.Decomposition
import Brockian.UnbalancedPentagon.Charpoly
import Brockian.UnbalancedPentagon.Symmetry
import Brockian.UnbalancedPentagon.Balanced

/-!
# The unbalanced pentagon: exact quotient spectrum

Blow up each vertex `i` of the 5-cycle into a fibre of `m i > 0` vertices and join two vertices
whenever their fibres are adjacent in `C₅`.  With `L` the normalized Laplacian, `T` the
fibre-constant isometry and `Q` the `5 × 5` quotient matrix, this development contains:

1. `fiber_decomposition` — the orthogonal splitting into fibre-constant vectors `Ufib` (the
   range of `T`) and fibre-sum-zero vectors `Wfib`;
2. `quotient_intertwining` (and `quotient_intertwining_matrix`) — `L ∘ T = T ∘ (I - Q)`;
3. `fiber_kernel_eigenvalue_one` — `L x = x` for `x ∈ Wfib`, and `dim Wfib = (∑ i, m i) - 5`;
4. `quotient_spectrum` — `charpoly L = (X - 1) ^ ((∑ i, m i) - 5) * charpoly (I - Q)`, with the
   derived multiplicity statement `quotient_spectrum_rootMultiplicity` and the eigenvalue
   statement `quotient_spectrum_isRoot`;
5. `d5_invariant_iff_balanced` — `D₅`-invariance of the fibre sizes is equivalent to their being
   constant, together with the induced graph automorphisms `balancedPerm` in the balanced case
   and `balancedPerm_commutes_Lap`;
6. `balanced_specialization` — for `m i = k > 0`, `Q = A(C₅)/2` and `L` has spectrum `0` (once),
   `(5-√5)/4` (twice), `1` with multiplicity `5(k-1)` and `(5+√5)/4` (twice).
-/

import Brockian.UnbalancedPentagon.Operators

/-!
# The orthogonal fibre decomposition

The space `EuclideanSpace ℝ (V m)` splits as the orthogonal direct sum of

* `Ufib m`, the range of the fibre-constant isometry `T` (the fibre-constant vectors), and
* `Wfib m`, the space of vectors whose sum on each fibre vanishes.

We prove `fiber_decomposition` and `fiber_kernel_eigenvalue_one`
(`L` acts as the identity on `Wfib m`, whose dimension is `(∑ i, m i) - 5`).
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix RealInnerProductSpace

variable {m : Fin 5 → ℕ}

variable (m) in
/-- Matrix of the fibre-sum map. -/
def Smat : Matrix (Fin 5) (V m) ℝ := fun i u => if u.1 = i then 1 else 0

variable (m) in
/-- The fibre-sum map, sending `x` to `i ↦ ∑ a, x (i, a)`. -/
noncomputable def fibreSum : EuclideanSpace ℝ (V m) →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
  Matrix.toEuclideanLin (Smat m)

@[simp] lemma fibreSum_apply (x : EuclideanSpace ℝ (V m)) (i : Fin 5) :
    fibreSum m x i = ∑ a : Fin (m i), x ⟨i, a⟩ := by
  rw [fibreSum, toEuclideanLin_apply', sum_V, Finset.sum_eq_single i]
  · simp [Smat]
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Smat, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

variable (m) in
/-- The subspace of fibre-constant vectors, i.e. the range of `T`. -/
noncomputable def Ufib : Submodule ℝ (EuclideanSpace ℝ (V m)) := LinearMap.range (Tlin m)

variable (m) in
/-- The subspace of vectors whose sum on each fibre vanishes. -/
noncomputable def Wfib : Submodule ℝ (EuclideanSpace ℝ (V m)) := LinearMap.ker (fibreSum m)

lemma mem_Wfib_iff (x : EuclideanSpace ℝ (V m)) :
    x ∈ Wfib m ↔ ∀ i, ∑ a : Fin (m i), x ⟨i, a⟩ = 0 := by
  constructor
  · intro hx i
    have h : fibreSum m x = 0 := hx
    simpa using congrArg (fun y : EuclideanSpace ℝ (Fin 5) => y i) h
  · intro hx
    show fibreSum m x = 0
    ext i
    simpa using hx i

/-- `Ufib m` consists exactly of the vectors that are constant on each fibre. -/
lemma mem_Ufib_iff (hpos : ∀ i, 0 < m i) (x : EuclideanSpace ℝ (V m)) :
    x ∈ Ufib m ↔ ∀ (i : Fin 5) (a b : Fin (m i)), x ⟨i, a⟩ = x ⟨i, b⟩ := by
  constructor
  · rintro ⟨f, rfl⟩ i a b
    simp
  · intro hx
    refine ⟨WithLp.toLp 2 (fun i => x ⟨i, ⟨0, hpos i⟩⟩ * Real.sqrt (m i)), ?_⟩
    ext u
    obtain ⟨i, a⟩ := u
    rw [Tlin_apply, mul_div_assoc, div_self (sqrt_m_ne hpos i), mul_one]
    exact (hx i ⟨0, hpos i⟩ a)

/-- Pairing a fibre-constant vector against an arbitrary vector only sees the fibre sums. -/
lemma inner_Tlin_eq (f : EuclideanSpace ℝ (Fin 5)) (x : EuclideanSpace ℝ (V m)) :
    ⟪Tlin m f, x⟫ = ∑ i, (f i / Real.sqrt (m i)) * ∑ a : Fin (m i), x ⟨i, a⟩ := by
  have h1 : ⟪Tlin m f, x⟫ = ∑ u, (Tlin m f) u * x u := by
    simp [PiLp.inner_apply, mul_comm]
  rw [h1, sum_V]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Tlin_apply]

/-- **Fibre decomposition**: the space is the orthogonal direct sum of the fibre-constant
vectors `Ufib m` and the fibre-sum-zero vectors `Wfib m`. -/
theorem fiber_decomposition (hpos : ∀ i, 0 < m i) :
    (Ufib m)ᗮ = Wfib m ∧ IsCompl (Ufib m) (Wfib m) ∧
      ∀ u ∈ Ufib m, ∀ w ∈ Wfib m, ⟪u, w⟫ = 0 := by
  have horth : (Ufib m)ᗮ = Wfib m := by
    ext x
    constructor
    · intro hx
      rw [mem_Wfib_iff]
      intro i
      have hmem : Tlin m (EuclideanSpace.single i (1 : ℝ)) ∈ Ufib m :=
        ⟨EuclideanSpace.single i 1, rfl⟩
      have h0 := hx _ hmem
      rw [inner_Tlin_eq] at h0
      rw [Finset.sum_eq_single i] at h0
      · simp only [EuclideanSpace.single_apply] at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd h (by simpa using one_div_ne_zero (sqrt_m_ne hpos i))
        · exact h
      · intro b _ hb
        simp [EuclideanSpace.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro hx
      rw [mem_Wfib_iff] at hx
      rintro u ⟨f, rfl⟩
      rw [inner_Tlin_eq]
      exact Finset.sum_eq_zero fun i _ => by rw [hx i, mul_zero]
  refine ⟨horth, ?_, ?_⟩
  · rw [← horth]
    exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  · intro u hu w hw
    rw [← horth] at hw
    exact (Submodule.mem_orthogonal _ _).1 hw u hu

/-! ## `L` acts as the identity on `Wfib m` -/

lemma Nop_eq_zero_on_Wfib (x : EuclideanSpace ℝ (V m)) (hx : x ∈ Wfib m) :
    Matrix.toEuclideanLin (Nmat m) x = 0 := by
  rw [mem_Wfib_iff] at hx
  ext u
  rw [toEuclideanLin_apply', sum_V]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hconst : ∀ a : Fin (m j), Nmat m u ⟨j, a⟩
      = if C5adj u.1 j then 1 / (Real.sqrt (deg m u.1) * Real.sqrt (deg m j)) else 0 :=
    fun _ => rfl
  calc ∑ a : Fin (m j), Nmat m u ⟨j, a⟩ * x ⟨j, a⟩
      = ∑ a : Fin (m j),
        (if C5adj u.1 j then 1 / (Real.sqrt (deg m u.1) * Real.sqrt (deg m j)) else 0)
          * x ⟨j, a⟩ := by
        exact Finset.sum_congr rfl fun a _ => by rw [hconst a]
    _ = (if C5adj u.1 j then 1 / (Real.sqrt (deg m u.1) * Real.sqrt (deg m j)) else 0)
          * ∑ a : Fin (m j), x ⟨j, a⟩ := by rw [Finset.mul_sum]
    _ = 0 := by rw [hx j, mul_zero]

/-- **Every fibre-sum-zero vector is an eigenvector of `L` with eigenvalue `1`**, and
`dim W = (∑ i, m i) - 5`. -/
theorem fiber_kernel_eigenvalue_one (hpos : ∀ i, 0 < m i) :
    (∀ x ∈ Wfib m, Lop m x = x) ∧
      Module.finrank ℝ (Wfib m) = (∑ i, m i) - 5 := by
  constructor
  · intro x hx
    have hN := Nop_eq_zero_on_Wfib x hx
    have : Lop m x = Matrix.toEuclideanLin (1 : Matrix (V m) (V m) ℝ) x
        - Matrix.toEuclideanLin (Nmat m) x := by
      rw [Lop, Lap, map_sub]
      rfl
    rw [this, hN, sub_zero]
    ext u
    rw [toEuclideanLin_apply', Finset.sum_eq_single u]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro b _ hb; rw [Matrix.one_apply_ne (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ u) h
  · have hrange : LinearMap.range (fibreSum m) = ⊤ := by
      rw [eq_top_iff]
      rintro f -
      refine ⟨Tlin m (WithLp.toLp 2 fun i => f i * Real.sqrt (m i) / m i), ?_⟩
      ext i
      rw [fibreSum_apply]
      have : ∀ a : Fin (m i),
          Tlin m (WithLp.toLp 2 fun i => f i * Real.sqrt (m i) / m i) ⟨i, a⟩
            = f i / (m i : ℝ) := by
        intro a
        rw [Tlin_apply]
        have h1 := sqrt_m_ne hpos i
        have h2 := ne_of_gt (m_pos_real hpos i)
        field_simp
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_comm,
        div_mul_cancel₀ _ (ne_of_gt (m_pos_real hpos i))]
    have hrk : Module.finrank ℝ (LinearMap.range (fibreSum m))
        + Module.finrank ℝ (LinearMap.ker (fibreSum m))
        = Module.finrank ℝ (EuclideanSpace ℝ (V m)) :=
      LinearMap.finrank_range_add_finrank_ker _
    rw [hrange] at hrk
    have h5 : Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 5))) = 5 := by
      rw [finrank_top, finrank_euclideanSpace, Fintype.card_fin]
    have hn : Module.finrank ℝ (EuclideanSpace ℝ (V m)) = ∑ i, m i := by
      rw [finrank_euclideanSpace, card_V]
    rw [h5, hn] at hrk
    rw [Wfib]
    omega

end Brockian.UnbalancedPentagon

import Brockian.UnbalancedPentagon.Charpoly

/-!
# The balanced specialization

For `m i = k > 0` the quotient matrix is `Q = A(C₅) / 2` and the normalized Laplacian has the
classical spectrum

* `0` with multiplicity `1`,
* `(5 - √5) / 4` with multiplicity `2`,
* `1` with multiplicity `5 (k - 1)`,
* `(5 + √5) / 4` with multiplicity `2`.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix Polynomial

/-- The adjacency matrix of the 5-cycle. -/
def AC5 : Matrix (Fin 5) (Fin 5) ℝ := fun i j => if C5adj i j then 1 else 0

/-! ## Numerical facts about `√5` -/

lemma sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)

lemma sqrt5_lb : 2 < Real.sqrt 5 := by
  have h : Real.sqrt 4 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h

lemma sqrt5_ub : Real.sqrt 5 < 3 := by
  have h : Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)] at h

/-! ## The quotient matrix in the balanced case -/

/-- **In the balanced case the quotient matrix is `A(C₅)/2`.** -/
theorem Qmat_balanced {k : ℕ} (hk : 0 < k) : Qmat (fun _ => k) = (1/2 : ℝ) • AC5 := by
  ext i j
  rw [Qmat_apply, Matrix.smul_apply, AC5, smul_eq_mul]
  by_cases h : C5adj i j
  · rw [if_pos h, if_pos h]
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    have hval : ((k:ℝ) * k / ((deg (fun _ => k) i : ℝ) * (deg (fun _ => k) j))) = 1/4 := by
      simp only [deg]
      push_cast
      field_simp
      ring
    rw [hval, show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · rw [if_neg h, if_neg h, mul_zero]

/-! ## The characteristic polynomial of the quotient -/

set_option maxHeartbeats 1000000 in
lemma det_balanced_quotient (x : ℝ) :
    (!![x-1, 1/2, 0, 0, 1/2;
        1/2, x-1, 1/2, 0, 0;
        0, 1/2, x-1, 1/2, 0;
        0, 0, 1/2, x-1, 1/2;
        1/2, 0, 0, 1/2, x-1]).det
      = x * (x - (5 - Real.sqrt 5)/4)^2 * (x - (5 + Real.sqrt 5)/4)^2 := by
  have key : (!![x-1, 1/2, 0, 0, 1/2;
        1/2, x-1, 1/2, 0, 0;
        0, 1/2, x-1, 1/2, 0;
        0, 0, 1/2, x-1, 1/2;
        1/2, 0, 0, 1/2, x-1]).det = x * (x^2 - (5/2)*x + 5/4)^2 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    norm_num [Fin.lt_def]
    ring
  have hfac : (x - (5 - Real.sqrt 5)/4) * (x - (5 + Real.sqrt 5)/4)
      = x^2 - (5/2)*x + 5/4 := by
    field_simp
    nlinarith [sqrt5_sq]
  rw [key, ← hfac]
  ring

lemma scalar_sub_one_sub_Qmat_balanced {k : ℕ} (hk : 0 < k) (x : ℝ) :
    Matrix.scalar (Fin 5) x - (1 - Qmat (fun _ => k))
      = !![x-1, 1/2, 0, 0, 1/2;
           1/2, x-1, 1/2, 0, 0;
           0, 1/2, x-1, 1/2, 0;
           0, 0, 1/2, x-1, 1/2;
           1/2, 0, 0, 1/2, x-1] := by
  have hQ : Qmat (fun _ => k) = fun i j => if C5adj i j then (1/2:ℝ) else 0 := by
    rw [Qmat_balanced hk]
    ext i j
    by_cases h : C5adj i j <;> simp [AC5, h]
  ext i j
  rw [hQ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar, Matrix.diagonal, C5adj, Fin.ext_iff]

/-- The characteristic polynomial of the `5 × 5` quotient in the balanced case. -/
theorem charpoly_one_sub_Qmat_balanced {k : ℕ} (hk : 0 < k) :
    (1 - Qmat (fun _ => k)).charpoly
      = (X - C (0:ℝ)) * (X - C ((5 - Real.sqrt 5)/4))^2
        * (X - C ((5 + Real.sqrt 5)/4))^2 := by
  refine Polynomial.funext fun x => ?_
  rw [Matrix.eval_charpoly, scalar_sub_one_sub_Qmat_balanced hk x, det_balanced_quotient x]
  simp

/-! ## The spectrum of the Laplacian in the balanced case -/

lemma rootMultiplicity_X_sub_C_pow (a mu : ℝ) (n : ℕ) :
    Polynomial.rootMultiplicity mu (((X : ℝ[X]) - C a) ^ n) = if mu = a then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a))
          (Polynomial.X_sub_C_ne_zero a)), ih, Polynomial.rootMultiplicity_X_sub_C]
      by_cases h : mu = a <;> simp [h]

lemma sum_balanced (k : ℕ) : ∑ _i : Fin 5, k = 5 * k := by simp [mul_comm]

/-- The characteristic polynomial of the normalized Laplacian in the balanced case, in fully
factored form. -/
theorem charpoly_Lap_balanced {k : ℕ} (hk : 0 < k) :
    (Lap (fun _ => k)).charpoly
      = (X - C (0:ℝ)) * (X - C ((5 - Real.sqrt 5)/4))^2
        * (X - C (1:ℝ)) ^ (5 * (k-1)) * (X - C ((5 + Real.sqrt 5)/4))^2 := by
  have hpos : ∀ i : Fin 5, 0 < (fun _ => k) i := fun _ => hk
  rw [quotient_spectrum hpos, charpoly_one_sub_Qmat_balanced hk, sum_balanced]
  have hexp : 5 * k - 5 = 5 * (k - 1) := by omega
  have hX : ((X : ℝ[X]) - 1) = X - C (1:ℝ) := by simp
  rw [hexp, hX]
  ring

/-- The multiplicity of every real number as a root of the characteristic polynomial of `L`
in the balanced case. -/
theorem balanced_rootMultiplicity {k : ℕ} (hk : 0 < k) (mu : ℝ) :
    ((Lap (fun _ => k)).charpoly).rootMultiplicity mu
      = (if mu = 0 then 1 else 0) + (if mu = (5 - Real.sqrt 5)/4 then 2 else 0)
        + (if mu = 1 then 5 * (k-1) else 0)
        + (if mu = (5 + Real.sqrt 5)/4 then 2 else 0) := by
  have hA : ((X : ℝ[X]) - C (0:ℝ)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hB : (((X : ℝ[X]) - C ((5 - Real.sqrt 5)/4))^2) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hC : (((X : ℝ[X]) - C (1:ℝ))^(5*(k-1))) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hD : (((X : ℝ[X]) - C ((5 + Real.sqrt 5)/4))^2) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  rw [charpoly_Lap_balanced hk,
    Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hC) hD),
    Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA hB) hC),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hA hB),
    Polynomial.rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C_pow,
    rootMultiplicity_X_sub_C_pow, rootMultiplicity_X_sub_C_pow]

/-! ### The four eigenvalues and their multiplicities -/

lemma lam_minus_pos : (0:ℝ) < (5 - Real.sqrt 5)/4 := by
  have := sqrt5_ub; linarith

lemma lam_minus_lt_one : (5 - Real.sqrt 5)/4 < 1 := by
  have := sqrt5_lb; linarith

lemma one_lt_lam_plus : (1:ℝ) < (5 + Real.sqrt 5)/4 := by
  have := sqrt5_lb; linarith

lemma lam_minus_ne_lam_plus : (5 - Real.sqrt 5)/4 ≠ (5 + Real.sqrt 5)/4 := by
  have := sqrt5_lb; intro h; nlinarith

/-- **Balanced specialization**: for `m i = k > 0` the quotient matrix is `A(C₅)/2` and the
normalized Laplacian has spectrum `0` (multiplicity `1`), `(5-√5)/4` (multiplicity `2`),
`1` (multiplicity `5(k-1)`) and `(5+√5)/4` (multiplicity `2`). -/
theorem balanced_specialization {k : ℕ} (hk : 0 < k) :
    Qmat (fun _ => k) = (1/2 : ℝ) • AC5 ∧
    (Lap (fun _ => k)).charpoly
      = (X - C (0:ℝ)) * (X - C ((5 - Real.sqrt 5)/4))^2
        * (X - C (1:ℝ)) ^ (5 * (k-1)) * (X - C ((5 + Real.sqrt 5)/4))^2 ∧
    ((Lap (fun _ => k)).charpoly).rootMultiplicity 0 = 1 ∧
    ((Lap (fun _ => k)).charpoly).rootMultiplicity ((5 - Real.sqrt 5)/4) = 2 ∧
    ((Lap (fun _ => k)).charpoly).rootMultiplicity 1 = 5 * (k-1) ∧
    ((Lap (fun _ => k)).charpoly).rootMultiplicity ((5 + Real.sqrt 5)/4) = 2 := by
  have hm := lam_minus_pos
  have hm1 := lam_minus_lt_one
  have hp1 := one_lt_lam_plus
  have hmp := lam_minus_ne_lam_plus
  refine ⟨Qmat_balanced hk, charpoly_Lap_balanced hk, ?_, ?_, ?_, ?_⟩
  · rw [balanced_rootMultiplicity hk]
    rw [if_pos rfl, if_neg (by intro h; rw [← h] at hm; exact lt_irrefl 0 hm),
      if_neg (by norm_num), if_neg (by intro h; rw [← h] at hp1; linarith)]
  · rw [balanced_rootMultiplicity hk]
    rw [if_neg (by intro h; rw [h] at hm; exact lt_irrefl 0 hm), if_pos rfl,
      if_neg (by intro h; rw [h] at hm1; exact lt_irrefl 1 hm1), if_neg hmp]
  · rw [balanced_rootMultiplicity hk]
    rw [if_neg (by norm_num), if_neg (fun h => absurd h.symm (ne_of_lt hm1)),
      if_pos rfl, if_neg (fun h => absurd h.symm (ne_of_gt hp1))]
    omega
  · rw [balanced_rootMultiplicity hk]
    rw [if_neg (by intro h; rw [h] at hp1; linarith), if_neg (Ne.symm hmp),
      if_neg (by intro h; rw [h] at hp1; exact lt_irrefl 1 hp1), if_pos rfl]

end Brockian.UnbalancedPentagon

import Brockian.UnbalancedPentagon.Decomposition

/-!
# The exact spectral reduction

The characteristic polynomial of the normalized Laplacian of the blown-up pentagon factors as

`charpoly L = (X - 1) ^ ((∑ i, m i) - 5) * charpoly (I - Q)`.

The proof is a Sylvester-type determinant identity applied to the rank-`≤ 5` factorization
`N = T Q Tᵀ` together with `Tᵀ T = I`; it is carried out over the field of rational functions
`RatFunc ℝ` and transported back along the injection `ℝ[X] → RatFunc ℝ`.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix Polynomial

/-! ## General lemmas -/

/-- A Sylvester-type determinant identity: for an invertible scalar `c`,
`det (c • 1 + A * B) = c ^ (|p| - |q|) * det (c • 1 + B * A)`. -/
theorem det_smul_one_add_mul_comm {p q K : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] [Field K] (c : K) (hc : c ≠ 0) (A : Matrix p q K) (B : Matrix q p K)
    (hcard : Fintype.card q ≤ Fintype.card p) :
    (c • (1 : Matrix p p K) + A * B).det
      = c ^ (Fintype.card p - Fintype.card q) * (c • (1 : Matrix q q K) + B * A).det := by
  have h1 : c • (1 : Matrix p p K) + A * B = c • (1 + (c⁻¹ • A) * B) := by
    rw [smul_add, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h2 : (1 : Matrix q q K) + B * (c⁻¹ • A) = c⁻¹ • (c • (1 : Matrix q q K) + B * A) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.mul_smul]
  have hpow : c ^ Fintype.card p
      = c ^ (Fintype.card p - Fintype.card q) * c ^ Fintype.card q := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  rw [h1, Matrix.det_smul, Matrix.det_one_add_mul_comm, h2, Matrix.det_smul, inv_pow, hpow]
  field_simp

/-- Applying a ring hom entrywise to `c • 1 + M`. -/
lemma map_smul_one_add {p R S : Type*} [Fintype p] [DecidableEq p] [CommRing R] [CommRing S]
    (f : R →+* S) (c : R) (M : Matrix p p R) :
    (c • (1 : Matrix p p R) + M).map f = (f c) • (1 : Matrix p p S) + M.map f := by
  ext u v
  by_cases h : u = v <;> simp [h]

/-- The characteristic matrix of `1 - M` for a matrix `M` with zero diagonal. -/
lemma charmatrix_one_sub {p : Type*} [Fintype p] [DecidableEq p] (M : Matrix p p ℝ)
    (hdiag : ∀ i, M i i = 0) :
    charmatrix (1 - M) = ((X : ℝ[X]) - 1) • (1 : Matrix p p ℝ[X]) + M.map C := by
  ext u v
  by_cases h : u = v
  · subst h
    rw [charmatrix_apply_eq]
    simp [hdiag u]
  · rw [charmatrix_apply_ne _ _ _ h]
    simp [h]

lemma X_sub_one_ne_zero : ((X : ℝ[X]) - 1) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 2) h
  norm_num at this

lemma rootMultiplicity_X_sub_one_pow (mu : ℝ) (k : ℕ) :
    Polynomial.rootMultiplicity mu (((X : ℝ[X]) - 1) ^ k) = if mu = 1 then k else 0 := by
  have hX : ((X : ℝ[X]) - 1) = X - C (1 : ℝ) := by simp
  rw [hX]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1))
          (Polynomial.X_sub_C_ne_zero 1)), ih, Polynomial.rootMultiplicity_X_sub_C]
      by_cases h : mu = 1 <;> simp [h]

/-! ## The factorization -/

variable {m : Fin 5 → ℕ}

lemma five_le_sum (hpos : ∀ i, 0 < m i) : 5 ≤ ∑ i, m i := by
  calc (5 : ℕ) = ∑ _i : Fin 5, 1 := by simp
    _ ≤ ∑ i, m i := Finset.sum_le_sum fun i _ => hpos i

lemma five_le_card_V (hpos : ∀ i, 0 < m i) : 5 ≤ Fintype.card (V m) := by
  rw [card_V]; exact five_le_sum hpos

/-- **Exact spectral reduction**: the characteristic polynomial of the normalized Laplacian
factors as `(X - 1) ^ ((∑ i, m i) - 5)` times the characteristic polynomial of the
`5 × 5` quotient `I - Q`. -/
theorem quotient_spectrum (hpos : ∀ i, 0 < m i) :
    (Lap m).charpoly
      = ((X : ℝ[X]) - 1) ^ ((∑ i, m i) - 5) * (1 - Qmat m).charpoly := by
  set phi : ℝ[X] →+* RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) with hphi
  have hphi_inj : Function.Injective phi := RatFunc.algebraMap_injective ℝ
  set psi : ℝ →+* RatFunc ℝ := phi.comp (Polynomial.C : ℝ →+* ℝ[X]) with hpsi
  set c : RatFunc ℝ := phi ((X : ℝ[X]) - 1) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    exact fun h => X_sub_one_ne_zero (hphi_inj (by simpa using h))
  have hLc : charmatrix (Lap m) = ((X : ℝ[X]) - 1) • (1 : Matrix (V m) (V m) ℝ[X])
      + (Nmat m).map C := by
    rw [Lap]
    exact charmatrix_one_sub _ (fun u => by simp [Nmat_apply, C5adj_irrefl u.1])
  have hQc : charmatrix (1 - Qmat m) = ((X : ℝ[X]) - 1) • (1 : Matrix (Fin 5) (Fin 5) ℝ[X])
      + (Qmat m).map C :=
    charmatrix_one_sub _ (fun i => by simp [Qmat_apply, C5adj_irrefl i])
  have hmapN : ((Nmat m).map C).map phi
      = ((Tmat m).map psi * (Qmat m).map psi) * (((Tmat m)ᵀ).map psi) := by
    have h0 : ((Nmat m).map C).map phi = (Nmat m).map psi := by
      ext u v; simp [hpsi]
    rw [h0, Nmat_eq_Tmat_mul hpos, ← Matrix.map_mul, ← Matrix.map_mul]
  have hmapQ : ((Qmat m).map C).map phi = (Qmat m).map psi := by
    ext i j; simp [hpsi]
  have hBA : (((Tmat m)ᵀ).map psi) * ((Tmat m).map psi * (Qmat m).map psi)
      = (Qmat m).map psi := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Tmat_transpose_mul_self hpos,
      Matrix.map_one _ (map_zero psi) (map_one psi), Matrix.one_mul]
  have e1 : phi ((Lap m).charpoly) = ((charmatrix (Lap m)).map phi).det := by
    rw [Matrix.charpoly, RingHom.map_det]; rfl
  have e2 : phi ((1 - Qmat m).charpoly) = ((charmatrix (1 - Qmat m)).map phi).det := by
    rw [Matrix.charpoly, RingHom.map_det]; rfl
  refine hphi_inj ?_
  rw [map_mul, e1, e2, hLc, hQc, map_smul_one_add, map_smul_one_add, hmapN, hmapQ, ← hc,
    det_smul_one_add_mul_comm c hcne _ _ (by simpa using five_le_card_V hpos), hBA]
  congr 1
  rw [map_pow, ← hc, card_V]
  simp

/-! ## Multiplicities and eigenvalues -/

lemma charpoly_ne_zero {p : Type*} [Fintype p] [DecidableEq p] (M : Matrix p p ℝ) :
    M.charpoly ≠ 0 := (M.charpoly_monic).ne_zero

/-- The root multiplicities of the characteristic polynomial of `L`: apart from the extra
`(∑ i, m i) - 5` copies of the eigenvalue `1`, they are those of the `5 × 5` quotient. -/
theorem quotient_spectrum_rootMultiplicity (hpos : ∀ i, 0 < m i) (mu : ℝ) :
    ((Lap m).charpoly).rootMultiplicity mu
      = (if mu = 1 then (∑ i, m i) - 5 else 0)
        + ((1 - Qmat m).charpoly).rootMultiplicity mu := by
  rw [quotient_spectrum hpos, Polynomial.rootMultiplicity_mul
    (mul_ne_zero (pow_ne_zero _ X_sub_one_ne_zero) (charpoly_ne_zero _)),
    rootMultiplicity_X_sub_one_pow]

/-- Eigenvalues of a real matrix are exactly the roots of its characteristic polynomial. -/
theorem isRoot_charpoly_iff {p : Type*} [Fintype p] [DecidableEq p] (M : Matrix p p ℝ) (mu : ℝ) :
    (M.charpoly).IsRoot mu ↔ ∃ v : p → ℝ, v ≠ 0 ∧ M *ᵥ v = mu • v := by
  have hscal : ∀ (v : p → ℝ) (i : p), (Matrix.scalar p mu *ᵥ v) i = mu * v i := by
    intro v i
    simp [Matrix.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal]
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hmv⟩
    refine ⟨v, hv, ?_⟩
    funext i
    have h1 : ((Matrix.scalar p mu - M) *ᵥ v) i = 0 := by rw [hmv]; rfl
    rw [Matrix.sub_mulVec, Pi.sub_apply, sub_eq_zero, hscal] at h1
    simpa [Pi.smul_apply] using h1.symm
  · rintro ⟨v, hv, hmv⟩
    refine ⟨v, hv, ?_⟩
    funext i
    have h1 : (M *ᵥ v) i = mu * v i := by rw [hmv]; simp
    rw [Matrix.sub_mulVec, Pi.sub_apply, hscal, h1]
    simp

/-- The spectrum of `L`: apart from the eigenvalue `1` (present as soon as some fibre has more
than one vertex), the eigenvalues of `L` are those of the `5 × 5` matrix `I - Q`. -/
theorem quotient_spectrum_isRoot (hpos : ∀ i, 0 < m i) (mu : ℝ) :
    ((Lap m).charpoly).IsRoot mu
      ↔ (mu = 1 ∧ 5 < ∑ i, m i) ∨ ((1 - Qmat m).charpoly).IsRoot mu := by
  have hk : ((∑ i, m i) - 5 ≠ 0) ↔ 5 < ∑ i, m i := by
    have := five_le_sum hpos; omega
  rw [quotient_spectrum hpos, Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero]
  simp only [Polynomial.eval_pow, pow_eq_zero_iff', Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, sub_eq_zero, Polynomial.IsRoot, hk]

end Brockian.UnbalancedPentagon

import Mathlib

/-!
# Unbalanced pentagon (blow-up of `C₅`): basic definitions

We blow up each vertex `i` of the 5-cycle `C₅` into a fibre of `m i` vertices, and join
two vertices whenever their fibres are adjacent in `C₅`.

This file sets up:

* `C5adj`, the adjacency relation of the 5-cycle on `Fin 5`;
* `V m`, the vertex type `Σ i : Fin 5, Fin (m i)`;
* `deg m i = m (i-1) + m (i+1)`, the common degree of the vertices of fibre `i`;
* the normalized adjacency matrix `Nmat m` and the normalized Laplacian `Lap m = 1 - Nmat m`;
* the `5 × 5` quotient matrix `Qmat m`;
* the matrix `Tmat m` of the fibre-constant isometry `T`.

The basic algebraic facts proved here are
`Tmat_transpose_mul_self : (Tmat m)ᵀ * Tmat m = 1` and
`Nmat_eq_Tmat_mul : Nmat m = Tmat m * Qmat m * (Tmat m)ᵀ`.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix

/-! ## The cycle `C₅` -/

/-- Adjacency of the 5-cycle on `Fin 5`. -/
def C5adj (i j : Fin 5) : Prop := j = i + 1 ∨ j = i - 1

instance : DecidableRel C5adj := fun i j => by unfold C5adj; infer_instance

lemma C5adj_symm {i j : Fin 5} : C5adj i j → C5adj j i := by
  revert i j; decide

lemma C5adj_comm (i j : Fin 5) : C5adj i j ↔ C5adj j i := ⟨C5adj_symm, C5adj_symm⟩

lemma C5adj_irrefl (i : Fin 5) : ¬ C5adj i i := by revert i; decide

/-- A convenient square-root identity used throughout. -/
lemma sqrt_mul_div_mul {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a * b / (c * d)) = Real.sqrt a * Real.sqrt b / (Real.sqrt c * Real.sqrt d) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul ha, Real.sqrt_mul hc]

/-! ## The blown-up graph -/

variable (m : Fin 5 → ℕ)

/-- The vertex type of the blown-up pentagon: fibre `i` has `m i` vertices. -/
def V (m : Fin 5 → ℕ) : Type := Σ i : Fin 5, Fin (m i)

instance : Fintype (V m) := inferInstanceAs (Fintype (Σ i : Fin 5, Fin (m i)))
instance : DecidableEq (V m) := inferInstanceAs (DecidableEq (Σ i : Fin 5, Fin (m i)))

/-- The number of vertices is `∑ i, m i`. -/
lemma card_V : Fintype.card (V m) = ∑ i, m i := by
  simp [V, Fintype.card_sigma]

/-- Summation over the vertex set, fibre by fibre. -/
lemma sum_V {M : Type*} [AddCommMonoid M] (f : V m → M) :
    ∑ u, f u = ∑ i, ∑ a : Fin (m i), f ⟨i, a⟩ :=
  Fintype.sum_sigma (α := fun i : Fin 5 => Fin (m i)) f

/-- The (common) degree of a vertex in fibre `i`. -/
def deg (m : Fin 5 → ℕ) (i : Fin 5) : ℕ := m (i - 1) + m (i + 1)

variable {m}

lemma deg_pos (hpos : ∀ i, 0 < m i) (i : Fin 5) : 0 < deg m i :=
  Nat.add_pos_left (hpos _) _

lemma deg_pos_real (hpos : ∀ i, 0 < m i) (i : Fin 5) : (0 : ℝ) < deg m i := by
  exact_mod_cast deg_pos hpos i

lemma sqrt_deg_pos (hpos : ∀ i, 0 < m i) (i : Fin 5) : 0 < Real.sqrt (deg m i) :=
  Real.sqrt_pos.2 (deg_pos_real hpos i)

lemma sqrt_deg_ne (hpos : ∀ i, 0 < m i) (i : Fin 5) : Real.sqrt (deg m i) ≠ 0 :=
  ne_of_gt (sqrt_deg_pos hpos i)

lemma m_pos_real (hpos : ∀ i, 0 < m i) (i : Fin 5) : (0 : ℝ) < m i := by
  exact_mod_cast hpos i

lemma sqrt_m_pos (hpos : ∀ i, 0 < m i) (i : Fin 5) : 0 < Real.sqrt (m i) :=
  Real.sqrt_pos.2 (m_pos_real hpos i)

lemma sqrt_m_ne (hpos : ∀ i, 0 < m i) (i : Fin 5) : Real.sqrt (m i) ≠ 0 :=
  ne_of_gt (sqrt_m_pos hpos i)

variable (m)

/-- The normalized adjacency matrix `D^{-1/2} A D^{-1/2}`. -/
noncomputable def Nmat : Matrix (V m) (V m) ℝ := fun u v =>
  if C5adj u.1 v.1 then 1 / (Real.sqrt (deg m u.1) * Real.sqrt (deg m v.1)) else 0

/-- The normalized Laplacian `L = I - D^{-1/2} A D^{-1/2}`. -/
noncomputable def Lap : Matrix (V m) (V m) ℝ := 1 - Nmat m

/-- The symmetric `5 × 5` quotient matrix. -/
noncomputable def Qmat : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  if C5adj i j then Real.sqrt ((m i : ℝ) * m j / ((deg m i : ℝ) * deg m j)) else 0

/-- The matrix of the fibre-constant isometry `T`: `(T f) (i, a) = f i / √(m i)`. -/
noncomputable def Tmat : Matrix (V m) (Fin 5) ℝ := fun u i => if u.1 = i then 1 / Real.sqrt (m i) else 0

variable {m}

lemma Nmat_apply (u v : V m) :
    Nmat m u v = if C5adj u.1 v.1 then 1 / (Real.sqrt (deg m u.1) * Real.sqrt (deg m v.1)) else 0 :=
  rfl

lemma Nmat_symm (u v : V m) : Nmat m u v = Nmat m v u := by
  simp only [Nmat_apply, C5adj_comm u.1 v.1]
  by_cases h : C5adj v.1 u.1 <;> simp [h, mul_comm]

lemma Lap_apply (u v : V m) : Lap m u v = (1 : Matrix (V m) (V m) ℝ) u v - Nmat m u v := rfl

lemma Qmat_apply (i j : Fin 5) :
    Qmat m i j = if C5adj i j then Real.sqrt ((m i : ℝ) * m j / ((deg m i : ℝ) * deg m j)) else 0 :=
  rfl

lemma Qmat_symm (i j : Fin 5) : Qmat m i j = Qmat m j i := by
  simp only [Qmat_apply, C5adj_comm i j]
  by_cases h : C5adj j i <;> simp [h, mul_comm]

lemma Tmat_apply (u : V m) (i : Fin 5) :
    Tmat m u i = if u.1 = i then 1 / Real.sqrt (m i) else 0 := rfl

/-- The columns of `T` are orthonormal: `Tᵀ T = I`. -/
lemma Tmat_transpose_mul_self (hpos : ∀ i, 0 < m i) : (Tmat m)ᵀ * Tmat m = 1 := by
  ext i j
  rw [Matrix.mul_apply, sum_V]
  simp only [Matrix.transpose_apply, Tmat_apply]
  have hconst : ∀ k : Fin 5, ∑ _a : Fin (m k),
      ((if k = i then 1 / Real.sqrt (m i) else 0) * (if k = j then 1 / Real.sqrt (m j) else 0))
      = (m k : ℝ) * ((if k = i then 1 / Real.sqrt (m i) else 0)
          * (if k = j then 1 / Real.sqrt (m j) else 0)) := by
    intro k; simp [Finset.sum_const, mul_comm]
  simp only [hconst]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · have h1 : Real.sqrt (m i) * Real.sqrt (m i) = m i :=
        Real.mul_self_sqrt (le_of_lt (m_pos_real hpos i))
      rw [Matrix.one_apply_eq]
      simp only [if_true]
      rw [one_div, ← mul_inv, h1]
      exact mul_inv_cancel₀ (ne_of_gt (m_pos_real hpos i))
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Matrix.one_apply_ne hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : k = i
    · subst h1; simp [hij]
    · simp [h1]

/-- Multiplying a `5 × 5` matrix on the left by `T`. -/
lemma Tmat_mul_apply (R : Matrix (Fin 5) (Fin 5) ℝ) (u : V m) (j : Fin 5) :
    (Tmat m * R) u j = R u.1 j / Real.sqrt (m u.1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single u.1]
  · rw [Tmat_apply, if_pos rfl]; ring
  · intro b _ hb; simp [Tmat_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ u.1) h

/-- Multiplying by `Tᵀ` on the right. -/
lemma mul_Tmat_transpose_apply (M' : Matrix (V m) (Fin 5) ℝ) (u v : V m) :
    (M' * (Tmat m)ᵀ) u v = M' u v.1 / Real.sqrt (m v.1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single v.1]
  · rw [Matrix.transpose_apply, Tmat_apply, if_pos rfl]; ring
  · intro b _ hb
    simp [Matrix.transpose_apply, Tmat_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ v.1) h

/-- The normalized adjacency matrix factors through the quotient matrix: `N = T Q Tᵀ`. -/
lemma Nmat_eq_Tmat_mul (hpos : ∀ i, 0 < m i) : Nmat m = Tmat m * Qmat m * (Tmat m)ᵀ := by
  ext u v
  rw [mul_Tmat_transpose_apply, Tmat_mul_apply, Nmat_apply, Qmat_apply]
  by_cases h : C5adj u.1 v.1
  · simp only [if_pos h]
    rw [sqrt_mul_div_mul (le_of_lt (m_pos_real hpos u.1)) (le_of_lt (m_pos_real hpos v.1))
      (le_of_lt (deg_pos_real hpos u.1))]
    have h1 := sqrt_m_ne hpos u.1
    have h2 := sqrt_m_ne hpos v.1
    have h3 := sqrt_deg_ne hpos u.1
    have h4 := sqrt_deg_ne hpos v.1
    field_simp
  · simp [h]

end Brockian.UnbalancedPentagon

import Brockian.UnbalancedPentagon

/-!
# Axiom audit

Building this module prints the axiom dependencies of every public target of
`Brockian.UnbalancedPentagon`.  All of them use only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms Brockian.UnbalancedPentagon.fiber_decomposition
#print axioms Brockian.UnbalancedPentagon.quotient_intertwining
#print axioms Brockian.UnbalancedPentagon.quotient_intertwining_matrix
#print axioms Brockian.UnbalancedPentagon.fiber_kernel_eigenvalue_one
#print axioms Brockian.UnbalancedPentagon.quotient_spectrum
#print axioms Brockian.UnbalancedPentagon.quotient_spectrum_rootMultiplicity
#print axioms Brockian.UnbalancedPentagon.quotient_spectrum_isRoot
#print axioms Brockian.UnbalancedPentagon.isRoot_charpoly_iff
#print axioms Brockian.UnbalancedPentagon.d5_invariant_iff_balanced
#print axioms Brockian.UnbalancedPentagon.balancedPerm_isAutomorphism
#print axioms Brockian.UnbalancedPentagon.balancedPerm_commutes_Lap
#print axioms Brockian.UnbalancedPentagon.balanced_specialization
#print axioms Brockian.UnbalancedPentagon.Qmat_balanced
#print axioms Brockian.UnbalancedPentagon.charpoly_Lap_balanced
#print axioms Brockian.UnbalancedPentagon.balanced_rootMultiplicity

import Brockian.UnbalancedPentagon.Basic

/-!
# The dihedral symmetry `D₅`

The dihedral group of order 10 acts on `Fin 5` by rotations `i ↦ i + c` and reflections
`i ↦ c - i`. We show:

* `d5_invariant_iff_balanced`: a fibre-size function `m` is invariant under the whole `D₅`
  action iff it is constant;
* in the constant (balanced) case there *is* a canonical induced action on the vertex type
  `V (fun _ => k)`, given by `balancedPerm`, and these vertex permutations are graph
  automorphisms which commute with the normalized Laplacian (`balancedPerm_commutes_Lap`).

Note that for a genuinely unbalanced `m` there is no base-only action on the dependent vertex
type `Σ i, Fin (m i)`: a rotation would have to map a fibre of size `m i` to a fibre of a
different size.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix

/-! ## The `D₅` action on `Fin 5` -/

/-- The rotation `i ↦ i + c` of the pentagon. -/
def D5rot (c : Fin 5) : Equiv.Perm (Fin 5) := Equiv.addRight c

/-- The reflection `i ↦ c - i` of the pentagon. -/
def D5refl (c : Fin 5) : Equiv.Perm (Fin 5) where
  toFun i := c - i
  invFun i := c - i
  left_inv i := by simp
  right_inv i := by simp

@[simp] lemma D5rot_apply (c i : Fin 5) : D5rot c i = i + c := rfl
@[simp] lemma D5refl_apply (c i : Fin 5) : D5refl c i = c - i := rfl

/-- The elements of the dihedral group `D₅` acting on the pentagon. -/
def IsD5 (sigma : Equiv.Perm (Fin 5)) : Prop :=
  (∃ c, sigma = D5rot c) ∨ (∃ c, sigma = D5refl c)

lemma isD5_rot (c : Fin 5) : IsD5 (D5rot c) := Or.inl ⟨c, rfl⟩
lemma isD5_refl (c : Fin 5) : IsD5 (D5refl c) := Or.inr ⟨c, rfl⟩

/-- Every element of `D₅` preserves the adjacency of the pentagon. -/
lemma IsD5.c5adj {sigma : Equiv.Perm (Fin 5)} (h : IsD5 sigma) (i j : Fin 5) :
    C5adj (sigma i) (sigma j) ↔ C5adj i j := by
  rcases h with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · simp only [D5rot_apply]
    revert i j c; decide
  · simp only [D5refl_apply]
    revert i j c; decide

/-! ## `D₅`-invariance means balanced -/

/-- **The fibre-size function is `D₅`-invariant iff it is constant.** -/
theorem d5_invariant_iff_balanced (m : Fin 5 → ℕ) :
    (∀ sigma : Equiv.Perm (Fin 5), IsD5 sigma → ∀ i, m (sigma i) = m i)
      ↔ ∃ k, ∀ i, m i = k := by
  constructor
  · intro h
    have hstep : ∀ i : Fin 5, m (i + 1) = m i := fun i => h (D5rot 1) (isD5_rot 1) i
    refine ⟨m 0, fun i => ?_⟩
    have h0 : m 1 = m 0 := hstep 0
    have h1 : m 2 = m 1 := hstep 1
    have h2 : m 3 = m 2 := hstep 2
    have h3 : m 4 = m 3 := hstep 3
    fin_cases i <;> simp_all
  · rintro ⟨k, hk⟩ sigma _ i
    rw [hk, hk]

/-! ## The induced `D₅` action in the balanced case -/

variable (k : ℕ)

/-- In the balanced case all fibres have the same size, so a permutation of the base induces a
permutation of the vertex set. -/
def balancedPerm (sigma : Equiv.Perm (Fin 5)) : V (fun _ => k) ≃ V (fun _ => k) where
  toFun u := ⟨sigma u.1, u.2⟩
  invFun u := ⟨sigma.symm u.1, u.2⟩
  left_inv u := by cases u; simp
  right_inv u := by cases u; simp

@[simp] lemma balancedPerm_apply (sigma : Equiv.Perm (Fin 5)) (u : V (fun _ => k)) :
    (balancedPerm k sigma u).1 = sigma u.1 := rfl

lemma deg_balanced (i : Fin 5) : deg (fun _ => k) i = k + k := rfl

/-- The vertex permutations induced by `D₅` are graph automorphisms. -/
theorem balancedPerm_isAutomorphism {sigma : Equiv.Perm (Fin 5)} (h : IsD5 sigma)
    (u v : V (fun _ => k)) :
    C5adj (balancedPerm k sigma u).1 (balancedPerm k sigma v).1 ↔ C5adj u.1 v.1 := by
  simpa using h.c5adj u.1 v.1

/-- The permutation matrix of a permutation of the vertex set. -/
def permMat {m : Fin 5 → ℕ} (e : V m ≃ V m) : Matrix (V m) (V m) ℝ :=
  fun u v => if v = e u then 1 else 0

lemma permMat_mul {m : Fin 5 → ℕ} (e : V m ≃ V m) (M : Matrix (V m) (V m) ℝ) (u v : V m) :
    (permMat e * M) u v = M (e u) v := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e u)]
  · simp [permMat]
  · intro b _ hb; simp [permMat, hb]
  · intro h; exact absurd (Finset.mem_univ (e u)) h

lemma mul_permMat {m : Fin 5 → ℕ} (e : V m ≃ V m) (M : Matrix (V m) (V m) ℝ) (u v : V m) :
    (M * permMat e) u v = M u (e.symm v) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm v)]
  · simp [permMat]
  · intro b _ hb
    have : ¬ (v = e b) := by
      intro hbv; exact hb (by rw [hbv, Equiv.symm_apply_apply])
    simp [permMat, this]
  · intro h; exact absurd (Finset.mem_univ (e.symm v)) h

/-- The `D₅` vertex permutations preserve every entry of the normalized Laplacian. -/
theorem balancedPerm_Lap_apply {sigma : Equiv.Perm (Fin 5)} (h : IsD5 sigma)
    (u v : V (fun _ => k)) :
    Lap (fun _ => k) (balancedPerm k sigma u) (balancedPerm k sigma v)
      = Lap (fun _ => k) u v := by
  have hinj : (balancedPerm k sigma u = balancedPerm k sigma v) ↔ (u = v) :=
    ⟨fun hh => (balancedPerm k sigma).injective hh, fun hh => by rw [hh]⟩
  have hN : Nmat (fun _ => k) (balancedPerm k sigma u) (balancedPerm k sigma v)
      = Nmat (fun _ => k) u v := by
    simp only [Nmat_apply, deg_balanced, balancedPerm_apply]
    by_cases hadj : C5adj u.1 v.1
    · rw [if_pos ((h.c5adj u.1 v.1).2 hadj), if_pos hadj]
    · rw [if_neg (fun hc => hadj ((h.c5adj u.1 v.1).1 hc)), if_neg hadj]
  simp only [Lap_apply, hN, Matrix.one_apply]
  by_cases huv : u = v
  · simp [huv]
  · rw [if_neg (fun hc => huv (hinj.1 hc)), if_neg huv]

/-- **The induced `D₅` automorphisms commute with the normalized Laplacian.** -/
theorem balancedPerm_commutes_Lap {sigma : Equiv.Perm (Fin 5)} (h : IsD5 sigma) :
    permMat (balancedPerm k sigma) * Lap (fun _ => k)
      = Lap (fun _ => k) * permMat (balancedPerm k sigma) := by
  ext u v
  rw [permMat_mul, mul_permMat]
  have := balancedPerm_Lap_apply k h u ((balancedPerm k sigma).symm v)
  rw [Equiv.apply_symm_apply] at this
  exact this

end Brockian.UnbalancedPentagon

import Brockian.UnbalancedPentagon.Basic

/-!
# The fibre-constant isometry and the quotient intertwining

We introduce the operators associated with the matrices of `Basic.lean`:

* `Tlin m : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] EuclideanSpace ℝ (V m)`, `(T f) (i, a) = f i / √(m i)`;
* `Tiso hpos`, the same map packaged as a linear isometry;
* `Lop m`, the normalized Laplacian as an operator;
* `Qop m`, the operator `I - Q` on `EuclideanSpace ℝ (Fin 5)`.

The main result is `quotient_intertwining`: `L ∘ T = T ∘ (I - Q)`.
-/

namespace Brockian.UnbalancedPentagon

open Finset Matrix RealInnerProductSpace

variable {m : Fin 5 → ℕ}

/-- Entries of a matrix acting on Euclidean space. -/
lemma toEuclideanLin_apply' {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (A : Matrix p q ℝ) (x : EuclideanSpace ℝ q) (i : p) :
    (Matrix.toEuclideanLin A x) i = ∑ j, A i j * x j := by
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

lemma toEuclideanLin_mul' {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]
    [DecidableEq q] [DecidableEq r] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    Matrix.toEuclideanLin (A * B)
      = (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B) := by
  ext x i
  simp [toEuclideanLin_apply', Finset.mul_sum]

/-! ## The fibre-constant isometry -/

variable (m) in
/-- The fibre-constant map `T`, `(T f) (i, a) = f i / √(m i)`. -/
noncomputable def Tlin : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] EuclideanSpace ℝ (V m) :=
  Matrix.toEuclideanLin (Tmat m)

@[simp] lemma Tlin_apply (f : EuclideanSpace ℝ (Fin 5)) (u : V m) :
    Tlin m f u = f u.1 / Real.sqrt (m u.1) := by
  rw [Tlin, toEuclideanLin_apply', Finset.sum_eq_single u.1]
  · rw [Tmat_apply, if_pos rfl]; ring
  · intro b _ hb; simp [Tmat_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ u.1) h

/-- `T` preserves inner products. -/
lemma Tlin_inner (hpos : ∀ i, 0 < m i) (f g : EuclideanSpace ℝ (Fin 5)) :
    ⟪Tlin m f, Tlin m g⟫ = ⟪f, g⟫ := by
  have h1 : ∀ x y : EuclideanSpace ℝ (V m), ⟪x, y⟫ = ∑ u, x u * y u := by
    intro x y; simp [PiLp.inner_apply, mul_comm]
  have h2 : ∀ x y : EuclideanSpace ℝ (Fin 5), ⟪x, y⟫ = ∑ i, x i * y i := by
    intro x y; simp [PiLp.inner_apply, mul_comm]
  rw [h1, h2, sum_V]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : Real.sqrt (m i) * Real.sqrt (m i) = m i :=
    Real.mul_self_sqrt (le_of_lt (m_pos_real hpos i))
  have hmne : (m i : ℝ) ≠ 0 := ne_of_gt (m_pos_real hpos i)
  have hfib : ∀ a : Fin (m i), Tlin m f ⟨i, a⟩ * Tlin m g ⟨i, a⟩
      = f i * g i / (m i : ℝ) := by
    intro a
    rw [Tlin_apply, Tlin_apply, div_mul_div_comm, hm]
  rw [Finset.sum_congr rfl (fun a _ => hfib a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hmne]

variable (m) in
/-- The fibre-constant isometry `T : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (V m)`. -/
noncomputable def Tiso (hpos : ∀ i, 0 < m i) :
    EuclideanSpace ℝ (Fin 5) →ₗᵢ[ℝ] EuclideanSpace ℝ (V m) :=
  (Tlin m).isometryOfInner (Tlin_inner hpos)

@[simp] lemma Tiso_coe (hpos : ∀ i, 0 < m i) :
    ((Tiso m hpos : EuclideanSpace ℝ (Fin 5) →ₗᵢ[ℝ] EuclideanSpace ℝ (V m)) :
      EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] EuclideanSpace ℝ (V m)) = Tlin m := rfl

lemma Tiso_apply (hpos : ∀ i, 0 < m i) (f : EuclideanSpace ℝ (Fin 5)) (u : V m) :
    Tiso m hpos f u = f u.1 / Real.sqrt (m u.1) := Tlin_apply f u

/-! ## The Laplacian and the quotient operator -/

variable (m) in
/-- The normalized Laplacian as an operator on `EuclideanSpace ℝ (V m)`. -/
noncomputable def Lop : EuclideanSpace ℝ (V m) →ₗ[ℝ] EuclideanSpace ℝ (V m) :=
  Matrix.toEuclideanLin (Lap m)

variable (m) in
/-- The operator `I - Q` on `EuclideanSpace ℝ (Fin 5)`. -/
noncomputable def Qop : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
  Matrix.toEuclideanLin (1 - Qmat m)

/-- **Quotient intertwining**, matrix form: `L T = T (I - Q)`. -/
theorem quotient_intertwining_matrix (hpos : ∀ i, 0 < m i) :
    Lap m * Tmat m = Tmat m * (1 - Qmat m) := by
  rw [Lap, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
    Nmat_eq_Tmat_mul hpos, Matrix.mul_assoc, Matrix.mul_assoc,
    Tmat_transpose_mul_self hpos, Matrix.mul_one]

/-- **Quotient intertwining**: `L ∘ T = T ∘ (I - Q)`. -/
theorem quotient_intertwining (hpos : ∀ i, 0 < m i) :
    (Lop m) ∘ₗ (Tlin m) = (Tlin m) ∘ₗ (Qop m) := by
  rw [Lop, Tlin, Qop, ← toEuclideanLin_mul', ← toEuclideanLin_mul',
    quotient_intertwining_matrix hpos]

end Brockian.UnbalancedPentagon

