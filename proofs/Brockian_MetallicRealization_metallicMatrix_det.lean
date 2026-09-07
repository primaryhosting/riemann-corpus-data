/-
  Brockian/MetallicRealization.lean — a genuine spectral realization of the
  metallic means.

  The golden mean `φ` appears in the C₅ adjacency spectrum as `φ − 1 = 2cos(2π/5)`
  (see `Brockian.Spectral.golden_unique_to_five`).  The *metallic means*
  `M_a = (a + √(a²+4))/2` (a = 1 golden, a = 2 silver, …), already pinned in
  `Brockian.MetallicFamily`, generalize `φ` as the roots of `x² − a·x − 1`.

  This file exhibits each metallic mean as a genuine **eigenvalue of a concrete
  2×2 real symmetric matrix** — the "metallic transfer / weighted-adjacency
  matrix"

        metallicMatrix a = !![a, 1; 1, 0]

  (for `a = 1` this is exactly the Fibonacci Q-matrix `!![1,1;1,0]`).  We prove
  its characteristic polynomial is `X² − a·X − 1`, that `M_a` and its conjugate
  `m_a` are precisely its two eigenvalues (with explicit eigenvectors and via
  Mathlib's `Module.End.HasEigenvalue`), that trace = `M_a + m_a` and
  det = `M_a · m_a`, and that `M_a` is a root of the degree-2 polynomial.  We
  also record the **honest scoping fact** distinguishing this from the C₅ story:
  for `a ≥ 2` the metallic mean exceeds `2`, so — unlike the golden value
  `φ − 1 < 2` — it can NOT be a cycle-adjacency eigenvalue (those lie in
  `[−2,2]`); the transfer-matrix realization is the correct carrier.

  ## What is proved
  * `metallicMatrix a := !![a,1;1,0]`, a real **symmetric** (weighted-adjacency)
    matrix; `metallicMatrix_isSymm`.
  * `metallicMatrix_trace = a`, `metallicMatrix_det = -1`; hence
    `trace = M_a + m_a` (`trace_eq_sum_roots`) and `det = M_a · m_a`
    (`det_eq_prod_roots`).
  * `metallicMatrix_charpoly`: the characteristic polynomial is
    `X² − C a · X − 1`; `metallicMatrix_charpoly_natDegree = 2` (degree exactly 2).
  * `metallicPoly_factor`: `x² − a·x − 1 = (x − M_a)(x − m_a)` over ℝ.
  * `metallicMatrix_mulVec_mean` / `_conj`: explicit eigenvectors `![M_a,1]`,
    `![m_a,1]` with eigenvalues `M_a`, `m_a`.
  * `metallicMatrix_eigenvalue_iff`: `charpoly.eval x = 0 ↔ x = M_a ∨ x = m_a`
    (the spectrum is *exactly* the two metallic roots).
  * `metallicMatrix_hasEigenvalue_mean` / `_conj`: `M_a`, `m_a` are eigenvalues
    in Mathlib's `Module.End.HasEigenvalue (toLin' (metallicMatrix a))` sense.
  * `metallicMean_isRoot`: `M_a` is a root of the monic degree-2 `X² − C a·X − 1`.
  * Golden `a = 1` consistency: `metallicMatrix_one = !![1,1;1,0]` (Fibonacci
    Q-matrix), `fibQ_charpoly = X² − X − 1`, `fibQ_mulVec_golden`,
    `golden_hasEigenvalue`.
  * `metallicMean_irrational`: for natural `n` with `n²+4` not a perfect square,
    `M_n` is irrational (so it is NOT rational — degree ≥ 2 over ℚ); corollary
    `goldenRatio_irrational`.
  * Scoping: `two_lt_metallicMean` (`a ≥ 2 ⇒ M_a > 2`) and
    `metallicMean_notMem_cycleSpectrum` / `metallicMean_two_notMem_cycleSpectrum`
    (`a ≥ 2 ⇒ M_a ∉ cycleSpectrum n`, since that set ⊆ [−2,2]).

  ## What is NOT proved
  * We do NOT claim the metallic means for `a ≥ 2` are cycle-graph eigenvalues —
    they provably are not (`metallicMean_notMem_cycleSpectrum`).  The genuine
    graph realization here is the 2-vertex weighted graph with adjacency
    `!![a,1;1,0]` (self-loop weight `a` at one vertex, unit edge), NOT the
    n-cycle.  The golden C₅ appearance is a *separate*, smaller-value phenomenon
    (`φ − 1 < 2`) proved elsewhere and only cited.
  * We do NOT formalize the `minpoly ℚ (M_n)` object or prove `minpoly` has
    degree exactly 2.  We instead prove the two facts that pin the algebraic
    degree at 2: `M_a` is a root of a monic degree-2 polynomial (degree ≤ 2) and,
    for non-square `n²+4`, `M_n` is irrational (not degree 1).  Irreducibility of
    `X² − a·X − 1` over ℚ and the `minpoly` identity are left to a later file.
  * No claim that `a ≥ 2` metallic means arise in any Brockian pentagonal
    context; this file is purely the algebra/linear-algebra realization.

  Verification: no sorry/admit/axioms beyond Mathlib's; AXLE @ lean-4.32.0.
-/
import Mathlib
import Brockian.MetallicFamily
import Brockian.CycleSpectrumFamily

namespace Brockian.MetallicRealization

open Brockian.MetallicFamily
open Brockian.Spectral
open Matrix Polynomial

/-! ### The metallic transfer / weighted-adjacency matrix -/

/-- **The metallic transfer matrix** `!![a, 1; 1, 0]`.  This is the (real
symmetric) weighted-adjacency matrix of the 2-vertex graph with a self-loop of
weight `a` at vertex `0` and a unit edge between the two vertices.  For `a = 1`
it is the Fibonacci Q-matrix. -/
def metallicMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 1; 1, 0]

/-- The metallic matrix is symmetric — a genuine weighted-adjacency matrix. -/
theorem metallicMatrix_isSymm (a : ℝ) : (metallicMatrix a).IsSymm := by
  show (metallicMatrix a)ᵀ = metallicMatrix a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metallicMatrix, Matrix.transpose_apply]

/-- Trace of the metallic matrix is `a` (= sum of eigenvalues). -/
theorem metallicMatrix_trace (a : ℝ) : (metallicMatrix a).trace = a := by
  unfold metallicMatrix
  rw [Matrix.trace_fin_two_of]
  ring

/-- Determinant of the metallic matrix is `-1` (= product of eigenvalues). -/
theorem metallicMatrix_det (a : ℝ) : (metallicMatrix a).det = -1 := by
  unfold metallicMatrix
  rw [Matrix.det_fin_two_of]
  ring

/-! ### Characteristic polynomial -/

/-- **The characteristic polynomial is `X² − a·X − 1`.** -/
theorem metallicMatrix_charpoly (a : ℝ) :
    (metallicMatrix a).charpoly = X ^ 2 - C a * X - 1 := by
  rw [Matrix.charpoly_fin_two, metallicMatrix_trace, metallicMatrix_det, map_neg, map_one]
  ring

/-- The characteristic polynomial has degree exactly `2`. -/
theorem metallicMatrix_charpoly_natDegree (a : ℝ) :
    (metallicMatrix a).charpoly.natDegree = 2 := by
  rw [Matrix.charpoly_natDegree_eq_dim]
  simp

/-- Hence `X² − a·X − 1` itself has degree `2`. -/
theorem metallicPoly_natDegree (a : ℝ) :
    (X ^ 2 - C a * X - 1 : Polynomial ℝ).natDegree = 2 := by
  rw [← metallicMatrix_charpoly]
  exact metallicMatrix_charpoly_natDegree a

/-! ### The two metallic roots are exactly the eigenvalues -/

/-- Factorization over ℝ: `x² − a·x − 1 = (x − M_a)(x − m_a)`. -/
theorem metallicPoly_factor (a x : ℝ) :
    x ^ 2 - a * x - 1 = (x - metallicMean a) * (x - metallicConj a) := by
  linear_combination x * metallicMean_add_conj a - metallicMean_mul_conj a

/-- **Explicit eigenvector for `M_a`.**  `![M_a, 1]` satisfies
`(metallicMatrix a) *ᵥ ![M_a,1] = M_a • ![M_a,1]` (uses `M_a² = a·M_a + 1`). -/
theorem metallicMatrix_mulVec_mean (a : ℝ) :
    (metallicMatrix a).mulVec ![metallicMean a, 1]
      = metallicMean a • ![metallicMean a, 1] := by
  funext i
  fin_cases i <;>
    simp [metallicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] <;>
    nlinarith [metallicMean_sq a]

/-- **Explicit eigenvector for the conjugate `m_a`.** -/
theorem metallicMatrix_mulVec_conj (a : ℝ) :
    (metallicMatrix a).mulVec ![metallicConj a, 1]
      = metallicConj a • ![metallicConj a, 1] := by
  funext i
  fin_cases i <;>
    simp [metallicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] <;>
    nlinarith [metallicConj_sq a]

/-- **The spectrum is exactly `{M_a, m_a}`.**  A real `x` is a root of the
characteristic polynomial iff `x = M_a` or `x = m_a`. -/
theorem metallicMatrix_eigenvalue_iff (a x : ℝ) :
    (metallicMatrix a).charpoly.eval x = 0 ↔ x = metallicMean a ∨ x = metallicConj a := by
  rw [metallicMatrix_charpoly]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
  rw [metallicPoly_factor a x, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- `M_a` is a root of the monic degree-2 polynomial `X² − C a·X − 1`. -/
theorem metallicMean_isRoot (a : ℝ) :
    (X ^ 2 - C a * X - 1 : Polynomial ℝ).eval (metallicMean a) = 0 := by
  rw [← metallicMatrix_charpoly]
  exact (metallicMatrix_eigenvalue_iff a (metallicMean a)).mpr (Or.inl rfl)

/-- `m_a` is a root of the same polynomial. -/
theorem metallicConj_isRoot (a : ℝ) :
    (X ^ 2 - C a * X - 1 : Polynomial ℝ).eval (metallicConj a) = 0 := by
  rw [← metallicMatrix_charpoly]
  exact (metallicMatrix_eigenvalue_iff a (metallicConj a)).mpr (Or.inr rfl)

/-! ### Eigenvalues in Mathlib's `Module.End.HasEigenvalue` sense -/

/-- `![M_a, 1]` is nonzero. -/
theorem eigvec_mean_ne_zero (a : ℝ) : (![metallicMean a, 1] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp at h1

/-- `![m_a, 1]` is nonzero. -/
theorem eigvec_conj_ne_zero (a : ℝ) : (![metallicConj a, 1] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp at h1

/-- **`M_a` is an eigenvalue** of `toLin' (metallicMatrix a)`. -/
theorem metallicMatrix_hasEigenvalue_mean (a : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (metallicMatrix a)) (metallicMean a) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := (![metallicMean a, 1] : Fin 2 → ℝ))
  refine ⟨?_, eigvec_mean_ne_zero a⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact metallicMatrix_mulVec_mean a

/-- **`m_a` is an eigenvalue** of `toLin' (metallicMatrix a)`. -/
theorem metallicMatrix_hasEigenvalue_conj (a : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (metallicMatrix a)) (metallicConj a) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := (![metallicConj a, 1] : Fin 2 → ℝ))
  refine ⟨?_, eigvec_conj_ne_zero a⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact metallicMatrix_mulVec_conj a

/-! ### Trace / determinant as symmetric functions of the eigenvalues -/

/-- Trace equals the sum of the two metallic eigenvalues. -/
theorem trace_eq_sum_roots (a : ℝ) :
    (metallicMatrix a).trace = metallicMean a + metallicConj a := by
  rw [metallicMatrix_trace, metallicMean_add_conj]

/-- Determinant equals the product of the two metallic eigenvalues. -/
theorem det_eq_prod_roots (a : ℝ) :
    (metallicMatrix a).det = metallicMean a * metallicConj a := by
  rw [metallicMatrix_det, metallicMean_mul_conj]

/-! ### Golden `a = 1` specialization (Fibonacci Q-matrix) -/

/-- For `a = 1` the metallic matrix is the Fibonacci Q-matrix `!![1,1;1,0]`. -/
theorem metallicMatrix_one : metallicMatrix (1 : ℝ) = !![1, 1; 1, 0] := rfl

/-- The Fibonacci Q-matrix has characteristic polynomial `X² − X − 1`. -/
theorem fibQ_charpoly :
    (metallicMatrix 1).charpoly = X ^ 2 - X - 1 := by
  rw [metallicMatrix_charpoly, map_one, one_mul]

/-- The golden ratio is an eigenvalue of the Fibonacci Q-matrix, with eigenvector
`![φ, 1]` — the `a = 1` instance of `metallicMatrix_mulVec_mean`. -/
theorem fibQ_mulVec_golden :
    (metallicMatrix 1).mulVec ![Real.goldenRatio, 1]
      = Real.goldenRatio • ![Real.goldenRatio, 1] := by
  have h := metallicMatrix_mulVec_mean 1
  rwa [metallicMean_one] at h

/-- The golden ratio `φ` is an eigenvalue of `toLin' (metallicMatrix 1)`. -/
theorem golden_hasEigenvalue :
    Module.End.HasEigenvalue (Matrix.toLin' (metallicMatrix 1)) Real.goldenRatio := by
  have h := metallicMatrix_hasEigenvalue_mean 1
  rwa [metallicMean_one] at h

/-! ### Algebraic degree: irrationality of the metallic mean -/

/-- **For natural `n` with `n²+4` not a perfect square, `M_n` is irrational.**
Combined with `metallicMean_isRoot` (a root of a monic degree-2 polynomial),
this pins the algebraic degree of `M_n` over ℚ at exactly `2`. -/
theorem metallicMean_irrational {n : ℕ} (h : ¬ IsSquare (n ^ 2 + 4)) :
    Irrational (metallicMean (n : ℝ)) := by
  have hcast : ((n : ℝ) ^ 2 + 4) = ((n ^ 2 + 4 : ℕ) : ℝ) := by push_cast; ring
  have hsqrt : Irrational (Real.sqrt ((n ^ 2 + 4 : ℕ) : ℝ)) :=
    irrational_sqrt_natCast_iff.mpr h
  have hstep : Irrational ((Real.sqrt ((n ^ 2 + 4 : ℕ) : ℝ) + (n : ℝ)) / 2) := by
    have h1 := hsqrt.add_natCast n
    have h2 := h1.div_natCast (m := 2) (by norm_num)
    simpa using h2
  have heq : metallicMean (n : ℝ)
      = (Real.sqrt ((n ^ 2 + 4 : ℕ) : ℝ) + (n : ℝ)) / 2 := by
    unfold metallicMean
    rw [hcast]
    ring
  rw [heq]
  exact hstep

/-- **The golden ratio is irrational** — the `n = 1` instance (`1²+4 = 5` is not a
square), recovering the classical fact from the metallic realization. -/
theorem goldenRatio_irrational : Irrational Real.goldenRatio := by
  have h : ¬ IsSquare (1 ^ 2 + 4) := by norm_num
  have hirr := metallicMean_irrational (n := 1) h
  rwa [show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num, metallicMean_one] at hirr

/-! ### Honesty boundary: metallic means (a ≥ 2) are NOT cycle eigenvalues -/

/-- For `a ≥ 2`, the metallic mean strictly exceeds `2`. -/
theorem two_lt_metallicMean {a : ℝ} (ha : 2 ≤ a) : 2 < metallicMean a := by
  have hs2 : (2 : ℝ) < Real.sqrt (a ^ 2 + 4) := by
    have h4 : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
    apply Real.sqrt_lt_sqrt (by norm_num)
    nlinarith [ha]
  unfold metallicMean
  linarith [hs2, ha]

/-- **Scoping fact.**  For `a ≥ 2`, `M_a ∉ cycleSpectrum n` for every `n`: the
cycle-adjacency spectrum lies in `[−2, 2]`, but `M_a > 2`.  So metallic means
beyond the golden case are realized by the transfer matrix, not the cycle graph. -/
theorem metallicMean_notMem_cycleSpectrum {a : ℝ} (ha : 2 ≤ a) (n : ℕ) :
    metallicMean a ∉ cycleSpectrum n := by
  intro hmem
  have hle := Brockian.CycleSpectrumFamily.cycleSpectrum_le_two hmem
  linarith [two_lt_metallicMean ha]

/-- The silver mean `M_2 = 1 + √2` is not a cycle-adjacency eigenvalue. -/
theorem metallicMean_two_notMem_cycleSpectrum (n : ℕ) :
    metallicMean 2 ∉ cycleSpectrum n :=
  metallicMean_notMem_cycleSpectrum (by norm_num) n

end Brockian.MetallicRealization
