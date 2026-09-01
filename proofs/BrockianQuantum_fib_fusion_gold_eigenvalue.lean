import Mathlib
/-!
# Fibonacci-anyon topological quantum computation (Brockian pentagon/golden bridge).
Uses Mathlib's `goldenRatio` (φ, with `gold_sq : φ^2 = φ + 1`). Bare `import Mathlib`; no
non-core/Archive namespaces or invented lemmas. These are TRUE algebraic facts (formalization of
known topological-QC algebra, not new physics).
-/
namespace BrockianQuantum
open Matrix Real

/-- **Quantum dimension.** The Fibonacci fusion matrix `N = [[0,1],[1,1]]` (rule `τ×τ = 1 ⊕ τ`) has
characteristic polynomial `X² − X − 1`, so the golden ratio φ (its Perron eigenvalue) is the
quantum dimension of the τ anyon: `charpoly` evaluated at φ is `0`. -/
theorem fib_fusion_gold_eigenvalue :
    (Matrix.of ![![(0:ℝ), 1], ![1, 1]]).charpoly.eval goldenRatio = 0 := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]

/-- **F-move consistency.** The real Fibonacci F-matrix
`F = [[1/φ, √(1/φ)], [√(1/φ), −1/φ]]` is involutory, `F² = 1` (needs `φ² = φ + 1`, equivalently
`1/φ² + 1/φ = 1`). -/
theorem fibonacci_F_involutory :
    (Matrix.of ![![goldenRatio⁻¹, Real.sqrt goldenRatio⁻¹],
                 ![Real.sqrt goldenRatio⁻¹, -goldenRatio⁻¹]]) ^ 2 = 1 := by
  -- Abstract away φ: only `0 < φ`, `φ² = φ + 1` and `√(1/φ)² = 1/φ` are used.
  suffices H : ∀ g s : ℝ, 0 < g → g ^ 2 = g + 1 → s * s = g⁻¹ →
      (Matrix.of ![![g⁻¹, s], ![s, -g⁻¹]]) ^ 2 = 1 from
    H goldenRatio (Real.sqrt goldenRatio⁻¹) Real.goldenRatio_pos Real.goldenRatio_sq
      (Real.mul_self_sqrt (inv_pos.mpr Real.goldenRatio_pos).le)
  intro g s hg hg2 hs
  have key : g⁻¹ * g⁻¹ + g⁻¹ = 1 := by
    field_simp
    nlinarith [hg2]
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [hs, key]

end BrockianQuantum

