/-
  Brockian/ConstellationGlobalSpectrum.lean — Brick 7 (final gate piece): the EXACT
  five-point spectrum of the assembled path-block operator.

  Upstream, everything is proved:
    • Brick 5 (`Brockian.ConstellationSpectrum`): the path-graph Hamiltonians H₁, H₂, H₃
      and their exact characteristic polynomials
          charpoly H₁ = X − 2,
          charpoly H₂ = (X − 1)(X − 3),
          charpoly H₃ = (X − 2)(X² − 4X + 2),
      whose roots form the five-point spectral alphabet {2 − √2, 1, 2, 3, 2 + √2}.
    • Brick 6 (`Brockian.ConstellationBlockSum`): the direct-sum charpoly law
      `charpoly (fromBlocks A 0 0 B) = charpoly A * charpoly B`, and the charpoly of the
      assembled block operator H₁ ⊕ (H₂ ⊕ H₃) as the product of the three block charpolys
      (`H123_charpoly`).

  WHAT THIS BRICK CLOSES (Target 2, concrete form — the spectral gate for the assembled
  operator).  We read the charpoly of the assembled three-block operator
      H₁₂₃ := fromBlocks H₁ 0 0 (fromBlocks H₂ 0 0 H₃)
  down to its exact real root set and prove:

      `H123_spectrum` :  charpoly(H₁₂₃).eval x = 0  ↔  x ∈ {2 − √2, 1, 2, 3, 2 + √2}

  i.e. the spectrum of the assembled path-block operator is EXACTLY the five reals
  {2 − √2, 1, 2, 3, 2 + √2}, with 2 ± √2 handled honestly via (√2)² = 2.  We also record
  the spectrum as a `Set` equality (`H123_spectrum_setEq`) and, via Brick 6's direct-sum
  law, multiplicity forms for repeated blocks (`H2_pow_charpoly`, `H33_mixed_charpoly`)
  showing that block spectra multiply — the mechanism producing the block multiplicities.

  WHAT REMAINS OPEN (honest scope).  This proves the exact spectrum of the ALREADY-
  ASSEMBLED block-diagonal operator H₁ ⊕ H₂ ⊕ H₃.  The remaining, unclaimed final step is
  the GRAPH → BLOCK-DIAGONAL identification: that the adjacency / Hamiltonian operator of
  the twin-admissible +3 constellation graph `G` — proved acyclic, degree ≤ 2, a forest of
  paths capped at 3 vertices upstream — is permutation-similar to such a direct sum of
  P₁/P₂/P₃ path blocks.  That reindexing-by-connected-component similarity (via
  `SimpleGraph.adjMatrix`, `SimpleGraph.ConnectedComponent`, `Matrix.reindex`) is NOT
  established here; it is the genuine open gate.  We do not fake it.

  Verification: no sorry / admit / axiom / native_decide.  Core Mathlib only.
-/
import Mathlib
import Brockian.ConstellationSpectrum
import Brockian.ConstellationBlockSum

namespace Brockian.ConstellationGlobalSpectrum

open Polynomial Matrix
open Brockian.ConstellationSpectrum
open Brockian.ConstellationBlockSum

/-! ### The assembled three-block operator -/

/-- The assembled path-block operator `H₁ ⊕ (H₂ ⊕ H₃)`, over the index type
`Fin 1 ⊕ (Fin 2 ⊕ Fin 3)`. -/
noncomputable def H123 : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 3)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 3)) ℝ :=
  Matrix.fromBlocks H1 0 0 (Matrix.fromBlocks H2 0 0 H3)

/-! ### Target 2 (concrete) — the EXACT five-point spectrum of the assembled operator -/

/-- **The exact spectrum of the assembled path-block operator.**  A real number `x` is an
eigenvalue of `H₁ ⊕ (H₂ ⊕ H₃)` (a root of its characteristic polynomial) if and only if it
is one of the five points `{2 − √2, 1, 2, 3, 2 + √2}`.  The irrational pair `2 ± √2` is the
root pair of the H₃ factor `X² − 4X + 2`, handled via `(√2)² = 2`. -/
theorem H123_spectrum (x : ℝ) :
    H123.charpoly.eval x = 0 ↔
      x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set ℝ) := by
  rw [H123, H123_charpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfac : x ^ 2 - 4 * x + 2
      = (x - (2 - Real.sqrt 2)) * (x - (2 + Real.sqrt 2)) := by
    linear_combination h2
  rw [hfac]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mul_eq_zero, sub_eq_zero]
  tauto

/-- **The spectrum as a set equality.**  The set of real roots of the assembled operator's
characteristic polynomial is exactly the five-point spectral alphabet. -/
theorem H123_spectrum_setEq :
    {x : ℝ | H123.charpoly.eval x = 0}
      = ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set ℝ) := by
  ext x
  simpa using H123_spectrum x

/-- Both of the irrational eigenvalues `2 ± √2` genuinely occur: they are honest roots of
the assembled operator's characteristic polynomial (not merely formal factors). -/
theorem H123_irrational_eigenvalues :
    H123.charpoly.eval (2 - Real.sqrt 2) = 0 ∧
    H123.charpoly.eval (2 + Real.sqrt 2) = 0 := by
  constructor
  · rw [H123_spectrum]; simp
  · rw [H123_spectrum]; simp

/-! ### Target 3 — multiplicity forms: block spectra (and multiplicities) multiply

Via Brick 6's direct-sum charpoly law, assembling repeated copies of a block raises that
block's charpoly to the corresponding power. -/

/-- Three copies of `H₂` assembled as `H₂ ⊕ (H₂ ⊕ H₂)` have charpoly `((X−1)(X−3))³`: the
block spectrum appears with multiplicity three.  Together with Brick 6's `H2_twice_charpoly`
(exponent two) this exhibits the general `n`-copies → `n`-th-power multiplicity law. -/
theorem H2_pow_charpoly :
    (Matrix.fromBlocks H2 0 0 (Matrix.fromBlocks H2 0 0 H2)).charpoly =
      ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 3)) ^ 3 := by
  simp only [Matrix.charpoly_fromBlocks_zero₂₁, H2_charpoly]
  ring

/-- A mixed assembly `H₃ ⊕ (H₃ ⊕ H₂)` carries the H₃ spectrum with multiplicity two and the
H₂ spectrum with multiplicity one: charpoly `= ((X−2)(X²−4X+2))² · (X−1)(X−3)`.  Distinct
blocks contribute independent multiplicities in the product. -/
theorem H33_mixed_charpoly :
    (Matrix.fromBlocks H3 0 0 (Matrix.fromBlocks H3 0 0 H2)).charpoly =
      ((Polynomial.X - Polynomial.C 2) *
          (Polynomial.X ^ 2 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2)) ^ 2 *
        ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 3)) := by
  simp only [Matrix.charpoly_fromBlocks_zero₂₁, H3_charpoly, H2_charpoly]
  ring

end Brockian.ConstellationGlobalSpectrum
