/-
  Brockian/ConstellationBlockSum.lean — Brick 6: the direct-sum / block-diagonal
  characteristic-polynomial law, giving the spectrum of the assembled path-block operator
  as the product of block spectra.

  Building on Brick 5 (`Brockian.ConstellationSpectrum`), which fixes the path-graph
  Hamiltonians and their exact characteristic polynomials:
      H₁ = !![2]                     charpoly H₁ = X − 2
      H₂ = !![2,-1; -1,2]            charpoly H₂ = (X − 1)(X − 3)
      H₃ = !![2,-1,0; -1,2,-1; 0,-1,2]  charpoly H₃ = (X − 2)(X² − 4X + 2)

  Theorem 1 (load-bearing) is the DIRECT-SUM charpoly law: for square matrices A over
  `Fin m` and B over `Fin n` (entries in a commutative ring), the block-diagonal matrix
  `fromBlocks A 0 0 B` has characteristic polynomial `A.charpoly * B.charpoly`.  Mathlib
  already provides this as `Matrix.charpoly_fromBlocks_zero₂₁` (via `charmatrix_fromBlocks`
  + `det_fromBlocks_zero₂₁`); we restate it in the exact `fromBlocks A 0 0 B` shape used
  by the constellation program and cite the Mathlib result for the proof.

  Theorem 2 assembles ONE copy of each path block, `H₁ ⊕ (H₂ ⊕ H₃)` as an iterated
  `fromBlocks`, and computes its charpoly as the product of the three block charpolys —
  i.e. the full five-point spectral alphabet {2 − √2, 1, 2, 3, 2 + √2} with the block
  multiplicities carried by the assembly.  Two auxiliary instances (`H₂ ⊕ H₃`, and two
  copies of `H₂`) show concretely that block spectra — and their multiplicities — multiply.

  HONEST SCOPE: this shows that IF the wheel / constellation operator is (similar to) the
  direct sum of its path components, THEN its spectrum is exactly the five-point alphabet
  with the block multiplicities.  The graph → block-diagonal PERMUTATION SIMILARITY itself
  remains a separate, unclaimed gate; it is NOT established here.

  Verification: no sorry / admit / axiom / native_decide.  Core Mathlib only.
-/
import Mathlib
import Brockian.ConstellationSpectrum

namespace Brockian.ConstellationBlockSum

open Polynomial Matrix
open Brockian.ConstellationSpectrum

/-! ### Theorem 1 — the direct-sum / block-diagonal characteristic-polynomial law -/

/-- **Direct-sum charpoly law.**  For square matrices `A` over `Fin m` and `B` over
`Fin n` (entries in a commutative ring `R`), the block-diagonal matrix `fromBlocks A 0 0 B`
has characteristic polynomial equal to the product `A.charpoly * B.charpoly`.

Proof: `charmatrix (fromBlocks A 0 0 B) = fromBlocks (charmatrix A) 0 0 (charmatrix B)`
(the off-diagonal `0` blocks stay `0` under `charmatrix = X•1 − map C M`), and the
determinant of a block-triangular matrix with a zero lower-left block factors as the
product of the diagonal blocks' determinants; Mathlib packages exactly this as
`Matrix.charpoly_fromBlocks_zero₂₁`. -/
theorem charpoly_fromBlocks_zero {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    (Matrix.fromBlocks A 0 0 B).charpoly = A.charpoly * B.charpoly :=
  Matrix.charpoly_fromBlocks_zero₂₁ A 0 B

/-! ### Theorem 2 — the assembled path-block spectrum multiplies

We assemble one copy of each block as the iterated direct sum `H₁ ⊕ (H₂ ⊕ H₃)`, over the
index type `Fin 1 ⊕ (Fin 2 ⊕ Fin 3)`, and read off its charpoly as the product of the
three block charpolys via two applications of Theorem 1 plus the Brick 5 factorizations. -/

/-- Charpoly of the two-block assembly `H₂ ⊕ H₃`: the product of the H₂ and H₃ spectra. -/
theorem H23_charpoly :
    (Matrix.fromBlocks H2 0 0 H3).charpoly =
      ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 3)) *
        ((Polynomial.X - Polynomial.C 2) *
          (Polynomial.X ^ 2 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2)) := by
  rw [charpoly_fromBlocks_zero, H2_charpoly, H3_charpoly]

/-- Charpoly of the full assembled path-block operator `H₁ ⊕ (H₂ ⊕ H₃)`: the product of
all three block charpolys, i.e. the five-point spectral alphabet
`{2 − √2, 1, 2, 3, 2 + √2}` carried with the block multiplicities. -/
theorem H123_charpoly :
    (Matrix.fromBlocks H1 0 0 (Matrix.fromBlocks H2 0 0 H3)).charpoly =
      (Polynomial.X - Polynomial.C 2) *
        ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 3)) *
        ((Polynomial.X - Polynomial.C 2) *
          (Polynomial.X ^ 2 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2)) := by
  -- The inner block `H₂ ⊕ H₃` is over the sum type `Fin 2 ⊕ Fin 3`, so we invoke the
  -- general Mathlib direct-sum law (not the `Fin`-restricted Theorem 1) for the outer split.
  simp only [Matrix.charpoly_fromBlocks_zero₂₁, H1_charpoly, H2_charpoly, H3_charpoly]
  ring

/-- **Multiplicity demonstration.**  Two copies of `H₂` assembled as `H₂ ⊕ H₂` have
charpoly `((X − 1)(X − 3))²`: the block spectrum appears with doubled multiplicity.  This
is the mechanism by which `n` copies of a block raise the block charpoly to the `n`-th
power. -/
theorem H2_twice_charpoly :
    (Matrix.fromBlocks H2 0 0 H2).charpoly =
      ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 3)) ^ 2 := by
  rw [charpoly_fromBlocks_zero, H2_charpoly, sq]

end Brockian.ConstellationBlockSum
