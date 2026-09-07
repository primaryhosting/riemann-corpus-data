/-
  Brockian/PentagonCharacterMultiplicity.lean

  **Cayley-graph spectrum from character theory (the pentagon case).**

  The two source files this module joins already sit at opposite ends of the same
  classical bridge:

    * `Brockian.PentagonMultiplicities` computes the *geometric multiplicities*
      of the C₅ adjacency operator `adjL` as honest Mathlib `finrank`s of the
      abstract eigenspaces `ker(adjL − μ·id)`:
          dim(eigenspace 2) = 1,  dim(eigenspace (φ−1)) = 2,  dim(eigenspace (−φ)) = 2.

    * `Brockian.D5CharacterComplete` builds the full irreducible character table of
      `D₅ = DihedralGroup 5`, in particular the two-dimensional *golden* irrep
      character `chiGolden` (values `2, φ−1, −φ, 0`) and its conjugate
      `chiConjugate`, together with the normalized character inner product
      `charInner ⟨χ,ψ⟩ = (1/|G|) Σ_g χ(g)·conj ψ(g)`.

  The classical principle relating them is:

      **the geometric multiplicity of an eigenvalue of the Cayley-graph adjacency
      operator equals the dimension of the corresponding irreducible
      representation — and that dimension is exactly the character value at the
      identity, `χ(1)`.**

  This file makes that identity literal for the golden eigenvalue φ−1 (and its
  conjugate companion −φ):

      dim (eigenspace_{φ−1}) = χ_golden(1) = 2,
      dim (eigenspace_{−φ})  = χ_conj(1)   = 2,
      dim (eigenspace_{2})   = χ_triv(1)   = 1.

  ## What is proved
    * `chiGolden_one`, `chiConjugate_one` — the character value at the identity is
      the irrep dimension (`= 2`), via `one_eq_r0` + `goldenRot_zero`/`conjRot_zero`.
    * `golden_multiplicity_eq_irrep_dim`, `neg_golden_multiplicity_eq_irrep_dim`
      — **THE GEM**: `finrank (eigenspace_μ adjL) = χ(1)` cast to `ℂ`, for the
      golden pair.
    * `multiplicity_table` — the full three-row multiplicity/dimension check
      `(1, 2, 2) = (χ_triv 1, χ_golden 1, χ_conj 1)`.
    * `golden_self_inner` — self-orthonormality `⟨χ_golden, χ_golden⟩ = 1`
      (the normalization backing "appears once"; = `row_GG`).
    * `permCharacter`, `permInner_golden`, `golden_isotypic_multiplicity`
      — the **inner-product refinement**: with the vertex permutation character
      `χ_perm` (fixed-point counts `r⁰↦5, rᵏ≠⁰↦0, reflections↦1`) one has
      `⟨χ_perm, χ_golden⟩ = 1`, so the golden irrep occurs *once* in the vertex
      permutation representation and the eigenspace dimension factors as
          dim(eigenspace_{φ−1}) = dim(χ_golden) · ⟨χ_perm, χ_golden⟩ = 2 · 1 = 2.

  ## Honesty note on `permCharacter`
    `permCharacter` is defined directly by the fixed-point counts of the `D₅`
    action on the five pentagon vertices — `r⁰` fixes all 5, a nontrivial rotation
    fixes 0, and each of the five reflections fixes exactly 1 vertex (n = 5 odd).
    These counts ARE the values of the permutation character (the permutation
    character of any permutation representation equals its fixed-point-count
    function).  We do NOT re-derive them here as traces of the concrete
    `d5Pull` permutation matrices — that trace-vs-fixed-points identification is
    the one link left as an elementary geometric fact rather than a formal lemma.
    Everything computed from `permCharacter` (the inner product, the multiplicity)
    is proved.

    No `sorry`/`admit`, no `native_decide`, no new axiom.  Axiom-clean modulo
    `{propext, Classical.choice, Quot.sound}`.  Verified on AXLE at `lean-4.32.0`.
-/
import Mathlib
import Brockian.PentagonMultiplicities
import Brockian.D5CharacterComplete

open BigOperators
open Module
open DihedralGroup
open Brockian.PentagonMultiplicities
open Brockian.D5CharacterComplete

namespace Brockian.PentagonCharacterMultiplicity

/-! ### (1) The character value at the identity is the irrep dimension -/

/-- The golden irrep character evaluated at the identity equals its dimension `2`.
`χ_golden(1) = χ_golden(r⁰) = goldenRot 0 = 2`. -/
theorem chiGolden_one : chiGolden (1 : DihedralGroup 5) = 2 := by
  rw [one_eq_r0, chiGolden_r]; exact goldenRot_zero

/-- The conjugate irrep character evaluated at the identity equals its dimension
`2`. `χ_conj(1) = χ_conj(r⁰) = conjRot 0 = 2`. -/
theorem chiConjugate_one : chiConjugate (1 : DihedralGroup 5) = 2 := by
  rw [one_eq_r0, chiConjugate_r]; exact conjRot_zero

/-! ### (2) THE GEM — eigenvalue multiplicity = irreducible-representation dimension -/

/-- **Cayley-spectrum from character theory.** The geometric multiplicity of the
golden eigenvalue φ−1 in the C₅ adjacency operator equals the dimension of the
golden irreducible D₅-representation, i.e. the value of its character at the
identity:
    dim (eigenspace_{φ−1}) = χ_golden(1) = 2. -/
theorem golden_multiplicity_eq_irrep_dim :
    (finrank ℂ (Module.End.eigenspace Brockian.PentagonMultiplicities.adjL
        ((Real.goldenRatio - 1 : ℝ) : ℂ)) : ℂ) = chiGolden (1 : DihedralGroup 5) := by
  rw [finrank_eigenspace_golden, chiGolden_one]
  norm_num

/-- The `−φ` companion: the geometric multiplicity of the eigenvalue `−φ` equals
the dimension of the *conjugate* golden irrep, `χ_conj(1) = 2`. -/
theorem neg_golden_multiplicity_eq_irrep_dim :
    (finrank ℂ (Module.End.eigenspace Brockian.PentagonMultiplicities.adjL
        ((-Real.goldenRatio : ℝ) : ℂ)) : ℂ) = chiConjugate (1 : DihedralGroup 5) := by
  rw [finrank_eigenspace_neg_golden, chiConjugate_one]
  norm_num

/-! ### (3) Inner-product refinement — the golden irrep appears exactly once -/

/-- Self-orthonormality of the golden irrep: `⟨χ_golden, χ_golden⟩ = 1`.  This is
the normalization backing the statement that the golden irrep appears *once* as a
constituent — reused from the first orthogonality relation (`row_GG`). -/
theorem golden_self_inner : charInner chiGolden chiGolden = 1 := row_GG

/-- The **vertex permutation character** of the `D₅` action on the five pentagon
vertices, given by its fixed-point counts: the identity `r⁰` fixes all `5`
vertices, a nontrivial rotation `rᵏ` (`k ≠ 0`) fixes none, and each of the five
reflections fixes exactly one vertex.  (See the honesty note in the file header.) -/
noncomputable def permCharacter : DihedralGroup 5 → ℂ
  | r k => if k = 0 then 5 else 0
  | sr _ => 1

@[simp] theorem permCharacter_r (k : Fin 5) :
    permCharacter (r k) = if k = 0 then 5 else 0 := rfl
@[simp] theorem permCharacter_sr (k : Fin 5) : permCharacter (sr k) = 1 := rfl

/-- **Multiplicity of the golden irrep in the vertex permutation representation is
`1`.**  `⟨χ_perm, χ_golden⟩ = (1/|G|) Σ_g χ_perm(g)·conj χ_golden(g) = 1`: only the
identity term survives on rotations (`5·χ_golden(1) = 5·2 = 10`) and reflections
contribute `0` (`χ_golden` vanishes there), giving `(1/10)·10 = 1`. -/
theorem permInner_golden : charInner permCharacter chiGolden = 1 := by
  rw [charInner_eq_pairSum _ _ chiGolden_real, pairSum_split]
  have hr : ∑ k : Fin 5, permCharacter (r k) * chiGolden (r k) = 10 := by
    simp only [Fin.sum_univ_five, permCharacter_r, chiGolden_r, goldenRot_zero,
      Fin.reduceEq, reduceIte]
    norm_num
  have hs : ∑ k : Fin 5, permCharacter (sr k) * chiGolden (sr k) = 0 := by
    simp [chiGolden_sr]
  rw [hr, hs]; norm_num

/-- **The eigenspace dimension factors through the irrep dimension.**  The
geometric multiplicity of the golden eigenvalue φ−1 equals the dimension of the
golden irrep times the number of times it occurs in the vertex permutation
representation:
    dim (eigenspace_{φ−1}) = dim(χ_golden) · ⟨χ_perm, χ_golden⟩ = χ_golden(1) · 1 = 2. -/
theorem golden_isotypic_multiplicity :
    (finrank ℂ (Module.End.eigenspace Brockian.PentagonMultiplicities.adjL
        ((Real.goldenRatio - 1 : ℝ) : ℂ)) : ℂ)
      = chiGolden (1 : DihedralGroup 5) * charInner permCharacter chiGolden := by
  rw [permInner_golden, mul_one]
  exact golden_multiplicity_eq_irrep_dim

/-! ### (4) The full multiplicity / dimension table -/

/-- **The pentagon multiplicity table equals the D₅ irrep-dimension column.**  The
three geometric multiplicities `(1, 2, 2)` of the eigenvalues `2, φ−1, −φ` of the
C₅ adjacency operator coincide with the dimensions of the trivial, golden, and
conjugate-golden irreducible D₅-representations, each read off as the character
value at the identity `χ(1)`. -/
theorem multiplicity_table :
    (finrank ℂ (Module.End.eigenspace Brockian.PentagonMultiplicities.adjL (2:ℂ)) : ℂ)
        = chiTrivial 1 ∧
    (finrank ℂ (Module.End.eigenspace Brockian.PentagonMultiplicities.adjL
        ((Real.goldenRatio - 1:ℝ):ℂ)) : ℂ) = chiGolden 1 ∧
    (finrank ℂ (Module.End.eigenspace Brockian.PentagonMultiplicities.adjL
        ((-Real.goldenRatio:ℝ):ℂ)) : ℂ) = chiConjugate 1 := by
  refine ⟨?_, golden_multiplicity_eq_irrep_dim, neg_golden_multiplicity_eq_irrep_dim⟩
  rw [finrank_eigenspace_two, chiTrivial_one]
  norm_num

end Brockian.PentagonCharacterMultiplicity
