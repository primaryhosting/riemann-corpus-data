/-
  Brockian/PentagonMultiplicities.lean

  The C₅ adjacency spectrum at the Mathlib *eigenspace / finrank* level.

  `Brockian.PentagonIsotypic` diagonalized the pentagon adjacency operator
  `A = ρ + ρ⁻¹` on `VertexSpace = Fin 5 → ℂ` "operationally": it produced the
  Fourier eigenmodes `eigenmode k`, the eigenvalue map `adjEigenvalue k`, the
  eigenbasis `eigenBasis`, and the frequency partition `{0}, {1,4}, {2,3}`
  carrying eigenvalues `2, φ−1, −φ`.  It EXPLICITLY LEFT OPEN the restatement
  through Mathlib's abstract `Module.End.eigenspace` / `Module.finrank` API: the
  geometric multiplicities `1, 2, 2` were proven only as `Finset.card` of the
  frequency groups, not as dimensions of kernels `ker (A − μ·id)`.

  This module closes that gap.  The adjacency operator is packaged as a genuine
  `adjL : Module.End ℂ VertexSpace` and every eigenspace is identified with the
  span of its grouped modes, with the geometric multiplicities computed as
  `finrank`.

  ## What is proved

    * `adjL`                     — the adjacency operator as `Module.End ℂ VertexSpace`
                                   (defeq to `adjacency`; `adjL_apply`).
    * `adjL_eigenmode`           — `adjL (eigenmode k) = adjEigenvalue k • eigenmode k`.
    * `repr_eq_zero_of_ne`       — if `adjL v = μ•v` and `adjEigenvalue i ≠ μ` then
                                   the `i`-th `eigenBasis`-coordinate of `v` vanishes
                                   (the core diagonalization fact).
    * `eigenspace_eq_span_group` — **`eigenspace adjL μ = span ℂ (eigenmode '' {k | adjEigenvalue k = μ})`
                                   for every `μ`** (both containments).
    * `eigenspace_two_eq`        — `eigenspace adjL 2      = span ℂ {eigenmode 0}`.
    * `eigenspace_golden_eq`     — `eigenspace adjL (φ−1)  = span ℂ {eigenmode 1, eigenmode 4}`.
    * `eigenspace_neg_golden_eq` — `eigenspace adjL (−φ)   = span ℂ {eigenmode 2, eigenmode 3}`.
    * `finrank_eigenspace_two`        — `finrank (eigenspace adjL 2)     = 1`.
    * `finrank_eigenspace_golden`     — `finrank (eigenspace adjL (φ−1)) = 2`.
    * `finrank_eigenspace_neg_golden` — `finrank (eigenspace adjL (−φ))  = 2`.
    * `multiplicities_sum_eq_finrank` — `1 + 2 + 2 = finrank ℂ VertexSpace = 5`
                                   (the geometric multiplicities exhaust the space).
    * `hasEigenvector_eigenmode`, `hasEigenvalue_two/golden/neg_golden`
                                   — the modes are genuine `Module.End.HasEigenvector`s
                                   and `2, φ−1, −φ` are genuine `HasEigenvalue`s.
    * `eigenspaces_span_top`     — `eigenspace 2 ⊔ eigenspace (φ−1) ⊔ eigenspace (−φ) = ⊤`
                                   (the diagonalizability statement: the eigenspaces
                                   fill the whole space).

  ## What is NOT proved
    * `DirectSum.IsInternal` of the eigenspace family is not packaged as such.
      We prove the two facts it factors into — the eigenspaces span `⊤`
      (`eigenspaces_span_top`) and their dimensions sum to `finrank = 5`
      (`multiplicities_sum_eq_finrank`) — but do not invoke Mathlib's
      `iSupIndep` / `DirectSum.IsInternal` combinator.  (The one Mathlib lemma
      that would let one assemble it directly is
      `Submodule.iSupIndep.eq_top_of_finrank_eq`-style reasoning from
      `Module.End.eigenspaces_iSupIndep`; we deliberately stay elementary.)
    * No new axioms; no `sorry`/`admit`/`native_decide`.  Verified on AXLE
      at `lean-4.32.0`.
-/
import Mathlib
import Brockian.D5Representation
import Brockian.D5Isotypic
import Brockian.Spectral
import Brockian.PentagonIsotypic

open BigOperators
open DihedralGroup
open Module
open Brockian.D5Representation
open Brockian.D5Isotypic
open Brockian.PentagonIsotypic

namespace Brockian.PentagonMultiplicities

/-! ### The adjacency operator as a `Module.End` -/

/-- The pentagon adjacency operator `A = ρ + ρ⁻¹` packaged as a genuine
`ℂ`-linear endomorphism of `VertexSpace`.  Definitionally equal to `adjacency`
(see `adjL_apply`); this repackaging is what lets us talk about
`Module.End.eigenspace`. -/
noncomputable def adjL : Module.End ℂ VertexSpace :=
  (d5Pull (r (1 : Fin 5))).toLinearMap + (d5Pull (r (-1 : Fin 5))).toLinearMap

/-- `adjL` acts as the operational `adjacency`. -/
theorem adjL_apply (f : VertexSpace) : adjL f = adjacency f := rfl

/-- The Fourier modes are eigenvectors of `adjL` with eigenvalue `adjEigenvalue`. -/
theorem adjL_eigenmode (k : Fin 5) :
    adjL (eigenmode k) = adjEigenvalue k • eigenmode k := by
  rw [adjL_apply, adjacency_eigenmode]

/-- `eigenBasis` is (pointwise) the Fourier eigenmode family. -/
theorem eigenBasis_apply (i : Fin 5) : eigenBasis i = eigenmode i := by
  simp only [eigenBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### The core diagonalization fact -/

/-- **Off-eigenvalue coordinates vanish.**  If `v` lies in the `μ`-eigenspace of
`adjL` (`adjL v = μ • v`), then every `eigenBasis`-coordinate of `v` at a
frequency `i` whose eigenvalue is not `μ` is zero.  This is the engine behind the
eigenspace = grouped-span identification. -/
theorem repr_eq_zero_of_ne {v : VertexSpace} {μ : ℂ}
    (hv : adjL v = μ • v) {i : Fin 5} (hi : adjEigenvalue i ≠ μ) :
    eigenBasis.repr v i = 0 := by
  have hrepr : v = ∑ j : Fin 5, (eigenBasis.repr v j) • eigenmode j := by
    conv_lhs => rw [← eigenBasis.sum_repr v]
    exact Finset.sum_congr rfl (fun j _ => by rw [eigenBasis_apply])
  have key : ∑ j : Fin 5, ((eigenBasis.repr v j) * (adjEigenvalue j - μ)) • eigenmode j = 0 := by
    have e1 : adjL v
        = ∑ j : Fin 5, ((eigenBasis.repr v j) * adjEigenvalue j) • eigenmode j := by
      conv_lhs => rw [hrepr]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [map_smul, adjL_eigenmode, smul_smul])
    have e2 : μ • v
        = ∑ j : Fin 5, (μ * (eigenBasis.repr v j)) • eigenmode j := by
      conv_lhs => rw [hrepr]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [smul_smul])
    have e0 : (∑ j : Fin 5, ((eigenBasis.repr v j) * adjEigenvalue j) • eigenmode j)
        - (∑ j : Fin 5, (μ * (eigenBasis.repr v j)) • eigenmode j) = 0 := by
      rw [← e1, ← e2, hv, sub_self]
    rw [← Finset.sum_sub_distrib] at e0
    rw [← e0]
    exact Finset.sum_congr rfl (fun j _ => by rw [← sub_smul]; congr 1; ring)
  have hcoeff : eigenBasis.repr v i * (adjEigenvalue i - μ) = 0 :=
    (Fintype.linearIndependent_iff.mp eigenmode_linearIndependent)
      (fun j => eigenBasis.repr v j * (adjEigenvalue j - μ)) key i
  rcases mul_eq_zero.mp hcoeff with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hi

/-! ### Eigenspace = span of the grouped modes -/

/-- **The eigenspace is exactly the span of its grouped isotypic modes.**  For
every scalar `μ`, `ker(adjL − μ·id) = span ℂ {eigenmode k | adjEigenvalue k = μ}`.
The `⊆` direction is `repr_eq_zero_of_ne`; the `⊇` direction is
`adjL_eigenmode`. -/
theorem eigenspace_eq_span_group (μ : ℂ) :
    Module.End.eigenspace adjL μ
      = Submodule.span ℂ (eigenmode '' {j : Fin 5 | adjEigenvalue j = μ}) := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hrepr : v = ∑ j : Fin 5, (eigenBasis.repr v j) • eigenmode j := by
      conv_lhs => rw [← eigenBasis.sum_repr v]
      exact Finset.sum_congr rfl (fun j _ => by rw [eigenBasis_apply])
    rw [hrepr]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : adjEigenvalue j = μ
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨j, hj, rfl⟩
    · rw [repr_eq_zero_of_ne hv hj, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, adjL_eigenmode, hj]

/-! ### The three frequency groups (as index sets) -/

/-- Frequency `0` is the unique eigenvalue-`2` mode. -/
theorem eigenIndices_two :
    {j : Fin 5 | adjEigenvalue j = (2 : ℂ)} = {0} := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have hmem : j ∈ Finset.univ.filter (fun k : Fin 5 => adjEigenvalue k = (2 : ℂ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
    rw [two_eigenfrequency] at hmem
    exact Finset.mem_singleton.mp hmem
  · intro h; subst h; exact adjEigenvalue_zero

/-- Frequencies `{1, 4}` are exactly the golden (`φ−1`) modes. -/
theorem eigenIndices_golden :
    {j : Fin 5 | adjEigenvalue j = ((Real.goldenRatio - 1 : ℝ) : ℂ)} = {1, 4} := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hmem : j ∈ Finset.univ.filter
        (fun k : Fin 5 => adjEigenvalue k = ((Real.goldenRatio - 1 : ℝ) : ℂ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
    rw [golden_eigenfrequencies] at hmem
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Finset.mem_singleton.mp h1)
  · rintro (rfl | rfl)
    · exact adjEigenvalue_one
    · exact adjEigenvalue_four

/-- Frequencies `{2, 3}` are exactly the `−φ` modes. -/
theorem eigenIndices_neg_golden :
    {j : Fin 5 | adjEigenvalue j = ((-Real.goldenRatio : ℝ) : ℂ)} = {2, 3} := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hmem : j ∈ Finset.univ.filter
        (fun k : Fin 5 => adjEigenvalue k = ((-Real.goldenRatio : ℝ) : ℂ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
    rw [neg_golden_eigenfrequencies] at hmem
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Finset.mem_singleton.mp h1)
  · rintro (rfl | rfl)
    · exact adjEigenvalue_two
    · exact adjEigenvalue_three

/-! ### Explicit eigenspace = mode-span identifications -/

/-- `eigenspace adjL 2 = span ℂ {eigenmode 0}` (the constant / Perron mode). -/
theorem eigenspace_two_eq :
    Module.End.eigenspace adjL (2 : ℂ) = Submodule.span ℂ {eigenmode 0} := by
  rw [eigenspace_eq_span_group, eigenIndices_two, Set.image_singleton]

/-- `eigenspace adjL (φ−1) = span ℂ {eigenmode 1, eigenmode 4}`. -/
theorem eigenspace_golden_eq :
    Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)
      = Submodule.span ℂ {eigenmode 1, eigenmode 4} := by
  rw [eigenspace_eq_span_group, eigenIndices_golden, Set.image_pair]

/-- `eigenspace adjL (−φ) = span ℂ {eigenmode 2, eigenmode 3}`. -/
theorem eigenspace_neg_golden_eq :
    Module.End.eigenspace adjL ((-Real.goldenRatio : ℝ) : ℂ)
      = Submodule.span ℂ {eigenmode 2, eigenmode 3} := by
  rw [eigenspace_eq_span_group, eigenIndices_neg_golden, Set.image_pair]

/-! ### Geometric multiplicities as `finrank` -/

/-- `Set.range ![a, b] = {a, b}`. -/
theorem range_matrix_two {M : Type*} (a b : M) :
    Set.range (![a, b] : Fin 2 → M) = {a, b} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/-- **Geometric multiplicity 1 of the eigenvalue `2`.** -/
theorem finrank_eigenspace_two :
    finrank ℂ (Module.End.eigenspace adjL (2 : ℂ)) = 1 := by
  rw [eigenspace_two_eq]
  exact finrank_span_singleton (eigenmode_ne_zero 0)

/-- Generic geometric-multiplicity-2 computation for a two-frequency group. -/
theorem finrank_eigenspace_pair {μ : ℂ} {p q : Fin 5} (hpq : p ≠ q)
    (hidx : {j : Fin 5 | adjEigenvalue j = μ} = {p, q}) :
    finrank ℂ (Module.End.eigenspace adjL μ) = 2 := by
  rw [eigenspace_eq_span_group, hidx]
  have himg : eigenmode '' ({p, q} : Set (Fin 5))
      = Set.range (![eigenmode p, eigenmode q] : Fin 2 → VertexSpace) := by
    rw [Set.image_pair, range_matrix_two]
  rw [himg]
  have hli : LinearIndependent ℂ (![eigenmode p, eigenmode q] : Fin 2 → VertexSpace) := by
    have hcomp : (![eigenmode p, eigenmode q] : Fin 2 → VertexSpace)
        = eigenmode ∘ (![p, q] : Fin 2 → Fin 5) := by
      funext i; fin_cases i <;> simp
    rw [hcomp]
    refine eigenmode_linearIndependent.comp _ ?_
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  rw [finrank_span_eq_card hli, Fintype.card_fin]

/-- **Geometric multiplicity 2 of the golden eigenvalue `φ−1`.** -/
theorem finrank_eigenspace_golden :
    finrank ℂ (Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)) = 2 :=
  finrank_eigenspace_pair (by decide) eigenIndices_golden

/-- **Geometric multiplicity 2 of the eigenvalue `−φ`.** -/
theorem finrank_eigenspace_neg_golden :
    finrank ℂ (Module.End.eigenspace adjL ((-Real.goldenRatio : ℝ) : ℂ)) = 2 :=
  finrank_eigenspace_pair (by decide) eigenIndices_neg_golden

/-- The ambient space is 5-dimensional. -/
theorem finrank_vertexSpace : finrank ℂ VertexSpace = 5 :=
  Module.finrank_fin_fun (R := ℂ)

/-- **The geometric multiplicities sum to the dimension.**
`1 + 2 + 2 = finrank ℂ VertexSpace = 5`: the eigenspaces of `2, φ−1, −φ`
account for the entire 5-dimensional space. -/
theorem multiplicities_sum_eq_finrank :
    finrank ℂ (Module.End.eigenspace adjL (2 : ℂ))
      + finrank ℂ (Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ))
      + finrank ℂ (Module.End.eigenspace adjL ((-Real.goldenRatio : ℝ) : ℂ))
      = finrank ℂ VertexSpace := by
  rw [finrank_eigenspace_two, finrank_eigenspace_golden, finrank_eigenspace_neg_golden,
    finrank_vertexSpace]

/-! ### Genuine eigenvectors / eigenvalues and diagonalizability -/

/-- Each Fourier mode is a genuine `Module.End.HasEigenvector` of `adjL`. -/
theorem hasEigenvector_eigenmode (i : Fin 5) :
    Module.End.HasEigenvector adjL (adjEigenvalue i) (eigenmode i) := by
  rw [Module.End.hasEigenvector_iff]
  exact ⟨Module.End.mem_eigenspace_iff.mpr (adjL_eigenmode i), eigenmode_ne_zero i⟩

/-- `2` is a genuine eigenvalue of `adjL`. -/
theorem hasEigenvalue_two : Module.End.HasEigenvalue adjL (2 : ℂ) := by
  have h := hasEigenvector_eigenmode 0
  rw [adjEigenvalue_zero] at h
  exact Module.End.hasEigenvalue_of_hasEigenvector h

/-- `φ − 1` is a genuine eigenvalue of `adjL`. -/
theorem hasEigenvalue_golden :
    Module.End.HasEigenvalue adjL ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  have h := hasEigenvector_eigenmode 1
  rw [adjEigenvalue_one] at h
  exact Module.End.hasEigenvalue_of_hasEigenvector h

/-- `−φ` is a genuine eigenvalue of `adjL`. -/
theorem hasEigenvalue_neg_golden :
    Module.End.HasEigenvalue adjL ((-Real.goldenRatio : ℝ) : ℂ) := by
  have h := hasEigenvector_eigenmode 2
  rw [adjEigenvalue_two] at h
  exact Module.End.hasEigenvalue_of_hasEigenvector h

/-- **Diagonalizability.**  The three eigenspaces of `2, φ−1, −φ` span the whole
space `VertexSpace`.  Together with `multiplicities_sum_eq_finrank` (their
dimensions sum to `finrank = 5`) this exhibits `adjL` as diagonalizable with the
eigenbasis `eigenBasis`. -/
theorem eigenspaces_span_top :
    Module.End.eigenspace adjL (2 : ℂ)
      ⊔ Module.End.eigenspace adjL ((Real.goldenRatio - 1 : ℝ) : ℂ)
      ⊔ Module.End.eigenspace adjL ((-Real.goldenRatio : ℝ) : ℂ) = ⊤ := by
  rw [eigenspace_two_eq, eigenspace_golden_eq, eigenspace_neg_golden_eq,
    ← Submodule.span_union, ← Submodule.span_union]
  have hset : ({eigenmode 0} : Set VertexSpace) ∪ {eigenmode 1, eigenmode 4}
      ∪ {eigenmode 2, eigenmode 3} = Set.range eigenmode := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro ((rfl | rfl | rfl) | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hset]
  have hcoe : (⇑eigenBasis : Fin 5 → VertexSpace) = eigenmode := funext eigenBasis_apply
  rw [← hcoe]
  exact eigenBasis.span_eq

end Brockian.PentagonMultiplicities
