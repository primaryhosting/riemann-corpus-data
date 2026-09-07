/-
  Brockian/PentagonIsotypic.lean

  Full operator-level C₅ isotypic spectral decomposition of the pentagon
  adjacency operator, and its identification of the golden eigenvalue.

  This file BUILDS ON `Brockian.D5Isotypic`, which defines the rotation
  pullback `d5Pull (r k)`, the primitive 5-th root `ω`, the Fourier modes
  `eigenmode j`, the geometric-sum lemma `sum_omegaPow`, character
  orthogonality, and the cyclic isotypic projector `isotypicProjector`.
  `D5Isotypic` proved the projector algebra *only on the Fourier basis*
  (`isotypicProjector_eigenmode`, `..._idempotent_eigenmode`, …).  Here we
  lift everything to arbitrary functions and add the adjacency operator, the
  multiplicity/eigenbasis structure, and the golden identification.

  ## What is proved

  (#9  definitions)
    * `adjacency`            — the C₅ adjacency operator `A = ρ + ρ⁻¹`,
                               `A f x = f (x-1) + f (x+1)`.
    * `adjEigenvalue k`      — the scalar `ω^k + ω^{-k}` (= `2cos(2πk/5)`).
    * `rot_isotypic`         — every rotation `ρ^a` acts on `Im Pₖ` as the
                               scalar `ω^{-ka}` (the key single-reindex lemma).

  (#10 projector algebra, for ALL f)
    * `isotypicProjector_comp`         — `Pⱼ ∘ Pₗ = δⱼₗ · Pₗ`.
    * `isotypicProjector_idempotent`   — `Pₖ ∘ Pₖ = Pₖ`.
    * `isotypicProjector_orthogonal`   — `j ≠ l → Pⱼ ∘ Pₗ = 0`.
    * `isotypicProjector_completeness` — `∑ₖ Pₖ = id`.

  (#11 adjacency diagonalization)
    * `adjacency_isotypicProjector` — `A ∘ Pₖ = (2cos(2πk/5)) · Pₖ` (for all f).
    * `adjEigenvalue_eq_two_cos`    — `ω^k + ω^{-k} = 2cos(2πk/5)`.
    * `adjEigenvalue_zero/one/two`  — the eigenvalues `2`, `φ−1`, `−φ`.
    * `golden_eigenvector`          — `A (eigenmode 1) = (φ−1) · eigenmode 1`,
                                      the structural home of the golden value.

  (#12 multiplicities / eigenbasis)
    * `adjacency_eigenmode`     — each mode is a genuine eigenvector.
    * `adjEigenvalue_neg`, `adjEigenvalue_three/four` — the frequency grouping
                                  `{0} , {1,4} , {2,3}`.
    * `eigenvalues_distinct`    — `2`, `φ−1`, `−φ` are pairwise distinct.
    * `eigenmode_linearIndependent`, `eigenBasis` — the five modes are a basis
                                  of `Fin 5 → ℂ` (diagonalizing eigenbasis).
    * `golden_eigenfrequencies` — `{k | A-eigenvalue k = φ−1} = {1,4}`
                                  and its `neg`/`two` companions, hence the
                                  multiplicities `1, 2, 2`.

  ## What is NOT proved
    * No `Module.End.eigenspace`/`finrank`-level statement of "geometric
      multiplicity 2".  We prove the strictly stronger *operational* content
      (a genuine basis of eigenvectors + the exact frequency partition +
      pairwise-distinct eigenvalues, so `1+2+2 = 5`), but do not package it
      through Mathlib's abstract eigenspace API.  The remaining formal step is
      to identify `LinearMap.ker (A - μ•id)` with the span of the grouped
      modes via `eigenBasis`.
    * No new axioms; no `sorry`/`admit`/`native_decide`.  Verified on AXLE
      at `lean-4.32.0`.
-/
import Mathlib
import Brockian.D5Representation
import Brockian.D5Isotypic
import Brockian.Spectral
import Brockian.CycleSpectrumFamily

open BigOperators
open DihedralGroup
open Module
open Brockian.D5Representation
open Brockian.D5Isotypic

namespace Brockian.PentagonIsotypic

/-! ### #9  The adjacency operator and its scalar eigenvalues -/

/-- The C₅ adjacency operator `A = ρ + ρ⁻¹` on vertex functions, where
`ρ = d5Pull (r 1)` and `ρ⁻¹ = d5Pull (r (-1))`. -/
noncomputable def adjacency (f : VertexSpace) : VertexSpace :=
  d5Pull (r (1 : Fin 5)) f + d5Pull (r (-1 : Fin 5)) f

theorem adjacency_apply (f : VertexSpace) (x : Fin 5) :
    adjacency f x = f (x - 1) + f (x + 1) := by
  simp only [adjacency, Pi.add_apply, d5Pull_r_apply]
  have hx : (x - -1 : Fin 5) = x + 1 := by rw [sub_neg_eq_add]
  rw [hx]

/-- The adjacency eigenvalue attached to frequency `k`: `ω^k + ω^{-k}`. -/
noncomputable def adjEigenvalue (k : Fin 5) : ℂ := omegaPow k + omegaPow (-k)

/-- **Key lemma (single reindex).**  Every rotation `ρ^a` acts on the image of
the isotypic projector `Pₖ` as multiplication by the character `ω^{-ka}`:
`ρ^a ∘ Pₖ = ω^{-ka} • Pₖ`.  This is the workhorse: idempotence, orthogonality
and the adjacency diagonalization all follow by summing it. -/
theorem rot_isotypic (a k : Fin 5) (f : VertexSpace) :
    d5Pull (r a) (isotypicProjector k f)
      = omegaPow (-(k * a)) • isotypicProjector k f := by
  funext x
  rw [d5Pull_r_apply, Pi.smul_apply, smul_eq_mul, isotypicProjector_apply,
    isotypicProjector_apply]
  have hsum :
      ∑ m : Fin 5, omegaPow (k * m) * f (x - a - m)
        = ∑ m : Fin 5, omegaPow (-(k * a)) * (omegaPow (k * m) * f (x - m)) := by
    refine Fintype.sum_equiv (Equiv.addLeft a) _ _ ?_
    intro m
    simp only [Equiv.coe_addLeft]
    rw [← mul_assoc, ← omegaPow_add]
    have he : (k * m : Fin 5) = -(k * a) + k * (a + m) := by
      rw [mul_add, neg_add_cancel_left]
    have hf : (x - a - m : Fin 5) = x - (a + m) := by rw [sub_sub]
    rw [he, hf]
  rw [hsum, ← Finset.mul_sum]
  ring

/-! ### #10  Projector algebra for arbitrary functions

`isotypicProjector` is `Pₖ f = (1/5) ∑ₘ ω^{km} ρ^m f`.  From `rot_isotypic`
the composition collapses to a geometric sum in the character. -/

/-- `Pₖ` is additive. -/
theorem isotypicProjector_add (k : Fin 5) (f g : VertexSpace) :
    isotypicProjector k (f + g)
      = isotypicProjector k f + isotypicProjector k g := by
  funext x
  simp only [Pi.add_apply, isotypicProjector_apply, mul_add, Finset.sum_add_distrib]

/-- **`Pⱼ ∘ Pₗ = δⱼₗ · Pₗ`.**  The full projector algebra (idempotence and
mutual orthogonality) in a single statement, valid for every `f`. -/
theorem isotypicProjector_comp (j l : Fin 5) (f : VertexSpace) :
    isotypicProjector j (isotypicProjector l f)
      = (if j = l then (1 : ℂ) else 0) • isotypicProjector l f := by
  have expand :
      isotypicProjector j (isotypicProjector l f)
        = (5 : ℂ)⁻¹ • ∑ k : Fin 5,
            omegaPow (j * k) • d5Pull (r k) (isotypicProjector l f) := rfl
  rw [expand]
  have hterm : ∀ k : Fin 5,
      omegaPow (j * k) • d5Pull (r k) (isotypicProjector l f)
        = omegaPow ((j - l) * k) • isotypicProjector l f := by
    intro k
    rw [rot_isotypic k l f, smul_smul, ← omegaPow_add]
    have he : (j * k + -(l * k) : Fin 5) = (j - l) * k := by
      rw [sub_mul, sub_eq_add_neg]
    rw [he]
  simp_rw [hterm]
  rw [← Finset.sum_smul, smul_smul, character_orthogonality]

/-- **Idempotence** `Pₖ ∘ Pₖ = Pₖ`, for all `f`. -/
theorem isotypicProjector_idempotent (k : Fin 5) (f : VertexSpace) :
    isotypicProjector k (isotypicProjector k f) = isotypicProjector k f := by
  rw [isotypicProjector_comp, if_pos rfl, one_smul]

/-- **Mutual orthogonality** `Pⱼ ∘ Pₗ = 0` for `j ≠ l`, for all `f`. -/
theorem isotypicProjector_orthogonal {j l : Fin 5} (h : j ≠ l) (f : VertexSpace) :
    isotypicProjector j (isotypicProjector l f) = 0 := by
  rw [isotypicProjector_comp, if_neg h, zero_smul]

/-- **Completeness** `∑ₖ Pₖ = id`, for all `f`. -/
theorem isotypicProjector_completeness (f : VertexSpace) :
    ∑ j : Fin 5, isotypicProjector j f = f := by
  funext x
  rw [Finset.sum_apply]
  simp_rw [isotypicProjector_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have inner : ∀ k : Fin 5,
      ∑ j : Fin 5, omegaPow (j * k) * f (x - k)
        = (if k = 0 then (5 : ℂ) else 0) * f (x - k) := by
    intro k
    rw [← Finset.sum_mul]
    congr 1
    rw [← sum_omegaPow k]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm])
  simp_rw [inner, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, sub_zero]
  rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (5 : ℂ) ≠ 0), one_mul]

/-! ### #11  Adjacency diagonalization -/

/-- **`A ∘ Pₖ = (ω^k + ω^{-k}) • Pₖ`**, for all `f`.  The adjacency operator is
diagonalized by the isotypic projectors: on the frequency-`k` sector it is the
scalar `2cos(2πk/5)` (see `adjEigenvalue_eq_two_cos`). -/
theorem adjacency_isotypicProjector (k : Fin 5) (f : VertexSpace) :
    adjacency (isotypicProjector k f)
      = adjEigenvalue k • isotypicProjector k f := by
  unfold adjacency adjEigenvalue
  rw [rot_isotypic (1 : Fin 5) k f, rot_isotypic (-1 : Fin 5) k f, ← add_smul]
  congr 1
  have h1 : (-(k * 1) : Fin 5) = -k := by rw [mul_one]
  have h2 : (-(k * (-1)) : Fin 5) = k := by rw [mul_neg_one, neg_neg]
  rw [h1, h2, add_comm]

/-- The mode `eigenmode k` is a genuine eigenvector of the adjacency operator. -/
theorem adjacency_eigenmode (k : Fin 5) :
    adjacency (eigenmode k) = adjEigenvalue k • eigenmode k := by
  unfold adjacency adjEigenvalue
  rw [d5Pull_r_eigenmode k (1 : Fin 5), d5Pull_r_eigenmode k (-1 : Fin 5), ← add_smul]
  congr 1
  have h1 : (-(k * 1) : Fin 5) = -k := by rw [mul_one]
  have h2 : (-(k * (-1)) : Fin 5) = k := by rw [mul_neg_one, neg_neg]
  rw [h1, h2, add_comm]

/-- **`ω^k + ω^{-k} = 2cos(2πk/5)`.**  Identifies the abstract character
eigenvalue with the real cosine spectrum of the cycle `C₅`. -/
theorem adjEigenvalue_eq_two_cos (k : Fin 5) :
    adjEigenvalue k
      = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 5) : ℝ) : ℂ) := by
  have hk : omegaPow k
      = Complex.exp ((↑(2 * Real.pi * (k.val : ℝ) / 5) : ℂ) * Complex.I) := by
    unfold omegaPow omega
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnk : omegaPow (-k)
      = Complex.exp (-((↑(2 * Real.pi * (k.val : ℝ) / 5) : ℂ) * Complex.I)) := by
    rw [omegaPow_neg, hk, ← Complex.exp_neg]
  show omegaPow k + omegaPow (-k) = _
  rw [hk, hnk, ← neg_mul, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

/-- The `k = 0` eigenvalue is `2`. -/
theorem adjEigenvalue_zero : adjEigenvalue 0 = 2 := by
  unfold adjEigenvalue
  simp only [neg_zero, omegaPow_zero]
  norm_num

/-- **The golden eigenvalue.**  The `k = 1` adjacency eigenvalue is `φ − 1`. -/
theorem adjEigenvalue_one :
    adjEigenvalue 1 = ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  rw [adjEigenvalue_eq_two_cos]
  congr 1
  have hv : (1 : Fin 5).val = 1 := by decide
  rw [hv, Nat.cast_one,
    show (2 * Real.pi * (1 : ℝ) / 5) = 2 * Real.pi / 5 from by ring]
  exact Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one

/-- The `k = 2` adjacency eigenvalue is `−φ`. -/
theorem adjEigenvalue_two :
    adjEigenvalue 2 = ((-Real.goldenRatio : ℝ) : ℂ) := by
  rw [adjEigenvalue_eq_two_cos]
  congr 1
  have hv : (2 : Fin 5).val = 2 := by decide
  rw [hv,
    show (2 * Real.pi * ((2 : ℕ) : ℝ) / 5) = 4 * Real.pi / 5 from by push_cast; ring]
  exact Brockian.Spectral.two_cos_four_pi_div_five

/-- **`A (eigenmode 1) = (φ − 1) • eigenmode 1`.**  The golden value is the
`k = 1` adjacency eigenvalue, with explicit eigenvector `x ↦ ω^x`.  This is the
structural explanation of the pentagon's golden spectrum. -/
theorem golden_eigenvector :
    adjacency (eigenmode 1) = ((Real.goldenRatio - 1 : ℝ) : ℂ) • eigenmode 1 := by
  rw [adjacency_eigenmode, adjEigenvalue_one]

/-! ### #12  Multiplicities and the diagonalizing eigenbasis -/

/-- The adjacency eigenvalue is even in the frequency: `λ_{-k} = λ_k`. -/
theorem adjEigenvalue_neg (k : Fin 5) : adjEigenvalue (-k) = adjEigenvalue k := by
  unfold adjEigenvalue
  rw [neg_neg, add_comm]

/-- Frequency `4 = -1` shares the golden eigenvalue with frequency `1`. -/
theorem adjEigenvalue_four :
    adjEigenvalue 4 = ((Real.goldenRatio - 1 : ℝ) : ℂ) := by
  have h : (4 : Fin 5) = -1 := by decide
  rw [h, adjEigenvalue_neg, adjEigenvalue_one]

/-- Frequency `3 = -2` shares the `−φ` eigenvalue with frequency `2`. -/
theorem adjEigenvalue_three :
    adjEigenvalue 3 = ((-Real.goldenRatio : ℝ) : ℂ) := by
  have h : (3 : Fin 5) = -2 := by decide
  rw [h, adjEigenvalue_neg, adjEigenvalue_two]

/-- The three distinct adjacency eigenvalues `2`, `φ−1`, `−φ` are pairwise
distinct (using `1 < φ < 2`). -/
theorem eigenvalues_distinct :
    (2 : ℂ) ≠ ((Real.goldenRatio - 1 : ℝ) : ℂ) ∧
    (2 : ℂ) ≠ ((-Real.goldenRatio : ℝ) : ℂ) ∧
    ((Real.goldenRatio - 1 : ℝ) : ℂ) ≠ ((-Real.goldenRatio : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    have h : (2 : ℝ) = Real.goldenRatio - 1 := by exact_mod_cast hc
    linarith [Real.goldenRatio_lt_two]
  · intro hc
    have h : (2 : ℝ) = -Real.goldenRatio := by exact_mod_cast hc
    linarith [Real.goldenRatio_pos]
  · intro hc
    have h : (Real.goldenRatio - 1 : ℝ) = -Real.goldenRatio := by exact_mod_cast hc
    linarith [Real.one_lt_goldenRatio]

/-- Each Fourier mode is nonzero (its value at vertex `0` is `1`). -/
theorem eigenmode_ne_zero (k : Fin 5) : eigenmode k ≠ 0 := by
  intro h
  have hval := congrFun h 0
  simp only [eigenmode_apply, mul_zero, omegaPow_zero, Pi.zero_apply] at hval
  exact one_ne_zero hval

/-- The isotypic projector `Pₖ` packaged as a `ℂ`-linear map. -/
noncomputable def isotypicProjectorL (k : Fin 5) : VertexSpace →ₗ[ℂ] VertexSpace where
  toFun := isotypicProjector k
  map_add' := isotypicProjector_add k
  map_smul' c f := isotypicProjector_smul k c f

/-- **The five Fourier modes are linearly independent.**  Proof: applying `Pₖ`
to a vanishing combination isolates the `k`-th coefficient, since
`Pₖ (eigenmode i) = δₖᵢ · eigenmode i` and each mode is nonzero. -/
theorem eigenmode_linearIndependent : LinearIndependent ℂ eigenmode := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hproj := congrArg (isotypicProjectorL k) hg
  rw [map_sum, map_zero] at hproj
  have hsimp : ∀ i : Fin 5,
      isotypicProjectorL k (g i • eigenmode i)
        = if k = i then g i • eigenmode i else 0 := by
    intro i
    rw [map_smul]
    have hL : (isotypicProjectorL k) (eigenmode i) = isotypicProjector k (eigenmode i) := rfl
    rw [hL, isotypicProjector_eigenmode]
    by_cases h : k = i <;> simp [h]
  simp_rw [hsimp] at hproj
  rw [Finset.sum_ite_eq] at hproj
  simp only [Finset.mem_univ, if_true] at hproj
  exact (smul_eq_zero.mp hproj).resolve_right (eigenmode_ne_zero k)

/-- **The diagonalizing eigenbasis.**  The five Fourier modes form a basis of
`Fin 5 → ℂ`; together with `adjacency_eigenmode` this exhibits `A` as
diagonal. -/
noncomputable def eigenBasis : Basis (Fin 5) ℂ VertexSpace :=
  basisOfLinearIndependentOfCardEqFinrank eigenmode_linearIndependent
    (by rw [Fintype.card_fin]; exact (Module.finrank_fin_fun (R := ℂ) (n := 5)).symm)

/-- **Golden multiplicity: exactly frequencies `{1,4}` carry eigenvalue `φ−1`.**
With `eigenBasis` and `adjacency_eigenmode`, this is the geometric multiplicity
`2` of the golden eigenvalue. -/
theorem golden_eigenfrequencies :
    (Finset.univ.filter
        (fun k : Fin 5 => adjEigenvalue k = ((Real.goldenRatio - 1 : ℝ) : ℂ)))
      = {1, 4} := by
  have d1 := eigenvalues_distinct.1
  have d3 := eigenvalues_distinct.2.2
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  fin_cases k
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h0 : adjEigenvalue 0 = ((Real.goldenRatio - 1 : ℝ) : ℂ) := h
      rw [adjEigenvalue_zero] at h0; exact absurd h0 d1
    · rcases h with h | h <;> exact absurd h (by decide)
  · exact ⟨fun _ => Or.inl (by decide), fun _ => adjEigenvalue_one⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 : adjEigenvalue 2 = ((Real.goldenRatio - 1 : ℝ) : ℂ) := h
      rw [adjEigenvalue_two] at h2; exact absurd h2 (Ne.symm d3)
    · rcases h with h | h <;> exact absurd h (by decide)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h3 : adjEigenvalue 3 = ((Real.goldenRatio - 1 : ℝ) : ℂ) := h
      rw [adjEigenvalue_three] at h3; exact absurd h3 (Ne.symm d3)
    · rcases h with h | h <;> exact absurd h (by decide)
  · exact ⟨fun _ => Or.inr (by decide), fun _ => adjEigenvalue_four⟩

/-- **`−φ` multiplicity: exactly frequencies `{2,3}`** (geometric multiplicity 2). -/
theorem neg_golden_eigenfrequencies :
    (Finset.univ.filter
        (fun k : Fin 5 => adjEigenvalue k = ((-Real.goldenRatio : ℝ) : ℂ)))
      = {2, 3} := by
  have d2 := eigenvalues_distinct.2.1
  have d3 := eigenvalues_distinct.2.2
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  fin_cases k
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h0 : adjEigenvalue 0 = ((-Real.goldenRatio : ℝ) : ℂ) := h
      rw [adjEigenvalue_zero] at h0; exact absurd h0 d2
    · rcases h with h | h <;> exact absurd h (by decide)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : adjEigenvalue 1 = ((-Real.goldenRatio : ℝ) : ℂ) := h
      rw [adjEigenvalue_one] at h1; exact absurd h1 d3
    · rcases h with h | h <;> exact absurd h (by decide)
  · exact ⟨fun _ => Or.inl (by decide), fun _ => adjEigenvalue_two⟩
  · exact ⟨fun _ => Or.inr (by decide), fun _ => adjEigenvalue_three⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h4 : adjEigenvalue 4 = ((-Real.goldenRatio : ℝ) : ℂ) := h
      rw [adjEigenvalue_four] at h4; exact absurd h4 d3
    · rcases h with h | h <;> exact absurd h (by decide)

/-- **Eigenvalue `2` multiplicity: exactly frequency `{0}`** (multiplicity 1). -/
theorem two_eigenfrequency :
    (Finset.univ.filter (fun k : Fin 5 => adjEigenvalue k = (2 : ℂ)))
      = {0} := by
  have d1 := eigenvalues_distinct.1
  have d2 := eigenvalues_distinct.2.1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  fin_cases k
  · exact ⟨fun _ => by decide, fun _ => adjEigenvalue_zero⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : adjEigenvalue 1 = (2 : ℂ) := h
      rw [adjEigenvalue_one] at h1; exact absurd h1 (Ne.symm d1)
    · exact absurd h (by decide)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 : adjEigenvalue 2 = (2 : ℂ) := h
      rw [adjEigenvalue_two] at h2; exact absurd h2 (Ne.symm d2)
    · exact absurd h (by decide)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h3 : adjEigenvalue 3 = (2 : ℂ) := h
      rw [adjEigenvalue_three] at h3; exact absurd h3 (Ne.symm d2)
    · exact absurd h (by decide)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · have h4 : adjEigenvalue 4 = (2 : ℂ) := h
      rw [adjEigenvalue_four] at h4; exact absurd h4 (Ne.symm d1)
    · exact absurd h (by decide)

/-- The multiplicities are `1, 2, 2` for eigenvalues `2, φ−1, −φ`. -/
theorem multiplicities :
    (Finset.univ.filter (fun k : Fin 5 => adjEigenvalue k = (2 : ℂ))).card = 1 ∧
    (Finset.univ.filter
      (fun k : Fin 5 => adjEigenvalue k = ((Real.goldenRatio - 1 : ℝ) : ℂ))).card = 2 ∧
    (Finset.univ.filter
      (fun k : Fin 5 => adjEigenvalue k = ((-Real.goldenRatio : ℝ) : ℂ))).card = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [two_eigenfrequency]; decide
  · rw [golden_eigenfrequencies]; decide
  · rw [neg_golden_eigenfrequencies]; decide

end Brockian.PentagonIsotypic
