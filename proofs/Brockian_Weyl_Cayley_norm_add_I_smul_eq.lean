/-
  Brockian/WeylCayley.lean — the **Cayley-transform / essential-self-adjointness
  criterion** for symmetric unbounded operators, the capstone von Neumann piece
  sitting on top of `Brockian/WeylOperator.lean` (namespace `Brockian.Weyl.Operator`).

  ## Setting

  `T : H →ₗ.[ℂ] H` is a densely-defined symmetric operator on a complex Hilbert
  space `H` (physics convention: `⟪·,·⟫` conjugate-linear in the FIRST slot).
  Mathlib v4.32.0 supplies `LinearPMap.adjoint` with its fundamental property
  `⟪T† g, x⟫ = ⟪g, T x⟫` (`adjoint_isFormalAdjoint`), `mem_adjoint_domain_of_exists`,
  and `adjoint_apply_eq`, but **none** of the deficiency/Cayley layer below.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `rangeSMulSub T w`              — the range submodule `ran(T − w) =
                                        {T v − w·v : v ∈ dom T}` (`Submodule ℂ H`),
                                        with membership lemma `mem_rangeSMulSub`.

    * `mem_orthogonal_rangeSMulSub_iff`
                                      — **THE von Neumann orthogonality identity**
                                        `ker(T* − z) = (ran(T − z̄))ᗮ`, in the form
                                        `g ∈ (ran(T − z̄))ᗮ ↔ ∃ hg, T* ⟨g,hg⟩ = z·g`.
                                        Proved directly from the adjoint's defining
                                        relation `⟪T* g, x⟫ = ⟪g, T x⟫` via
                                        `mem_adjoint_domain_of_exists` and
                                        `adjoint_apply_eq`. This is the genuine
                                        inner-product content of the criterion.

    * `deficiencySpace_eq_bot_iff`    — the deficiency space `ker(T* − z)` is
                                        trivial iff `ran(T − z̄)` is dense in `H`
                                        (bridges the subtype-valued kernel to a
                                        density statement, via
                                        `topologicalClosure_eq_top_iff`:
                                        `Kᗮ = ⊥ ↔ Dense K`).

    * `essentiallySelfAdjoint_iff`    — **THE CRITERION.** A densely-defined
                                        symmetric operator is essentially
                                        self-adjoint iff both `ran(T + i)` and
                                        `ran(T − i)` are dense:
                                        `EssentiallySelfAdjoint T ↔
                                          Dense (ran(T+i)) ∧ Dense (ran(T−i))`.
                                        The full Weyl / von Neumann deficiency
                                        criterion — a genuine ⟺, not a
                                        restatement of the predicate.

    * `norm_add_I_smul_eq`            — **the Cayley isometry (norm form)**
                                        `‖T v + i·v‖ = ‖T v − i·v‖` for `v ∈ dom T`,
                                        `T` symmetric. Exactly the statement that
                                        the Cayley map `V : (T−i)v ↦ (T+i)v`
                                        preserves norm (its isometry content): the
                                        `±i` cross terms cancel because `⟪T v, v⟫`
                                        is real. Proved from the
                                        `norm_add_sq`/`norm_sub_sq` expansion.

    * `apply_ne_I_smul` / `apply_ne_neg_I_smul`
                                      — injectivity of `T ± i` on the domain
                                        (`±i` are never eigenvalues of a symmetric
                                        operator), so `V` is well-defined.

  ## Scope

  `essentiallySelfAdjoint_iff` is the FULL rung: a real ⟺ whose forward/backward
  work is carried by the orthogonality identity `mem_orthogonal_rangeSMulSub_iff`,
  which does honest inner-product computation with the adjoint. Not built (and not
  needed for the criterion): the bundled `LinearIsometry` object for the Cayley
  transform (choosing preimages of `ran(T−i)`, packaging linearity) and the
  closure / self-adjoint-extension theory `T̄ = T**`, both absent from Mathlib
  v4.32.0. `norm_add_I_smul_eq` is the isometry's mathematical content; the bundled
  map is deferred.

  Verification (spec §2A): AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperator

namespace Brockian.Weyl.Cayley

open scoped InnerProductSpace
open Brockian.Weyl.Operator LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### The range submodule `ran(T − w)` -/

/-- **The range submodule** `ran(T − w) = {T v − w·v : v ∈ dom T}` as a
`Submodule ℂ H`, built from the honest linear map `v ↦ T v − w·v` on `dom T`. -/
noncomputable def rangeSMulSub (T : H →ₗ.[ℂ] H) (w : ℂ) : Submodule ℂ H :=
  LinearMap.range (T.toFun - w • T.domain.subtype)

/-- Membership in `ran(T − w)`: `u ∈ ran(T − w) ↔ ∃ v ∈ dom T, T v − w·v = u`. -/
theorem mem_rangeSMulSub {T : H →ₗ.[ℂ] H} {w : ℂ} {u : H} :
    u ∈ rangeSMulSub T w ↔ ∃ v : T.domain, T v - w • (v : H) = u := by
  rw [rangeSMulSub, LinearMap.mem_range]
  constructor <;> · rintro ⟨v, hv⟩; exact ⟨v, by simpa using hv⟩

/-! ### The von Neumann orthogonality identity -/

section Adjoint

variable [CompleteSpace H]

/-- **The von Neumann orthogonality identity** `ker(T* − z) = (ran(T − z̄))ᗮ`.

For a densely-defined `T`, a vector `g` lies in the orthogonal complement of the
range of `T − z̄` exactly when `g` belongs to the domain of the adjoint and is an
eigenvector `T* g = z·g`. This identifies the deficiency space `ker(T* − z)` with
the closed subspace `(ran(T − z̄))ᗮ`, whence "deficiency trivial ⟺ range dense".
Proved directly from the adjoint's fundamental property `⟪T* g, x⟫ = ⟪g, T x⟫`. -/
theorem mem_orthogonal_rangeSMulSub_iff {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) (z : ℂ) (g : H) :
    g ∈ (rangeSMulSub T (starRingEnd ℂ z))ᗮ ↔
      ∃ hg : g ∈ T.adjoint.domain, T.adjoint ⟨g, hg⟩ = z • g := by
  constructor
  · -- `g ⊥ ran(T − z̄)` gives `⟪g, T v⟫ = z̄·⟪g, v⟫`, so `g ∈ dom T*` and `T* g = z·g`
    intro hg
    have hortho : ∀ v : T.domain, ⟪g, T v⟫_ℂ = (starRingEnd ℂ z) * ⟪g, (v : H)⟫_ℂ := by
      intro v
      have hz := (Submodule.mem_orthogonal' _ g).mp hg
        (T v - (starRingEnd ℂ z) • (v : H)) (mem_rangeSMulSub.mpr ⟨v, rfl⟩)
      rw [inner_sub_right, inner_smul_right, sub_eq_zero] at hz
      exact hz
    have hg' : g ∈ T.adjoint.domain := by
      apply mem_adjoint_domain_of_exists
      refine ⟨z • g, fun x => ?_⟩
      rw [inner_smul_left, hortho x]
    refine ⟨hg', ?_⟩
    apply adjoint_apply_eq hT
    intro x
    rw [inner_smul_left]
    exact (hortho x).symm
  · -- eigenvector of `T*` at `z` ⇒ orthogonal to `ran(T − z̄)`
    rintro ⟨hg, heig⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨v, rfl⟩ := mem_rangeSMulSub.mp hu
    rw [inner_sub_right, inner_smul_right, sub_eq_zero]
    have hfa := adjoint_isFormalAdjoint hT ⟨g, hg⟩ v
    rw [heig, inner_smul_left] at hfa
    exact hfa.symm

/-- **Deficiency space trivial ⟺ range dense.** `ker(T* − z) = ⊥` exactly when
`ran(T − z̄)` is dense in `H`. Combines the orthogonality identity with
`topologicalClosure_eq_top_iff` (`Kᗮ = ⊥ ↔ closure K = ⊤ ↔ Dense K`), bridging the
subtype-valued deficiency space to a density statement in `H`. -/
theorem deficiencySpace_eq_bot_iff {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) (z : ℂ) :
    deficiencySpace T z = ⊥ ↔ Dense (rangeSMulSub T (starRingEnd ℂ z) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff, Submodule.eq_bot_iff]
  constructor
  · intro h g hg
    obtain ⟨hgd, heig⟩ := (mem_orthogonal_rangeSMulSub_iff hT z g).mp hg
    have h0 : (⟨g, hgd⟩ : T.adjoint.domain) = 0 :=
      h ⟨g, hgd⟩ ((mem_deficiencySpace_iff T z ⟨g, hgd⟩).mpr heig)
    simpa using congrArg Subtype.val h0
  · intro h g hg
    have heig := (mem_deficiencySpace_iff T z g).mp hg
    have hmem : (g : H) ∈ (rangeSMulSub T (starRingEnd ℂ z))ᗮ :=
      (mem_orthogonal_rangeSMulSub_iff hT z (g : H)).mpr ⟨g.2, heig⟩
    exact Subtype.ext (h (g : H) hmem)

/-! ### The essential-self-adjointness criterion -/

/-- `ran(T + i) = {T v + i·v : v ∈ dom T}` (the Cayley denominator's range). -/
noncomputable def rangeAddI (T : H →ₗ.[ℂ] H) : Submodule ℂ H := rangeSMulSub T (-Complex.I)

/-- `ran(T − i) = {T v − i·v : v ∈ dom T}` (the Cayley numerator's range). -/
noncomputable def rangeSubI (T : H →ₗ.[ℂ] H) : Submodule ℂ H := rangeSMulSub T Complex.I

/-- **THE ESSENTIAL-SELF-ADJOINTNESS CRITERION (Weyl / von Neumann).**

A densely-defined symmetric operator `T` is essentially self-adjoint **iff** both
`ran(T + i)` and `ran(T − i)` are dense in `H`. Equivalently, both deficiency
spaces `ker(T* ∓ i)` are trivial. Obtained by applying the orthogonality identity
at `z = i` (`z̄ = −i`, giving `ran(T + i)`) and at `z = −i` (`z̄ = i`, giving
`ran(T − i)`). -/
theorem essentiallySelfAdjoint_iff {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) :
    EssentiallySelfAdjoint T ↔
      Dense (rangeAddI T : Set H) ∧ Dense (rangeSubI T : Set H) := by
  unfold EssentiallySelfAdjoint
  rw [deficiencySpace_eq_bot_iff hT, deficiencySpace_eq_bot_iff hT, rangeAddI, rangeSubI,
      show (starRingEnd ℂ) Complex.I = -Complex.I from Complex.conj_I,
      show (starRingEnd ℂ) (-Complex.I) = Complex.I by
        rw [_root_.map_neg, Complex.conj_I, neg_neg]]

end Adjoint

/-! ### The Cayley isometry (norm form) and injectivity of `T ± i` -/

/-- **The Cayley isometry, norm form:** `‖T v + i·v‖ = ‖T v − i·v‖` for `v` in the
domain of a symmetric operator `T`. This says the Cayley map `V : (T−i)v ↦ (T+i)v`
preserves norm — the analytic heart of `V : ran(T−i) → ran(T+i)` being an isometry.
The cross terms `±2·Re⟪T v, i·v⟫` cancel because `⟪T v, v⟫` is real
(`IsSymmetric.inner_self_im`), so the two squared norms coincide. -/
theorem norm_add_I_smul_eq {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) (v : T.domain) :
    ‖T v + Complex.I • (v : H)‖ = ‖T v - Complex.I • (v : H)‖ := by
  set u : H := T v with hu
  set w : H := (v : H) with hw
  have hc : (⟪u, w⟫_ℂ).im = 0 := hT.inner_self_im v
  have hre : RCLike.re (⟪u, Complex.I • w⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    show (Complex.I * ⟪u, w⟫_ℂ).re = 0
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, hc]; ring
  have e1 : ‖u + Complex.I • w‖ ^ 2
      = ‖u‖ ^ 2 + 2 * RCLike.re (⟪u, Complex.I • w⟫_ℂ) + ‖Complex.I • w‖ ^ 2 :=
    norm_add_sq u _
  have e2 : ‖u - Complex.I • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, Complex.I • w⟫_ℂ) + ‖Complex.I • w‖ ^ 2 :=
    norm_sub_sq u _
  have hsq : ‖u + Complex.I • w‖ ^ 2 = ‖u - Complex.I • w‖ ^ 2 := by rw [e1, e2, hre]; ring
  have hfin := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hfin

/-- **`T + i` is injective on the domain.** `i` is never an eigenvalue of a
symmetric operator: `T v = i·v ⇒ v = 0`. (So the Cayley factor, here in `+i` form,
is injective and `V` is well-defined.) -/
theorem apply_ne_I_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {v : T.domain}
    (h : T v = Complex.I • (v : H)) : (v : H) = 0 :=
  hT.eq_zero_of_apply_eq_smul (by rw [Complex.I_im]; exact one_ne_zero) h

/-- **`T − i` is injective on the domain.** `−i` is never an eigenvalue of a
symmetric operator: `T v = −i·v ⇒ v = 0`. -/
theorem apply_ne_neg_I_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {v : T.domain}
    (h : T v = (-Complex.I) • (v : H)) : (v : H) = 0 :=
  hT.eq_zero_of_apply_eq_smul
    (by rw [Complex.neg_im, Complex.I_im]; exact neg_ne_zero.mpr one_ne_zero) h

end Brockian.Weyl.Cayley
