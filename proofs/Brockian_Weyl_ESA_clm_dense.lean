/-
  Brockian/WeylEssSelfAdjoint.lean — a CONCRETE inhabitant of the
  essential-self-adjointness predicate from `Brockian/WeylOperator.lean`.

  ## What this file grounds

  `Brockian.Weyl.Operator.EssentiallySelfAdjoint` (the Weyl-criterion predicate:
  both deficiency spaces `ker(T* ∓ i)` are trivial) was, in `WeylOperator.lean`,
  only *defined* — never inhabited. The `smulPMap` witness there was proved
  symmetric but NOT essentially self-adjoint, because that needed a handle on the
  adjoint of a full-domain operator that the Operator agent left OPEN.

  This file closes that blocker. It exhibits a genuine, non-vacuous inhabitant:
  **every bounded self-adjoint operator `A : H →L[ℂ] H`, viewed as a
  densely-defined `LinearPMap` with full domain `⊤`, is essentially self-adjoint.**

  ## Rung shipped:  FULL — `EssentiallySelfAdjoint` is actually inhabited.

    * `clm_isSymmetric`        — `A.toPMap ⊤` is symmetric (`IsSelfAdjoint A ⇒ ⟪Ax,y⟫ =
                                 ⟪x,Ay⟫`), instantiating the framework non-vacuously.
    * `vec_eq_zero_of_inner`   — the analytic core: if `conj z · ⟪v,v⟫ = ⟪v, A v⟫`
                                 for self-adjoint `A` and non-real `z`, then `v = 0`.
                                 (Real quadratic form ⇒ non-real `z` cannot occur.)
    * `clm_deficiency_eq_bot`  — `ker(A* − z) = ⊥` for `Im z ≠ 0`. Proved with the
                                 adjoint's fundamental property
                                 `LinearPMap.adjoint_isFormalAdjoint`
                                 (`⟪A* g, x⟫ = ⟪g, A x⟫`), evaluated at `x = g`.
    * `clm_essentiallySelfAdjoint`
                               — **`EssentiallySelfAdjoint (A.toPMap ⊤)`** for any
                                 bounded self-adjoint `A`. THE inhabitant.
    * `id_essentiallySelfAdjoint`
                               — the identity `1 : H →L[ℂ] H` (nonzero, nontrivial)
                                 is essentially self-adjoint. A concrete, closed
                                 witness that the predicate is not empty.

  ## How the OPEN blocker was actually closed

  The Operator agent's obstruction was: identify `(A.toPMap ⊤)*` explicitly. Two
  facts in Mathlib v4.32.0 dissolve it:
    * `LinearPMap.adjoint_isFormalAdjoint` : for a densely-defined `T`, the adjoint
      satisfies `⟪T* y, x⟫ = ⟪y, T x⟫` on the domains. We never need the adjoint's
      *value*, only this relation — evaluated at the eigenvector itself.
    * `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense` (not needed by
      the proof below, but it *does* give `(A.toPMap p)* = A*.toPMap ⊤` outright —
      so the "missing eval lemma" in fact exists).
  Either way the identification is available; this file uses the first, lighter one.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Brockian.WeylOperator

namespace Brockian.Weyl.ESA

open scoped InnerProductSpace ComplexConjugate
open Brockian.Weyl.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The full-domain PMap of a bounded self-adjoint operator -/

/-- The full domain of `A.toPMap ⊤` is `⊤`. -/
theorem clm_domain (A : H →L[ℂ] H) : (A.toPMap ⊤).domain = ⊤ :=
  LinearMap.toPMap_domain _ _

/-- `A.toPMap ⊤` is densely defined (its domain `⊤` is dense). -/
theorem clm_dense (A : H →L[ℂ] H) : Dense ((A.toPMap ⊤).domain : Set H) := by
  rw [clm_domain, Submodule.top_coe]; exact dense_univ

/-- **A bounded self-adjoint operator is symmetric as a full-domain `LinearPMap`.**
This instantiates `IsSymmetric` — and hence the whole `WeylOperator` framework —
on a genuine, everywhere-defined operator, so nothing here is vacuous. -/
theorem clm_isSymmetric (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    IsSymmetric (A.toPMap ⊤) := by
  intro x y
  simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe]
  rw [← A.adjoint_inner_right, hA.adjoint_eq]

/-! ### The analytic core -/

/-- **Real quadratic form ⇒ non-real spectral parameter is excluded.** If `A` is
bounded self-adjoint, `Im z ≠ 0`, and `v` satisfies the adjoint eigen-relation in
inner-product form `conj z · ⟪v, v⟫ = ⟪v, A v⟫`, then `v = 0`.

The mechanism: `⟪v, A v⟫` is *real* (self-adjointness), while `conj z · ⟪v, v⟫`
has imaginary part `-Im z · ‖v‖²`. Equating imaginary parts forces `‖v‖² = 0`. -/
theorem vec_eq_zero_of_inner (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (v : H)
    (h : (starRingEnd ℂ) z * ⟪v, v⟫_ℂ = ⟪v, A v⟫_ℂ) : v = 0 := by
  -- the right-hand quadratic form is real
  have hreal : (starRingEnd ℂ) ⟪v, A v⟫_ℂ = ⟪v, A v⟫_ℂ := by
    rw [inner_conj_symm, ← A.adjoint_inner_right, hA.adjoint_eq]
  have hrim : (⟪v, A v⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
  -- `s = ⟪v, v⟫` is real with real part `‖v‖²`
  set s : ℂ := ⟪v, v⟫_ℂ with hs
  have hsim : s.im = 0 := Complex.conj_eq_iff_im.mp (inner_conj_symm v v)
  have hsre : s.re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  -- take imaginary parts of the hypothesis
  have him := congrArg Complex.im h
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hsim, hrim] at him
  have key : z.im * s.re = 0 := by linear_combination -him
  have hsre0 : s.re = 0 := (mul_eq_zero.mp key).resolve_left hz
  have hn2 : ‖v‖ ^ 2 = 0 := by rw [← hsre]; exact hsre0
  have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hn

/-! ### Deficiency-space triviality and essential self-adjointness -/

/-- **The deficiency space is trivial for non-real `z`.** For a bounded
self-adjoint `A` and `Im z ≠ 0`, `ker((A.toPMap ⊤)* − z) = ⊥`.

Proof: any `g` in the deficiency space is an adjoint eigenvector, `A* g = z • g`.
The adjoint's fundamental property `⟪A* g, x⟫ = ⟪g, A x⟫` (valid on the dense
domain) evaluated at `x = g` yields `conj z · ⟪g, g⟫ = ⟪g, A g⟫`; the analytic
core then forces `g = 0`. -/
theorem clm_deficiency_eq_bot (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : deficiencySpace (A.toPMap ⊤) z = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [mem_deficiencySpace_iff] at hg
  -- `hg : (A.toPMap ⊤).adjoint g = z • ↑g`
  have hFA := LinearPMap.adjoint_isFormalAdjoint (clm_dense A)
  have hgmem : (g : H) ∈ (A.toPMap ⊤).domain := by rw [clm_domain]; exact Submodule.mem_top
  have hFAeq := hFA g ⟨(g : H), hgmem⟩
  rw [hg] at hFAeq
  simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe] at hFAeq
  rw [inner_smul_left] at hFAeq
  -- `hFAeq : conj z * ⟪↑g, ↑g⟫ = ⟪↑g, A ↑g⟫`
  exact Submodule.coe_eq_zero.mp (vec_eq_zero_of_inner A hA hz (g : H) hFAeq)

/-- **THE INHABITANT.** Every bounded self-adjoint operator `A : H →L[ℂ] H`,
viewed as a full-domain densely-defined `LinearPMap`, is essentially self-adjoint:
both deficiency spaces `ker(A* ∓ i)` vanish. This is a genuine, non-vacuous
witness of `Brockian.Weyl.Operator.EssentiallySelfAdjoint`. -/
theorem clm_essentiallySelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    EssentiallySelfAdjoint (A.toPMap ⊤) :=
  ⟨clm_deficiency_eq_bot A hA (by rw [Complex.I_im]; exact one_ne_zero),
   clm_deficiency_eq_bot A hA (by simp [Complex.neg_im, Complex.I_im])⟩

/-- **A concrete, closed witness.** The identity operator `1 : H →L[ℂ] H` — a
nonzero, nontrivial bounded self-adjoint operator — is essentially self-adjoint.
So `EssentiallySelfAdjoint` is inhabited by something that is not the degenerate
zero operator. -/
theorem id_essentiallySelfAdjoint :
    EssentiallySelfAdjoint ((1 : H →L[ℂ] H).toPMap ⊤) :=
  clm_essentiallySelfAdjoint 1 (IsSelfAdjoint.one (H →L[ℂ] H))

end Brockian.Weyl.ESA
