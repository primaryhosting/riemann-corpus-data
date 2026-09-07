/-
  Brockian/FreeLaplacianPlancherel.lean — discharging the *unitary* half of the
  free-Laplacian Fourier conditional using Mathlib's genuine L² Plancherel theorem.

  `Brockian/WeylFreeLaplacian2.lean` proves the free Laplacian `−d²/dx²` essentially
  self-adjoint (ESA) *conditional* on an abstract Fourier package: an abstract unitary
  `U : K ≃ₗᵢ[ℂ] H`, an ESA momentum-space multiplication operator `M` (multiplication by
  `ξ²`), and an intertwining identity `S = U M U⁻¹`. That file leaves the unitary `U`
  abstract.

  Mathlib 4.32 now contains the honest Plancherel theorem: the Fourier transform on `L²`
  is a *linear isometry equivalence* `MeasureTheory.Lp.fourierTransformₗᵢ`. This file uses
  it to remove `U` from the list of hypotheses: the momentum→position intertwiner is no
  longer an abstract unitary but the *actual Fourier transform of L²(ℝ)*. What remains
  conditional is exactly the two genuinely-missing analytic facts, isolated precisely.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `fourierL2`                    — the Fourier transform on `L²(ℝ; ℂ)` (with Lebesgue
                                      `volume`) as a concrete unitary
                                      `L2R ≃ₗᵢ[ℂ] L2R`, i.e. Plancherel's unitary
                                      `MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ`. This is a
                                      genuine `L² ≃ₗᵢ L²`, not an abstract stand-in.

    * `fourierL2_norm_map` / `fourierL2_inner_map`
                                    — Plancherel norm/inner-product preservation for
                                      `fourierL2`, pulled back from Mathlib. Records that
                                      `fourierL2` really is the isometric Fourier transform.

    * `essentiallySelfAdjoint_fourierConj`
                                    — **THE PLANCHEREL TRANSFER.** For any densely-defined
                                      ESA operator `M` on `L²(ℝ)` and any operator `S` that
                                      is `M` conjugated by the *actual Fourier transform*
                                      (`S.domain = ℱ(dom M)`, `S = ℱ M ℱ⁻¹`), `S` is ESA.
                                      This discharges the abstract unitary of
                                      `freeLaplacian_essentiallySelfAdjoint_of_fourier`
                                      against the concrete `fourierL2`. Fully proved via the
                                      transfer core of `WeylFreeLaplacian2`.

    * `freeLaplacian_essentiallySelfAdjoint_via_plancherel`
                                    — the free-Laplacian specialization: with `M`
                                      multiplication by `ξ²` on momentum-space `L²(ℝ)`
                                      (densely defined, ESA) and `S = ℱ M ℱ⁻¹` the free
                                      Laplacian, `S` is ESA. The Fourier unitary is now the
                                      concrete Plancherel `fourierL2`; only `hMdom`, `hM`,
                                      and the intertwining `hdom`/`hact` remain as inputs.

  ## What is NOT proved

  The free Laplacian is **not** made unconditionally ESA. Two analytic facts remain as
  hypotheses (they are Mathlib-scale and absent from Mathlib 4.32):

    1. `hM` — the *unbounded* multiplication operator `M_{ξ²}` on `L²(ℝ)` (domain
       `{f : ξ²·f ∈ L²}`) is essentially self-adjoint. Mathlib has bounded/CLM self-adjoint
       operators and the `LinearPMap` adjoint, but no unbounded multiplication-operator
       self-adjointness theory.
    2. `hdom`/`hact` — the operator identity `−d²/dx² = ℱ⁻¹ · (ξ²·) · ℱ` at the level of
       `L²` domains. Mathlib's `FourierTransformDeriv` gives the derivative↔multiplication
       intertwining only pointwise / on Schwartz / integrable functions; the free Laplacian
       is not even defined as a `LinearPMap` in Mathlib.

  ## Precise remaining obstruction

  To make `freeLaplacian_essentiallySelfAdjoint_via_plancherel` unconditional one needs, in
  Mathlib terms:

    (A) A theory of the unbounded multiplication operator `M_g` for a real measurable
        `g : ℝ → ℝ` on `L²(ℝ)`, with domain `{f | g·f ∈ L²}`, and a proof that
        `ran(M_g − w) = L²` for `Im w ≠ 0` (equivalently `M_g` is self-adjoint, hence ESA),
        specialized to `g = (· ^ 2)`. The mathematical proof is `f ↦ f/(g−w)` (well-defined
        as `|g−w| ≥ |Im w| > 0`, and `g/(g−w)` is a bounded multiplier), but this requires
        `Lp`/`AEEqFun` multiplication-by-bounded-function plumbing that Mathlib lacks.
    (B) The definition of `−d²/dx²` as a `LinearPMap` on `L²(ℝ)` (e.g. via the `H²` Sobolev
        domain) together with the L²-level identity `ℱ ∘ (−d²/dx²) = (ξ²·) ∘ ℱ` on that
        domain. Mathlib's Fourier–derivative lemmas are the pointwise ingredients; the
        operator-level packaging is missing.

  This file's contribution is (A0): the unitary/Plancherel half — "the Fourier transform is
  an `L²` unitary and it transfers essential self-adjointness" — is now discharged against
  the genuine Mathlib Plancherel isometry, not an abstract hypothesis.

  Owner: Claude (A3 discharge task). Untracked companion to `WeylFreeLaplacian2.lean`.
  Verification: AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylFreeLaplacian2

namespace Brockian.FreeLaplacianPlancherel

open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.Cayley
open Brockian.Weyl.FreeLaplacian2
open MeasureTheory

/-- `L²(ℝ; ℂ)` with the Lebesgue `volume` measure: the position/momentum Hilbert space. -/
noncomputable abbrev L2R : Type := Lp (α := ℝ) ℂ 2

/-- **The Fourier transform on `L²(ℝ; ℂ)` as a concrete unitary.** This is Plancherel's
theorem in operator form: `MeasureTheory.Lp.fourierTransformₗᵢ`, the Fourier transform
realized as a `LinearIsometryEquiv` of `L²` onto itself. Unlike the abstract unitary in
`freeLaplacian_essentiallySelfAdjoint_of_fourier`, this *is* the Fourier transform. -/
noncomputable def fourierL2 : L2R ≃ₗᵢ[ℂ] L2R :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-- Plancherel: `fourierL2` preserves the `L²` norm. -/
theorem fourierL2_norm_map (f : L2R) : ‖fourierL2 f‖ = ‖f‖ :=
  (fourierL2).norm_map f

/-- Plancherel: `fourierL2` preserves the `L²` inner product. -/
theorem fourierL2_inner_map (f g : L2R) :
    (inner ℂ (fourierL2 f) (fourierL2 g)) = inner ℂ f g :=
  (fourierL2).inner_map_map f g

/-- **The Plancherel transfer of essential self-adjointness.** Let `M` be a densely-defined
essentially self-adjoint operator on momentum-space `L²(ℝ)`, and let `S` be `M` conjugated
by the *actual Fourier transform* `fourierL2`: its domain is `ℱ(dom M)` and it acts as
`S = ℱ M ℱ⁻¹`. Then `S` is essentially self-adjoint.

This is `essentiallySelfAdjoint_transfer` / `freeLaplacian_essentiallySelfAdjoint_of_fourier`
with the abstract unitary replaced by the concrete Plancherel isometry `fourierL2`. The
unitary half of the Fourier conditional is thereby discharged: no abstract `U` is assumed. -/
theorem essentiallySelfAdjoint_fourierConj
    {M S : L2R →ₗ.[ℂ] L2R}
    (hMdom : Dense (M.domain : Set L2R))
    (hM : EssentiallySelfAdjoint M)
    (hdom : S.domain = M.domain.map (fourierL2).toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain),
      (y : L2R) = fourierL2 (x : L2R) → S y = fourierL2 (M x)) :
    EssentiallySelfAdjoint S :=
  freeLaplacian_essentiallySelfAdjoint_of_fourier fourierL2 hMdom hM hdom hact

/-- **The free Laplacian `−d²/dx²` is essentially self-adjoint — via the genuine Plancherel
unitary, conditional only on the two remaining analytic facts.**

Take momentum and position space to be `L²(ℝ; ℂ)`. Suppose:

  * `M : L2R →ₗ.[ℂ] L2R` is multiplication by `ξ²`, densely defined (`hMdom`) and
    essentially self-adjoint (`hM`);
  * `S : L2R →ₗ.[ℂ] L2R` is the free Laplacian, intertwined with `M` by the *actual Fourier
    transform* `fourierL2`: `S.domain = ℱ(dom M)` and `S = ℱ M ℱ⁻¹` (`hdom`, `hact`).

Then `S` (the free Laplacian) is essentially self-adjoint.

Compared with `freeLaplacian_essentiallySelfAdjoint_of_fourier`, the unitary `U` is no
longer a hypothesis: it is the concrete Mathlib Plancherel isometry `fourierL2`. The only
remaining inputs are `hM` (unbounded `ξ²`-multiplication is ESA) and `hdom`/`hact` (the
`−d²/dx² = ℱ⁻¹ ξ² ℱ` operator identity) — the two facts isolated in this file's header. -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel
    {M S : L2R →ₗ.[ℂ] L2R}
    (hMdom : Dense (M.domain : Set L2R))
    (hM : EssentiallySelfAdjoint M)
    (hdom : S.domain = M.domain.map (fourierL2).toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain),
      (y : L2R) = fourierL2 (x : L2R) → S y = fourierL2 (M x)) :
    EssentiallySelfAdjoint S :=
  essentiallySelfAdjoint_fourierConj hMdom hM hdom hact

end Brockian.FreeLaplacianPlancherel
