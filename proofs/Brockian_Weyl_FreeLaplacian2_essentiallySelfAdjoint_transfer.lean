/-
  Brockian/WeylFreeLaplacian2.lean — the free-Laplacian essential-self-adjointness
  story done via the *reusable* unitary-transfer core, plus a genuine
  multiplication-operator model.

  This file complements Grok's `Brockian/WeylFreeLaplacian.lean` (bounded conjugation
  `conjCLM`). Where that file transferred bounded self-adjointness by hand, this file
  proves the transfer at the level the Weyl program actually needs: **essential
  self-adjointness — i.e. deficiency-space triviality — transfers across a unitary
  equivalence of (possibly unbounded) `LinearPMap`s**, via the Cayley criterion
  `Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff`. It then instantiates a real
  multiplication operator (`ξ ↦ ξ²` on discrete momentum space) as an essentially
  self-adjoint model, and packages the exact conditional under which `−d²/dx²` is
  essentially self-adjoint via the Fourier unitary.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

  ### 1. The reusable transfer core

    * `dense_map_iff`               — density of a submodule transfers across a unitary
                                      (`Dense (p.map U) ↔ Dense p`).
    * `rangeSMulSub_image`          — `ran(S − w) = U '' ran(T − w)` when `S` is `T`
                                      conjugated by the unitary `U` (relation form).
    * `essentiallySelfAdjoint_transfer`
                                    — **THE TRANSFER LEMMA.** If `T` has dense domain,
                                      `S.domain = U(dom T)`, and `S` acts as `U T U⁻¹`,
                                      then `EssentiallySelfAdjoint S ↔ EssentiallySelfAdjoint T`.
                                      Both deficiency spaces of `S` vanish iff both of
                                      `T` do. This is the reusable core the Fourier
                                      route rests on — proved through the honest von
                                      Neumann range-density criterion, no `sorry`.

  ### 2. Bounded conjugation witness (non-vacuity + free-model packaging)

    * `conjCLM_toPMap_essentiallySelfAdjoint_iff`
                                    — the transfer lemma applied to the bounded
                                      conjugation `conjCLM U A`: it is ESA iff `A.toPMap ⊤`
                                      is. Instantiates the abstract hypotheses concretely.
    * `conjCLM_essentiallySelfAdjoint`
                                    — the position-space conjugate of any bounded
                                      self-adjoint operator is essentially self-adjoint.

  ### 3. Genuine multiplication model (`ξ ↦ ξ²`, bounded/discrete)

    * `multCLM`                     — multiplication by a real function `g : Fin n → ℝ`
                                      on `EuclideanSpace ℂ (Fin n)` (a genuine
                                      multiplication operator on a discrete measure space).
    * `isSelfAdjoint_multCLM`       — it is self-adjoint (real diagonal ⇒ Hermitian).
    * `multCLM_essentiallySelfAdjoint`
                                    — hence essentially self-adjoint.
    * `sqMultCLM` / `sqMult_essentiallySelfAdjoint`
                                    — the **`ξ ↦ ξ²`** specialization: multiplication by
                                      `ξ²` (here `i ↦ i²` on the discrete momentum lattice)
                                      is essentially self-adjoint. The momentum-space side
                                      of the free Laplacian, made concrete.
    * `sqMult_conj_essentiallySelfAdjoint`
                                    — its position-space conjugate under any unitary is
                                      ESA: the free-Laplacian shape, unconditional in the
                                      bounded/discrete model.

  ### 4. The conditional free Laplacian `−d²/dx²`

    * `freeLaplacian_essentiallySelfAdjoint_of_fourier`
                                    — **the exact remaining Fourier fact, stated precisely.**
                                      Given a unitary `U : K ≃ₗᵢ[ℂ] H` (the inverse Fourier
                                      transform, momentum `K` → position `H`) and a
                                      momentum-space multiplication operator `M`
                                      (multiplication by `ξ²`) that is densely defined and
                                      essentially self-adjoint, any position-space operator
                                      `S` intertwined with `M` by `U` (i.e. `S = U M U⁻¹` —
                                      this is `−d²/dx² = ℱ⁻¹ · ξ² · ℱ`) is essentially
                                      self-adjoint. Immediate from the transfer lemma.

  ## What is NOT proved, and the precise blocker

  The genuine unbounded multiplication-by-`ξ²` operator on `L²(ℝ)` being essentially
  self-adjoint (the `hM` hypothesis of `freeLaplacian_essentiallySelfAdjoint_of_fourier`),
  and the Fourier transform `ℱ : L²(ℝ) ≃ₗᵢ L²(ℝ)` being the unitary intertwiner with the
  action identity `S = U M U⁻¹`, are the two facts left as hypotheses. Both are
  Mathlib-scale (unbounded multiplication ESA needs the maximal domain `{f : ξ²f ∈ L²}`
  and range density of `M ± i`; `fourierIntegral` as a Plancherel `L² ≃ₗᵢ L²`). The
  transfer core, the bounded/discrete `ξ²` model, and the conditional are all hole-free.

  Owner: Claude (swarm, queue #2 companion). Do not clobber without coordination.
  Verification (spec §2A): AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylCayley
import Brockian.WeylEssSelfAdjoint
import Brockian.WeylFreeLaplacian

namespace Brockian.Weyl.FreeLaplacian2

open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.Cayley Brockian.Weyl.ESA
open Brockian.Weyl.FreeLaplacian

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### 1. The reusable transfer core -/

/-- **Density transfers across a unitary.** For a submodule `p ⊆ H` and a unitary
`U : H ≃ₗᵢ K`, the image `p.map U` is dense in `K` iff `p` is dense in `H`. (A unitary
is a homeomorphism, and homeomorphisms are dense embeddings, preserving density both ways.) -/
theorem dense_map_iff (U : H ≃ₗᵢ[ℂ] K) (p : Submodule ℂ H) :
    Dense ((p.map U.toLinearMap : Set K)) ↔ Dense (p : Set H) := by
  rw [Submodule.map_coe]
  exact U.toHomeomorph.isDenseEmbedding.dense_image

/-- **The conjugated range is the image of the range.** If `S` is `T` conjugated by the
unitary `U` (`S.domain = U(dom T)` and `S` acts as `U ∘ T ∘ U⁻¹`), then the range of
`S − w` is exactly `U` applied to the range of `T − w`, for every `w : ℂ`. This is the
step that turns the Cayley density criterion into a transfer statement. -/
theorem rangeSMulSub_image (U : H ≃ₗᵢ[ℂ] K) {T : H →ₗ.[ℂ] H} {S : K →ₗ.[ℂ] K}
    (hdom : S.domain = T.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : T.domain), (y : K) = U (x : H) → S y = U (T x))
    (w : ℂ) :
    (rangeSMulSub S w : Set K) = U '' (rangeSMulSub T w : Set H) := by
  ext u
  constructor
  · intro hu
    rw [SetLike.mem_coe, mem_rangeSMulSub] at hu
    obtain ⟨y, hy⟩ := hu
    have hmem : (y : K) ∈ T.domain.map U.toLinearMap := hdom ▸ y.2
    rw [Submodule.mem_map] at hmem
    obtain ⟨x, hx, hUx⟩ := hmem
    have hUx' : U (x : H) = (y : K) := hUx
    have hact' : S y = U (T ⟨x, hx⟩) := hact y ⟨x, hx⟩ hUx'.symm
    refine ⟨T ⟨x, hx⟩ - w • (x : H), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_rangeSMulSub]; exact ⟨⟨x, hx⟩, rfl⟩
    · rw [map_sub, map_smul, ← hy, hact', hUx']
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_rangeSMulSub] at hv
    obtain ⟨x, hx⟩ := hv
    have hmemS : (U (x : H)) ∈ S.domain := by
      rw [hdom]; exact Submodule.mem_map_of_mem x.2
    have hact' : S ⟨U (x : H), hmemS⟩ = U (T x) := hact ⟨U (x : H), hmemS⟩ x rfl
    rw [SetLike.mem_coe, mem_rangeSMulSub]
    refine ⟨⟨U (x : H), hmemS⟩, ?_⟩
    rw [hact', ← hx, map_sub, map_smul]

/-- **THE TRANSFER LEMMA — essential self-adjointness transfers across a unitary
equivalence.** Let `U : H ≃ₗᵢ[ℂ] K` be a unitary, `T` a densely-defined operator on `H`,
and `S` an operator on `K` that is `T` conjugated by `U`: its domain is `U(dom T)` and it
acts as `U ∘ T ∘ U⁻¹`. Then `S` is essentially self-adjoint **iff** `T` is.

Both deficiency spaces `ker(S* ∓ i)` vanish exactly when both of `ker(T* ∓ i)` do. Proved
through the von Neumann range-density criterion: ESA ⟺ `ran(·±i)` dense, and the ranges of
`S` are the `U`-images of the ranges of `T`, so density is preserved by the unitary.

This is the reusable core of the Fourier route to `−Δ`: the free Laplacian in position
space is the unitary conjugate (by the Fourier transform) of multiplication by `ξ²` in
momentum space; this lemma carries essential self-adjointness across that conjugation. -/
theorem essentiallySelfAdjoint_transfer (U : H ≃ₗᵢ[ℂ] K) {T : H →ₗ.[ℂ] H}
    {S : K →ₗ.[ℂ] K} (hTdom : Dense (T.domain : Set H))
    (hdom : S.domain = T.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : T.domain), (y : K) = U (x : H) → S y = U (T x)) :
    EssentiallySelfAdjoint S ↔ EssentiallySelfAdjoint T := by
  have hSdom : Dense (S.domain : Set K) := by
    rw [hdom]; exact (dense_map_iff U T.domain).mpr hTdom
  rw [essentiallySelfAdjoint_iff hSdom, essentiallySelfAdjoint_iff hTdom]
  unfold rangeAddI rangeSubI
  have himg : ∀ w : ℂ,
      Dense (rangeSMulSub S w : Set K) ↔ Dense (rangeSMulSub T w : Set H) := by
    intro w
    rw [rangeSMulSub_image U hdom hact w]
    exact U.toHomeomorph.isDenseEmbedding.dense_image
  rw [himg (-Complex.I), himg Complex.I]

/-! ### 2. Bounded conjugation witness (non-vacuity + free-model packaging) -/

/-- The bounded conjugation `conjCLM U A` (Grok's `WeylFreeLaplacian`) is essentially
self-adjoint iff `A.toPMap ⊤` is — an instance of the abstract transfer lemma with
`T = A.toPMap ⊤`, `S = (conjCLM U A).toPMap ⊤`. Shows the transfer hypotheses are
concretely satisfiable. -/
theorem conjCLM_toPMap_essentiallySelfAdjoint_iff (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) :
    EssentiallySelfAdjoint ((conjCLM U A).toPMap ⊤) ↔
      EssentiallySelfAdjoint (A.toPMap ⊤) := by
  refine essentiallySelfAdjoint_transfer U (T := A.toPMap ⊤)
    (S := (conjCLM U A).toPMap ⊤) (clm_dense A) ?_ ?_
  · rw [clm_domain, clm_domain, Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr U.surjective).symm
  · intro y x hxy
    simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe, conjCLM_apply]
    rw [hxy, U.symm_apply_apply]

/-- **The position-space conjugate of a bounded self-adjoint operator is essentially
self-adjoint.** For any unitary `U` and bounded self-adjoint `A`, `conjCLM U A` (viewed as
a full-domain `LinearPMap`) is ESA. -/
theorem conjCLM_essentiallySelfAdjoint (U : H ≃ₗᵢ[ℂ] K) {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) :
    EssentiallySelfAdjoint ((conjCLM U A).toPMap ⊤) :=
  (conjCLM_toPMap_essentiallySelfAdjoint_iff U A).mpr (clm_essentiallySelfAdjoint A hA)

/-! ### 3. Genuine multiplication model (`ξ ↦ ξ²`, discrete/bounded) -/

section Mult

variable {n : ℕ}

/-- **Multiplication by a real function** `g : Fin n → ℝ` on `EuclideanSpace ℂ (Fin n)`.
This is a genuine multiplication operator on a (discrete, finite) measure space: it acts
diagonally, `f ↦ (i ↦ g i · f i)`, realized as the CLM of the real diagonal matrix. -/
noncomputable def multCLM (g : Fin n → ℝ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.diagonal (fun i => (g i : ℂ)))

/-- The diagonal matrix of a real function is Hermitian (self-adjoint). -/
theorem isSelfAdjoint_diagonal (g : Fin n → ℝ) :
    IsSelfAdjoint (Matrix.diagonal (fun i => (g i : ℂ))) := by
  show star (Matrix.diagonal (fun i => (g i : ℂ))) = Matrix.diagonal (fun i => (g i : ℂ))
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  exact Complex.conj_ofReal (g i)

/-- **Multiplication by a real function is self-adjoint.** (`Matrix.toEuclideanCLM` is a
`⋆`-algebra isomorphism, so it carries the Hermitian diagonal matrix to a self-adjoint
operator.) -/
theorem isSelfAdjoint_multCLM (g : Fin n → ℝ) : IsSelfAdjoint (multCLM g) := by
  show star (multCLM g) = multCLM g
  unfold multCLM
  rw [← map_star]
  exact congrArg _ (isSelfAdjoint_diagonal g)

/-- **A real multiplication operator is essentially self-adjoint.** -/
theorem multCLM_essentiallySelfAdjoint (g : Fin n → ℝ) :
    EssentiallySelfAdjoint ((multCLM g).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (isSelfAdjoint_multCLM g)

/-- **Multiplication by `ξ²`** on the discrete momentum lattice `Fin n`: `i ↦ i² · f i`.
The momentum-space kinetic-energy symbol of the free Laplacian, made concrete. -/
noncomputable def sqMultCLM (n : ℕ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  multCLM (fun i => ((i : ℝ)) ^ 2)

/-- **Multiplication by `ξ²` is essentially self-adjoint** (bounded/discrete model). -/
theorem sqMult_essentiallySelfAdjoint (n : ℕ) :
    EssentiallySelfAdjoint ((sqMultCLM n).toPMap ⊤) :=
  multCLM_essentiallySelfAdjoint _

/-- **Free-Laplacian shape, bounded/discrete model, unconditional.** The position-space
conjugate (under any unitary `U`) of momentum-space multiplication by `ξ²` is essentially
self-adjoint. This is `−Δ = U · ξ² · U⁻¹` with the genuine `ξ²` multiplication on the
momentum side — the entire construction hole-free, in the discrete model. -/
theorem sqMult_conj_essentiallySelfAdjoint (n : ℕ)
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] L) :
    EssentiallySelfAdjoint ((conjCLM U (sqMultCLM n)).toPMap ⊤) :=
  conjCLM_essentiallySelfAdjoint U (isSelfAdjoint_multCLM _)

end Mult

/-! ### 4. The conditional free Laplacian `−d²/dx²` -/

/-- **The free Laplacian `−d²/dx²` is essentially self-adjoint — conditional on the two
named Fourier facts.**

Take momentum space `K = L²(ℝ)` and position space `H = L²(ℝ)`. Suppose:

  * `U : K ≃ₗᵢ[ℂ] H` is the (inverse) Fourier transform as a unitary;
  * `M : K →ₗ.[ℂ] K` is multiplication by `ξ²`, densely defined (`hMdom`) and essentially
    self-adjoint (`hM`);
  * `S : H →ₗ.[ℂ] H` is the free Laplacian, intertwined with `M` by `U`: its domain is
    `U(dom M)` and it acts as `S = U M U⁻¹` (`hdom`, `hact`) — i.e. `−d²/dx² = ℱ⁻¹ ξ² ℱ`.

Then `S` (the free Laplacian) is essentially self-adjoint.

The two remaining Mathlib-scale facts are exactly the hypotheses `hM` (unbounded
multiplication by `ξ²` is ESA) and `hdom`/`hact` with `U` a Plancherel unitary (the Fourier
transform intertwines). The transfer machinery discharges everything else. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hMdom : Dense (M.domain : Set K)) (hM : EssentiallySelfAdjoint M)
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x)) :
    EssentiallySelfAdjoint S :=
  (essentiallySelfAdjoint_transfer U hMdom hdom hact).mpr hM

end Brockian.Weyl.FreeLaplacian2
