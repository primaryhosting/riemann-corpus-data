/-
  Brockian/GaloisCyclicGroup.lean — the Galois GROUP of the real cyclotomic field.

  `Brockian/GaloisGeneralDegree.lean` proved the DEGREE
  `[ℚ(2cos(2π/p)):ℚ] = (p−1)/2` for every odd prime `p`.  This file identifies
  the Galois GROUP of that maximal real subfield `ℚ(ζ_p)⁺ = ℚ(2cos(2π/p))` of the
  `p`-th cyclotomic field ℚ(ζ_p):

        `Gal(ℚ(2cos(2π/p)) / ℚ)` is **CYCLIC of order `(p−1)/2`**.

  ## Proof architecture (the classical quotient, made executable)

  With `ζ = exp(2πi/p)` (`Complex.isPrimitiveRoot_exp`) and `α = ζ + ζ⁻¹ = 2cos(2π/p)`,
  working inside the cyclotomic field `L = ℚ(ζ) ⊆ ℂ`:

    * `L/ℚ` is a cyclotomic extension
      (`IsPrimitiveRoot.adjoin_isCyclotomicExtension`, applied through
       `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`), hence
      Galois (`IsCyclotomicExtension.isGalois`).
    * `Gal(L/ℚ) ≃* (ℤ/p)ˣ`  (`IsCyclotomicExtension.autEquivPow`, using
      `Polynomial.cyclotomic.irreducible_rat`), and `(ℤ/p)ˣ` is CYCLIC for `p`
      prime (`ZMod.isCyclic_units_prime`).  So `Gal(L/ℚ)` is cyclic
      (`MulEquiv.isCyclic`).
    * Therefore `L/ℚ` is ABELIAN Galois (`IsAbelianGalois.of_isCyclic`), so EVERY
      intermediate field is Galois over ℚ — in particular the real subfield
      `K = ℚ(α) ⊆ L` (Mathlib instance `IsAbelianGalois K K'`).  This is the
      normality of the real subfield, obtained for free from abelianness.
    * `Gal(L/ℚ) ↠ Gal(K/ℚ)` is surjective (`AlgEquiv.restrictNormalHom_surjective`,
      both fields normal), so `Gal(K/ℚ)` is a homomorphic image of a cyclic group,
      hence CYCLIC (`isCyclic_of_surjective`).
    * Its ORDER is `[K:ℚ] = (p−1)/2` (`IsGalois.card_aut_eq_finrank`
      + `Brockian.GaloisGeneralDegree.real_subfield_degree`, transported through
       `minpoly.algebraMap_eq` for the field embedding `K ↪ ℂ`).

  ## What is proved (AXLE-verified at lean-4.32.0, axioms ⊆
     {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`)

    * `realSubfield p`               — the real cyclotomic subfield `ℚ(2cos(2π/p))`
                                        realized as an `IntermediateField ℚ ℚ(ζ_p)`.
    * `realSubfield_isGalois`        — for every prime `p ≠ 2`, `ℚ(2cos(2π/p))/ℚ`
                                        is a **Galois** (indeed abelian) extension.
    * `realSubfield_gal_isCyclic`    — for every prime `p ≠ 2`, its Galois group
                                        `Gal(ℚ(2cos(2π/p))/ℚ)` is **CYCLIC**.
    * `realSubfield_gal_card`        — for every prime `p ≠ 2`, that Galois group has
                                        **order `(p−1)/2`**.

  ## What is NOT proved

    * `p = 2` is excluded (there `2cos(π) = −2 ∈ ℚ`, degree 1, the degenerate
      boundary case), matching `GaloisGeneralDegree`.  This is the only omission;
      the odd-prime theorem is fully general.
-/
import Mathlib
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.GaloisCyclicGroup

open Polynomial
open scoped IntermediateField

/-! ### The cyclotomic field and its real subfield -/

/-- **`ζ_p = exp(2πi/p) ∈ ℂ`** — a primitive `p`-th root of unity. -/
noncomputable def zetaC (p : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))

/-- **`ζ_p` viewed inside the cyclotomic field `ℚ(ζ_p) ⊆ ℂ`.** -/
noncomputable def zetaSub (p : ℕ) : ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) :=
  ⟨zetaC p, IntermediateField.mem_adjoin_simple_self ℚ (zetaC p)⟩

/-- **`α_p = ζ_p + ζ_p⁻¹ = 2cos(2π/p)`**, the real spectral generator, viewed
inside the cyclotomic field `ℚ(ζ_p)`. -/
noncomputable def alphaSub (p : ℕ) : ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) :=
  zetaSub p + (zetaSub p)⁻¹

/-- **The real cyclotomic subfield `ℚ(2cos(2π/p)) = ℚ(ζ_p)⁺`**, realized as an
intermediate field of the cyclotomic field `ℚ(ζ_p)`. -/
noncomputable def realSubfield (p : ℕ) :
    IntermediateField ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) :=
  ℚ⟮alphaSub p⟯

/-! ### The primitive root and cyclotomic-extension structure -/

/-- `ζ_p` is a primitive `p`-th root of unity. -/
theorem primRoot {p : ℕ} (hp : p.Prime) : IsPrimitiveRoot (zetaC p) p :=
  Complex.isPrimitiveRoot_exp p hp.pos.ne'

/-- `ℚ(ζ_p)/ℚ` is a cyclotomic extension of `ℚ`. -/
theorem cycExt {p : ℕ} (hp : p.Prime) :
    IsCyclotomicExtension {p} ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hζ := primRoot hp
  have halg : IsAlgebraic ℚ (zetaC p) := ((hζ.isIntegral hp.pos).tower_top).isAlgebraic
  change IsCyclotomicExtension {p} ℚ (ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
  exact hζ.adjoin_isCyclotomicExtension ℚ

/-! ### The full structural fact -/

/-- **The Galois group of the real cyclotomic subfield is cyclic of order `(p−1)/2`.**
Packaged as a single structural fact: for every prime `p ≠ 2`, the extension
`ℚ(2cos(2π/p))/ℚ` is Galois, its automorphism group is cyclic, and that group has
order `(p−1)/2`. -/
theorem realSubfield_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsGalois ℚ ↥(realSubfield p) ∧
    IsCyclic (↥(realSubfield p) ≃ₐ[ℚ] ↥(realSubfield p)) ∧
    Nat.card (↥(realSubfield p) ≃ₐ[ℚ] ↥(realSubfield p)) = (p - 1) / 2 := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- The cyclotomic field `L = ℚ(ζ_p)` and its structure over ℚ.
  haveI hcyc : IsCyclotomicExtension {p} ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) := cycExt hp
  haveI hfinL : FiniteDimensional ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) :=
    IsCyclotomicExtension.finiteDimensional (S := {p}) (K := ℚ) _
  haveI hgalL : IsGalois ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) :=
    IsCyclotomicExtension.isGalois {p} ℚ _
  -- `Gal(L/ℚ) ≃* (ZMod p)ˣ`, which is cyclic for `p` prime.
  haveI hcycGalL : IsCyclic (↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)
      ≃ₐ[ℚ] ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)) :=
    (IsCyclotomicExtension.autEquivPow (↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ))
      (cyclotomic.irreducible_rat hp.pos)).isCyclic.mpr (ZMod.isCyclic_units_prime hp)
  -- Hence `L/ℚ` is abelian Galois, so every intermediate field is Galois over ℚ.
  haveI habL : IsAbelianGalois ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) :=
    IsAbelianGalois.of_isCyclic ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)
  haveI habK : IsAbelianGalois ℚ ↥(realSubfield p) :=
    IsAbelianGalois.tower_bot ℚ ↥(realSubfield p) ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)
  haveI hgalK : IsGalois ℚ ↥(realSubfield p) := inferInstance
  -- Integrality of the real generator, and its degree `(p−1)/2`.
  haveI : Algebra.IsIntegral ℚ ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ) := inferInstance
  have hα'int : IsIntegral ℚ (alphaSub p) := Algebra.IsIntegral.isIntegral (alphaSub p)
  haveI hfinK : FiniteDimensional ℚ ↥(realSubfield p) := by
    have := IntermediateField.adjoin.finiteDimensional hα'int
    exact this
  -- `α_p = ζ_p + ζ_p⁻¹ = 2cos(2π/p)` as a complex number.
  have hnorm : ‖zetaC p‖ = 1 := by
    have harg : (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))
              = ((2 * Real.pi / (p : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    unfold zetaC; rw [harg]; exact Complex.norm_exp_ofReal_mul_I _
  have hre : (zetaC p).re = Real.cos (2 * Real.pi / (p : ℝ)) := by
    have harg : (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))
              = ((2 * Real.pi / (p : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    unfold zetaC; rw [harg]; exact Complex.exp_ofReal_mul_I_re _
  have hconjζ : (starRingEnd ℂ) (zetaC p) = (zetaC p)⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hbeta : zetaC p + (zetaC p)⁻¹ = ((Brockian.GaloisWhyFive.spectralGen p : ℝ) : ℂ) := by
    rw [← hconjζ, Complex.add_conj, hre]
    simp only [Brockian.GaloisWhyFive.spectralGen]
  -- The image of `α_p` under the field embedding `L ↪ ℂ` is `ζ_p + ζ_p⁻¹`.
  have hcoe : (algebraMap (↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)) ℂ) (alphaSub p)
      = zetaC p + (zetaC p)⁻¹ := by
    simp only [alphaSub, map_add, map_inv₀]
    rfl
  -- Degree of the real generator is `(p−1)/2`.
  have hinj : Function.Injective (algebraMap (↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)) ℂ) :=
    (algebraMap (↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ)) ℂ).injective
  have hminα : (minpoly ℚ (alphaSub p)).natDegree = (p - 1) / 2 := by
    rw [← minpoly.algebraMap_eq hinj (alphaSub p), hcoe, hbeta,
      show ((Brockian.GaloisWhyFive.spectralGen p : ℝ) : ℂ)
          = algebraMap ℝ ℂ (Brockian.GaloisWhyFive.spectralGen p) from rfl,
      minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective ℝ ℂ)]
    exact Brockian.GaloisGeneralDegree.real_subfield_degree hp hp2
  -- Assemble.
  refine ⟨hgalK, ?_, ?_⟩
  · -- cyclicity: `Gal(K/ℚ)` is a surjective image of the cyclic `Gal(L/ℚ)`.
    have hsurj := AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := ↥(realSubfield p)) (E := ↥(ℚ⟮zetaC p⟯ : IntermediateField ℚ ℂ))
    exact isCyclic_of_surjective _ hsurj
  · -- order: `|Gal(K/ℚ)| = [K:ℚ] = (p−1)/2`.
    rw [IsGalois.card_aut_eq_finrank ℚ ↥(realSubfield p)]
    show Module.finrank ℚ ↥ℚ⟮alphaSub p⟯ = (p - 1) / 2
    rw [IntermediateField.adjoin.finrank hα'int]
    exact hminα

/-! ### The named theorems -/

/-- **The real cyclotomic subfield is Galois over ℚ.**  For every prime `p ≠ 2`,
`ℚ(2cos(2π/p))/ℚ` is a (finite, abelian) Galois extension — its normality comes
for free from the abelianness of the cyclotomic Galois group. -/
theorem realSubfield_isGalois {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsGalois ℚ ↥(realSubfield p) :=
  (realSubfield_facts hp hp2).1

/-- **The Galois group of the real cyclotomic subfield is cyclic.**  For every prime
`p ≠ 2`, `Gal(ℚ(2cos(2π/p))/ℚ)` is a cyclic group — being a homomorphic image of the
cyclic group `Gal(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)ˣ`. -/
theorem realSubfield_gal_isCyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsCyclic (↥(realSubfield p) ≃ₐ[ℚ] ↥(realSubfield p)) :=
  (realSubfield_facts hp hp2).2.1

/-- **The Galois group of the real cyclotomic subfield has order `(p−1)/2`.**  For every
prime `p ≠ 2`, `|Gal(ℚ(2cos(2π/p))/ℚ)| = (p−1)/2 = [ℚ(2cos(2π/p)):ℚ]`. -/
theorem realSubfield_gal_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (↥(realSubfield p) ≃ₐ[ℚ] ↥(realSubfield p)) = (p - 1) / 2 :=
  (realSubfield_facts hp hp2).2.2

end Brockian.GaloisCyclicGroup
