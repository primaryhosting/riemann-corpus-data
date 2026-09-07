/-
  Brockian/CyclotomicGaloisGroup.lean — the Galois GROUP of the real cyclotomic
  subfield for GENERAL (composite) `n`.

  `Brockian/GaloisCyclicGroup.lean` identified the Galois group of the real
  cyclotomic subfield `ℚ(2cos 2π/p) = ℚ(ζ_p)⁺` for odd PRIMES `p`: it is CYCLIC of
  order `(p−1)/2`, because the cyclotomic Galois group `(ℤ/p)ˣ` is itself cyclic.

  `Brockian/CyclotomicRealDegree.lean` computed the DEGREE for ALL `n ≥ 3`:
  `[ℚ(2cos 2π/n):ℚ] = φ(n)/2`.

  This file identifies the Galois GROUP for ALL `n ≥ 3`.  For general `n` the
  cyclotomic Galois group `(ℤ/n)ˣ` is no longer cyclic, but it is always ABELIAN,
  and this passes to the real subfield:

        `Gal(ℚ(2cos 2π/n) / ℚ)` is **ABELIAN Galois of order `φ(n)/2`**,

  and it is a **quotient of the cyclotomic Galois group `(ℤ/n)ˣ`**.

  ## Proof architecture (the same classical tower as `GaloisCyclicGroup`, but with
     the cyclic step replaced by the always-available commutativity step)

  Reusing the definitions of `GaloisCyclicGroup` (`zetaC n = exp(2πi/n)`,
  `alphaSub n = ζ_n + ζ_n⁻¹`, `realSubfield n = ℚ(alphaSub n) ⊆ ℚ(ζ_n)`):

    * `L = ℚ(ζ_n)/ℚ` is a cyclotomic extension
      (`IsPrimitiveRoot.adjoin_isCyclotomicExtension`), hence Galois
      (`IsCyclotomicExtension.isGalois`), finite-dimensional.
    * `Gal(L/ℚ) ≃* (ℤ/n)ˣ`  (`IsCyclotomicExtension.autEquivPow`, using
      `cyclotomic.irreducible_rat`).  Since `(ℤ/n)ˣ` is commutative, transporting
      the commutativity through the equiv gives `IsMulCommutative Gal(L/ℚ)`, i.e.
      `L/ℚ` is **abelian** Galois (`IsAbelianGalois`).  (For `n` prime, `(ℤ/n)ˣ` is
      additionally cyclic — that extra fact is `GaloisCyclicGroup`'s; here we only
      use commutativity, which holds for every `n`.)
    * Every intermediate field of an abelian extension is Galois over the base
      (`IsAbelianGalois.tower_bot` / the intermediate-field instance), so the real
      subfield `K = ℚ(alphaSub n)` is abelian Galois over ℚ.
    * Its ORDER is `[K:ℚ] = φ(n)/2` (`IsGalois.card_aut_eq_finrank`
      + `CyclotomicRealDegree.spectral_degree_general`, transported through
      `minpoly.algebraMap_eq` for the embedding `K ↪ ℂ`).
    * `(ℤ/n)ˣ ≃* Gal(L/ℚ) ↠ Gal(K/ℚ)` (restriction to the normal subfield `K`,
      `AlgEquiv.restrictNormalHom_surjective`) exhibits `Gal(K/ℚ)` as a QUOTIENT of
      `(ℤ/n)ˣ`, i.e. `Gal(K/ℚ) ≃* (ℤ/n)ˣ ⧸ H` for `H = ker` of that surjection
      (`QuotientGroup.quotientKerEquivOfSurjective`).

  ## What is proved (to be AXLE-verified at lean-4.32.0, axioms ⊆
     {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`)

    * `realSubfield_facts_general`   — for every `n ≥ 3`: `ℚ(2cos 2π/n)/ℚ` is Galois,
                                       is ABELIAN Galois, and its Galois group has
                                       order `φ(n)/2`.
    * `realSubfield_isGalois`        — for every `n ≥ 3`, `ℚ(2cos 2π/n)/ℚ` is Galois.
    * `realSubfield_isAbelianGalois` — for every `n ≥ 3`, it is ABELIAN Galois.
    * `realSubfield_gal_card`        — for every `n ≥ 3`, its Galois group has order
                                       `φ(n)/2`.
    * `realSubfield_gal_units_presentation`
                                     — for every `n ≥ 3`, there is a SURJECTIVE group
                                       hom `(ℤ/n)ˣ →* Gal(ℚ(2cos 2π/n)/ℚ)`, and the
                                       Galois group is `≃* (ℤ/n)ˣ ⧸ (its kernel)`.
    * `realSubfield_gal_isQuotientOfUnits` / `realSubfield_gal_equivUnitsQuotient`
                                     — the two named halves of that presentation.
    * `realSubfield_gal_isCyclic_of_prime`
                                     — the prime case additionally gives CYCLIC (bridge
                                       to `GaloisCyclicGroup`), the extra fact that is
                                       special to primes.

  ## What is NOT proved

    * `n ∈ {0,1,2}` is excluded (`n ≥ 3` hypothesis): there `2cos(2π/n) ∈ ℚ`
      (degrees `2cos 0 = 2`, `2cos π = −2`), the degenerate boundary, not the
      maximal-real-subfield regime.  This is the only omission; the theorem is fully
      general for `n ≥ 3`.
    * The EXPLICIT identification of the quotient subgroup `H ⊆ (ℤ/n)ˣ` with the
      order-two subgroup `{±1}` (complex conjugation) is NOT proved.  We prove
      `Gal(K/ℚ) ≃* (ℤ/n)ˣ ⧸ H` with `H` given as the kernel of the restriction
      surjection; `H` is of order `2` (its order is `[L:ℚ]/[K:ℚ] = 2`), and
      classically `H = {±1}`.  Closing `H = {±1}` requires the missing input that
      complex conjugation is the automorphism of `ℚ(ζ_n)` sent to `−1` under
      `IsCyclotomicExtension.autEquivPow` (equivalently `IsPrimitiveRoot.autToPow`);
      Mathlib (v4.32.0) has no lemma computing `autToPow`/`autEquivPow` on complex
      conjugation, so this identification is left as the precise remaining gap.

  ## Precise remaining obstruction

    * For (Galois / abelian / order `φ(n)/2` / quotient-of-`(ℤ/n)ˣ`): none — all
      closed for every `n ≥ 3`.
    * For the explicit `≅ (ℤ/n)ˣ / {±1}`: the single missing named fact is a
      Mathlib computation
        `IsCyclotomicExtension.autEquivPow L h (complexConjugation) = (−1 : (ZMod n)ˣ)`
      (complex conjugation ↦ `−1`), from which `H = {±1}` and hence
        `Gal(ℚ(2cos 2π/n)/ℚ) ≃* (ℤ/n)ˣ ⧸ ⟨−1⟩`
      would follow.  Absent that lemma the quotient is given by its (order-two) kernel.
-/
import Mathlib
import Brockian.CyclotomicRealDegree
import Brockian.GaloisCyclicGroup
import Brockian.GaloisGeneralDegree

namespace Brockian.CyclotomicGaloisGroup

open Polynomial
open scoped IntermediateField
open Brockian.GaloisCyclicGroup (zetaC zetaSub alphaSub realSubfield)
open Brockian.GaloisWhyFive (spectralGen)

/-! ### The structural facts for general `n` -/

/-- **The real cyclotomic subfield is abelian Galois of order `φ(n)/2` (general `n`).**
Packaged as a single structural fact: for every `n ≥ 3` the extension
`ℚ(2cos 2π/n)/ℚ` is Galois, is ABELIAN Galois, and its automorphism group has order
`φ(n)/2`.  Generalizes `GaloisCyclicGroup.realSubfield_facts` (odd primes, cyclic) to
all `n`, keeping the always-available abelianness in place of prime-only cyclicity. -/
theorem realSubfield_facts_general {n : ℕ} (hn : 3 ≤ n) :
    IsGalois ℚ ↥(realSubfield n) ∧
    IsAbelianGalois ℚ ↥(realSubfield n) ∧
    Nat.card (↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)) = Nat.totient n / 2 := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  -- The primitive n-th root and the cyclotomic field L = ℚ(ζ_n).
  have hζ : IsPrimitiveRoot (zetaC n) n := Complex.isPrimitiveRoot_exp n hn0
  haveI hcyc : IsCyclotomicExtension {n} ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) := by
    have halg : IsAlgebraic ℚ (zetaC n) := ((hζ.isIntegral (by omega)).tower_top).isAlgebraic
    change IsCyclotomicExtension {n} ℚ (ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  haveI hfinL : FiniteDimensional ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) :=
    IsCyclotomicExtension.finiteDimensional (S := {n}) (K := ℚ) _
  haveI hgalL : IsGalois ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) :=
    IsCyclotomicExtension.isGalois {n} ℚ _
  -- `Gal(L/ℚ) ≃* (ZMod n)ˣ`, which is commutative; hence `L/ℚ` is abelian Galois.
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (by omega)
  let e := IsCyclotomicExtension.autEquivPow (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) hirr
  haveI hcomm : IsMulCommutative
      (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) ≃ₐ[ℚ] ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) :=
    IsMulCommutative.of_comm (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm]))
  haveI habL : IsAbelianGalois ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) := { }
  haveI habK : IsAbelianGalois ℚ ↥(realSubfield n) :=
    IsAbelianGalois.tower_bot ℚ ↥(realSubfield n) ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)
  haveI hgalK : IsGalois ℚ ↥(realSubfield n) := inferInstance
  -- Integrality of the real generator and finite-dimensionality of K.
  haveI : Algebra.IsIntegral ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) := inferInstance
  have hα'int : IsIntegral ℚ (alphaSub n) := Algebra.IsIntegral.isIntegral (alphaSub n)
  haveI hfinK : FiniteDimensional ℚ ↥(realSubfield n) :=
    IntermediateField.adjoin.finiteDimensional hα'int
  -- `α_n = ζ_n + ζ_n⁻¹ = 2cos(2π/n)` as a complex number.
  have hnorm : ‖zetaC n‖ = 1 := by
    have harg : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
              = ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    unfold zetaC; rw [harg]; exact Complex.norm_exp_ofReal_mul_I _
  have hre : (zetaC n).re = Real.cos (2 * Real.pi / (n : ℝ)) := by
    have harg : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
              = ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    unfold zetaC; rw [harg]; exact Complex.exp_ofReal_mul_I_re _
  have hconjζ : (starRingEnd ℂ) (zetaC n) = (zetaC n)⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hbeta : zetaC n + (zetaC n)⁻¹ = ((spectralGen n : ℝ) : ℂ) := by
    rw [← hconjζ, Complex.add_conj, hre]; simp only [spectralGen]
  have hcoe : (algebraMap (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) ℂ) (alphaSub n)
      = zetaC n + (zetaC n)⁻¹ := by
    simp only [alphaSub, map_add, map_inv₀]; rfl
  have hinj : Function.Injective (algebraMap (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) ℂ) :=
    (algebraMap (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) ℂ).injective
  -- Degree of the real generator is `φ(n)/2`.
  have hminα : (minpoly ℚ (alphaSub n)).natDegree = Nat.totient n / 2 := by
    rw [← minpoly.algebraMap_eq hinj (alphaSub n), hcoe, hbeta,
      show ((spectralGen n : ℝ) : ℂ) = algebraMap ℝ ℂ (spectralGen n) from rfl,
      minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective ℝ ℂ)]
    exact Brockian.CyclotomicRealDegree.spectral_degree_general hn
  -- Assemble.
  refine ⟨hgalK, habK, ?_⟩
  rw [IsGalois.card_aut_eq_finrank ℚ ↥(realSubfield n)]
  show Module.finrank ℚ ↥ℚ⟮alphaSub n⟯ = Nat.totient n / 2
  rw [IntermediateField.adjoin.finrank hα'int]
  exact hminα

/-! ### The named structural theorems -/

/-- **The real cyclotomic subfield is Galois over ℚ (general `n`).**  For every
`n ≥ 3`, `ℚ(2cos 2π/n)/ℚ` is a (finite, abelian) Galois extension. -/
theorem realSubfield_isGalois {n : ℕ} (hn : 3 ≤ n) :
    IsGalois ℚ ↥(realSubfield n) :=
  (realSubfield_facts_general hn).1

/-- **The real cyclotomic subfield is ABELIAN Galois (general `n`).**  For every
`n ≥ 3`, `Gal(ℚ(2cos 2π/n)/ℚ)` is commutative — it is a quotient of the abelian
cyclotomic Galois group `(ℤ/n)ˣ`.  Unlike the prime case (`GaloisCyclicGroup`), it is
not cyclic in general; abelianness is the sharp general statement. -/
theorem realSubfield_isAbelianGalois {n : ℕ} (hn : 3 ≤ n) :
    IsAbelianGalois ℚ ↥(realSubfield n) :=
  (realSubfield_facts_general hn).2.1

/-- **The Galois group of the real cyclotomic subfield has order `φ(n)/2` (general `n`).**
For every `n ≥ 3`, `|Gal(ℚ(2cos 2π/n)/ℚ)| = φ(n)/2 = [ℚ(2cos 2π/n):ℚ]`. -/
theorem realSubfield_gal_card {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)) = Nat.totient n / 2 :=
  (realSubfield_facts_general hn).2.2

/-! ### Presentation of the Galois group as a quotient of `(ℤ/n)ˣ` -/

/-- **`Gal(ℚ(2cos 2π/n)/ℚ)` is a quotient of the cyclotomic Galois group `(ℤ/n)ˣ`.**
For every `n ≥ 3` there is a SURJECTIVE group homomorphism
`(ℤ/n)ˣ →* Gal(ℚ(2cos 2π/n)/ℚ)`, and the Galois group is isomorphic to `(ℤ/n)ˣ`
modulo the kernel of that surjection (first isomorphism theorem).  This is the
quotient `(ℤ/n)ˣ / {±1}` classically; here the quotient subgroup is given as the
kernel (which has order `2`), the explicit identification with `{±1}` being the one
remaining gap (see the header). -/
theorem realSubfield_gal_units_presentation {n : ℕ} (hn : 3 ≤ n) :
    ∃ φ : (ZMod n)ˣ →* (↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)),
      Function.Surjective φ ∧
      Nonempty ((↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)) ≃* (ZMod n)ˣ ⧸ φ.ker) := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  have hζ : IsPrimitiveRoot (zetaC n) n := Complex.isPrimitiveRoot_exp n hn0
  haveI hcyc : IsCyclotomicExtension {n} ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) := by
    have halg : IsAlgebraic ℚ (zetaC n) := ((hζ.isIntegral (by omega)).tower_top).isAlgebraic
    change IsCyclotomicExtension {n} ℚ (ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  haveI hfinL : FiniteDimensional ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) :=
    IsCyclotomicExtension.finiteDimensional (S := {n}) (K := ℚ) _
  haveI hgalL : IsGalois ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) :=
    IsCyclotomicExtension.isGalois {n} ℚ _
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (by omega)
  let e := IsCyclotomicExtension.autEquivPow (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) hirr
  haveI hcomm : IsMulCommutative
      (↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) ≃ₐ[ℚ] ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) :=
    IsMulCommutative.of_comm (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm]))
  haveI habL : IsAbelianGalois ℚ ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ) := { }
  haveI habK : IsAbelianGalois ℚ ↥(realSubfield n) :=
    IsAbelianGalois.tower_bot ℚ ↥(realSubfield n) ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)
  haveI hgalK : IsGalois ℚ ↥(realSubfield n) := inferInstance
  -- The restriction surjection `Gal(L/ℚ) ↠ Gal(K/ℚ)`, precomposed with `(ℤ/n)ˣ ≃* Gal(L/ℚ)`.
  set φ : (ZMod n)ˣ →* (↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)) :=
    (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ)) (↥(realSubfield n))).comp
      e.symm.toMonoidHom with hφdef
  have hφ : Function.Surjective ⇑φ := by
    have hr := AlgEquiv.restrictNormalHom_surjective (F := ℚ)
      (K₁ := ↥(realSubfield n)) (E := ↥(ℚ⟮zetaC n⟯ : IntermediateField ℚ ℂ))
    rw [hφdef, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact hr.comp e.symm.surjective
  exact ⟨φ, hφ, ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm⟩⟩

/-- **The surjection half of the presentation.**  For every `n ≥ 3`, there is a
SURJECTIVE group homomorphism `(ℤ/n)ˣ →* Gal(ℚ(2cos 2π/n)/ℚ)` — the real subfield's
Galois group is a homomorphic image (quotient) of the cyclotomic Galois group. -/
theorem realSubfield_gal_isQuotientOfUnits {n : ℕ} (hn : 3 ≤ n) :
    ∃ φ : (ZMod n)ˣ →* (↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)), Function.Surjective φ :=
  let ⟨φ, hs, _⟩ := realSubfield_gal_units_presentation hn
  ⟨φ, hs⟩

/-- **The quotient-isomorphism half of the presentation.**  For every `n ≥ 3` there is a
subgroup `H ⊆ (ℤ/n)ˣ` with `Gal(ℚ(2cos 2π/n)/ℚ) ≃* (ℤ/n)ˣ ⧸ H`.  (Classically
`H = {±1}`; see the header for the remaining explicit-identification gap.) -/
theorem realSubfield_gal_equivUnitsQuotient {n : ℕ} (hn : 3 ≤ n) :
    ∃ H : Subgroup (ZMod n)ˣ,
      Nonempty ((↥(realSubfield n) ≃ₐ[ℚ] ↥(realSubfield n)) ≃* (ZMod n)ˣ ⧸ H) :=
  let ⟨φ, _, hq⟩ := realSubfield_gal_units_presentation hn
  ⟨φ.ker, hq⟩

/-! ### The prime case: the extra cyclicity -/

/-- **The prime case additionally gives a CYCLIC Galois group.**  For every prime
`p ≠ 2`, `Gal(ℚ(2cos 2π/p)/ℚ)` is not merely abelian but CYCLIC — the extra fact
special to primes (where `(ℤ/p)ˣ` is cyclic), recorded in `GaloisCyclicGroup`.  This
bridges the general abelian result above back to the sharper prime statement. -/
theorem realSubfield_gal_isCyclic_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsCyclic (↥(realSubfield p) ≃ₐ[ℚ] ↥(realSubfield p)) :=
  Brockian.GaloisCyclicGroup.realSubfield_gal_isCyclic hp hp2

end Brockian.CyclotomicGaloisGroup
