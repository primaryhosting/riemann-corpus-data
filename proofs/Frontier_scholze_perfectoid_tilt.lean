-- Note: Lean 4 requires `import` commands to precede every other command, including module
-- docstrings, so the required header comment appears immediately after the import below.
import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

universe u₁ u₂

/-!
## The setting

Following Scholze (*Perfectoid spaces*, Publ. IHÉS 116 (2012)), a **perfectoid field** is a
complete non-archimedean field `K` of residue characteristic `p` whose (rank one) valuation is
non-discrete and for which the Frobenius map on `O_K / p` is surjective.  Its **tilt** `K♭` is
the fraction field of the perfection of `O_K / p`; this is Mathlib's `Tilt K v O hv p`, with
`PreTilt O p = Ring.Perfection (ModP O p) p` the perfection of `O_K/p` itself.

The *tilting equivalence* asserts that `K ↦ K♭` is an equivalence between perfectoid fields over
`K` and perfectoid fields over `K♭` (in particular an isomorphism of absolute Galois groups).
Here we formalize the field-level statement of the construction and prove:

* the tilt is a field of characteristic `p` on which every element has a `p`-th root
  (i.e. `K♭` is a *perfect* field of characteristic `p`);
* the tilt carries a rank one valuation whose vanishing locus is exactly `0`;
* the multiplicative "sharp"/untilt map `O♭ →* O` lifting the zeroth coordinate exists;
* the **base case** of the tilting equivalence: if `K` already has characteristic `p`, then
  tilting does nothing, i.e. `K♭ ≃+* K`.
-/

/-- `IsPerfectoidField K v O hv p` records that the valued field `(K, v)` with ring of integers
`O` is a perfectoid field of residue characteristic `p`:

* `p` is prime;
* `K` is the fraction field of `O`;
* `p` lies in the maximal ideal of `O` (residue characteristic `p`);
* `O` is `p`-adically complete (the completeness hypothesis);
* the value group is non-discrete (dense in `(0,1)`);
* the Frobenius `x ↦ x ^ p` on `O/p` is surjective.
-/
structure IsPerfectoidField (K : Type u₁) [Field K] (v : Valuation K ℝ≥0)
    (O : Type u₂) [CommRing O] [Algebra O K] (hv : v.Integers O) (p : ℕ) : Prop where
  /-- The residue characteristic is a prime number. -/
  prime : p.Prime
  /-- `K` is the fraction field of its ring of integers. -/
  isFractionRing : IsFractionRing O K
  /-- `p` is not a unit in `O`, i.e. the residue characteristic is `p`. -/
  residue_char : ¬ IsUnit (p : O)
  /-- `O` is `p`-adically complete. -/
  complete : IsAdicComplete (Ideal.span {(p : O)}) O
  /-- The value group is non-discrete. -/
  nondiscrete : ∀ γ : ℝ≥0, 0 < γ → γ < 1 → ∃ x : K, γ < v x ∧ v x < 1
  /-- Frobenius is surjective on `O/p`. -/
  frobenius_surjective : ∀ x : ModP O p, ∃ y : ModP O p, y ^ p = x

section

variable {K : Type u₁} [Field K] {v : Valuation K ℝ≥0} {O : Type u₂} [CommRing O] [Algebra O K]
  {hv : v.Integers O} {p : ℕ} [Fact p.Prime] [Fact (v (p : K) ≠ 1)] [Fact (¬ IsUnit (p : O))]

/-- The tilt `K♭` of a valued field is a field of characteristic `p`. -/
theorem charP_tilt : CharP (Tilt K v O hv p) p := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain K v O hv p
  haveI : Field (FractionRing (PreTilt O p)) := FractionRing.field _
  exact charP_of_injective_algebraMap
    (IsFractionRing.injective (PreTilt O p) (FractionRing (PreTilt O p))) p

/-- In a field of fractions of a perfect domain of characteristic `p`, every element has a
`p`-th root. -/
theorem pow_surjective_fractionRing (A : Type u₂) [CommRing A] [IsDomain A] (q : ℕ)
    [ExpChar A q] [PerfectRing A q] :
    Function.Surjective (fun x : FractionRing A => x ^ q) := by
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  obtain ⟨a, ha⟩ : ∃ a : A, a ^ q = x := ⟨(frobeniusEquiv A q).symm x, by simp⟩
  obtain ⟨b, hb⟩ : ∃ b : A, b ^ q = (y : A) := ⟨(frobeniusEquiv A q).symm (y : A), by simp⟩
  have hy0 : (y : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
  have hb0 : b ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    rintro rfl
    exact hy0 (by rw [← hb, zero_pow (expChar_ne_zero A q)])
  have hy : y = (⟨b, hb0⟩ : nonZeroDivisors A) ^ q := Subtype.ext (by simpa using hb.symm)
  refine ⟨IsLocalization.mk' (FractionRing A) a ⟨b, hb0⟩, ?_⟩
  rw [hy, ← ha]
  exact (IsLocalization.mk'_pow a ⟨b, hb0⟩ q).symm

/-- The tilt `K♭` is a *perfect* field: every element has a `p`-th root. -/
theorem pow_surjective_tilt : Function.Surjective (fun x : Tilt K v O hv p => x ^ p) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain K v O hv p
  haveI : ExpChar (PreTilt O p) p := ExpChar.prime (Fact.out : p.Prime)
  exact pow_surjective_fractionRing (PreTilt O p) p

omit [Fact (v (p : K) ≠ 1)] in
include hv in
/-- The perfection `O♭ = Perfection (O/p)` of the ring of integers carries a rank one valuation
whose vanishing locus is exactly `{0}`; this is the valuation of the tilt. -/
theorem exists_valuation_preTilt :
    ∃ w : Valuation (PreTilt O p) ℝ≥0, ∀ f : PreTilt O p, w f = 0 ↔ f = 0 :=
  ⟨PreTilt.val K v O hv p, fun _ => PreTilt.map_eq_zero hv⟩

/-- The multiplicative "sharp" (untilt) map `O♭ →* O`, lifting the zeroth coordinate
`O♭ → O/p`.  It exists as soon as `O` is `p`-adically complete. -/
theorem exists_sharp (hc : IsAdicComplete (Ideal.span {(p : O)}) O) :
    ∃ sharp : PreTilt O p →* O,
      ∀ x : PreTilt O p,
        Ideal.Quotient.mk (Ideal.span {(p : O)}) (sharp x) = PreTilt.coeff 0 x := by
  haveI := hc
  exact ⟨PreTilt.untilt, fun x => PreTilt.mk_untilt_eq_coeff_zero x⟩

/-- **Base case of the tilting equivalence.**  If the perfectoid field `K` already has
characteristic `p`, then tilting does nothing: `K♭ ≃+* K`. -/
theorem tilt_ringEquiv_self_of_charP [CharP K p] (hfr : IsFractionRing O K)
    (hfrob : ∀ x : ModP O p, ∃ y : ModP O p, y ^ p = x) :
    Nonempty (Tilt K v O hv p ≃+* K) := by
  haveI := hfr
  have hOinj : Function.Injective (algebraMap O K) := hv.hom_inj
  haveI : CharP O p := (RingHom.charP_iff (algebraMap O K) hOinj p).mpr inferInstance
  haveI : IsReduced O := isReduced_of_injective (algebraMap O K) hOinj
  -- Since `p = 0` in `O`, we have `O/p = O`.
  have e2 : ModP O p ≃+* O := by
    refine (Ideal.quotEquivOfEq ?_).trans (RingEquiv.quotientBot O)
    rw [Ideal.span_singleton_eq_bot]
    exact CharP.cast_eq_zero O p
  haveI : IsReduced (ModP O p) := isReduced_of_injective (e2 : ModP O p →+* O) e2.injective
  haveI : ExpChar (ModP O p) p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing (ModP O p) p := by
    refine PerfectRing.ofSurjective _ p fun x => ?_
    obtain ⟨y, hy⟩ := hfrob x
    exact ⟨y, by rw [frobenius_def, hy]⟩
  -- Hence the perfection of `O/p` is `O` itself, ...
  have e1 : ModP O p ≃+* Ring.Perfection (ModP O p) p := (PerfectionMap.id p (ModP O p)).equiv
  have e0 : PreTilt O p ≃+* O := e1.symm.trans e2
  -- ... and passing to fraction fields gives `K♭ ≃+* K`.
  exact ⟨IsFractionRing.ringEquivOfRingEquiv
    (A := PreTilt O p) (K := FractionRing (PreTilt O p)) e0⟩

/-- **Scholze's tilting construction for perfectoid fields.**

Let `(K, v)` be a perfectoid field of residue characteristic `p` with ring of integers `O`, and
let `K♭ = Tilt K v O hv p` be its tilt, the fraction field of the perfection `O♭` of `O/p`.
Then:

1. `K♭` is a field of characteristic `p`;
2. `K♭` is perfect: every element of `K♭` is a `p`-th power;
3. `K♭` carries a rank one valuation whose vanishing locus is exactly `{0}`, so `K♭` is again a
   valued field;
4. there is a multiplicative "sharp" map `O♭ →* O` lifting the zeroth coordinate
   `O♭ → O/p` (the multiplicative half of the tilting equivalence at the level of rings of
   integers);
5. (base case of the tilting equivalence) if `K` itself has characteristic `p`, then tilting is
   the identity: `K♭ ≃+* K`.
-/
theorem scholze_perfectoid_tilt (hK : IsPerfectoidField K v O hv p) :
    CharP (Tilt K v O hv p) p ∧
    Function.Surjective (fun x : Tilt K v O hv p => x ^ p) ∧
    (∃ w : Valuation (PreTilt O p) ℝ≥0, ∀ f : PreTilt O p, w f = 0 ↔ f = 0) ∧
    (∃ sharp : PreTilt O p →* O,
      ∀ x : PreTilt O p,
        Ideal.Quotient.mk (Ideal.span {(p : O)}) (sharp x) = PreTilt.coeff 0 x) ∧
    (CharP K p → Nonempty (Tilt K v O hv p ≃+* K)) :=
  ⟨charP_tilt, pow_surjective_tilt, exists_valuation_preTilt (K := K) (v := v) (hv := hv),
    exists_sharp hK.complete,
    fun _ => tilt_ringEquiv_self_of_charP hK.isFractionRing hK.frobenius_surjective⟩

end

end Frontier

