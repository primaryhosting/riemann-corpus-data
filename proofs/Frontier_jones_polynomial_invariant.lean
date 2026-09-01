import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Frontier

variable {R : Type*} [CommRing R]

/-- The Kauffman bracket loop value `δ = -A² - A⁻²`. -/
def kauffmanDelta (A : Rˣ) : R := -(A : R) ^ 2 - ((A⁻¹ : Rˣ) : R) ^ 2

/-- The writhe normalisation unit `-A³`. -/
def writheUnit (A : Rˣ) : Rˣ := -A ^ 3

/-- The (Kauffman-normalised) Jones invariant of a diagram whose writhe is `w` and whose
Kauffman bracket is `b`, namely `(-A³)^(-w) · b`. -/
def jones (A : Rˣ) (w : ℤ) (b : R) : R := ((writheUnit A ^ (-w) : Rˣ) : R) * b

lemma jones_smul_writheUnit (A : Rˣ) (w : ℤ) (b : R) :
    jones A (w + 1) (((writheUnit A : Rˣ) : R) * b) = jones A w b := by
  unfold jones
  rw [← mul_assoc, ← Units.val_mul, ← zpow_add_one]
  congr 3
  omega

lemma jones_smul_writheUnit_inv (A : Rˣ) (w : ℤ) (b : R) :
    jones A (w - 1) ((((writheUnit A)⁻¹ : Rˣ) : R) * b) = jones A w b := by
  unfold jones
  rw [← mul_assoc, ← Units.val_mul, ← zpow_sub_one]
  congr 3
  omega

/-- **Reidemeister I (positive kink), bracket level.**  If `bloop` is the bracket of the
diagram with an extra free loop and `bkink` is the bracket of the kinked diagram, obtained
by the Kauffman skein relation from `bloop` and `b`, then `bkink = -A³ · b`. -/
lemma bracket_R1_pos (A : Rˣ) (b bloop bkink : R)
    (hloop : bloop = kauffmanDelta A * b)
    (hskein : bkink = (A : R) * bloop + ((A⁻¹ : Rˣ) : R) * b) :
    bkink = ((writheUnit A : Rˣ) : R) * b := by
  have hA : (A : R) * ((A⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul]; simp
  subst hloop; subst hskein
  simp only [kauffmanDelta, writheUnit, Units.val_neg, Units.val_pow_eq_pow_val]
  linear_combination (-(((A⁻¹ : Rˣ) : R)) * b) * hA

/-- **Reidemeister I (negative kink), bracket level.** -/
lemma bracket_R1_neg (A : Rˣ) (b bloop bkink : R)
    (hloop : bloop = kauffmanDelta A * b)
    (hskein : bkink = (A : R) * b + ((A⁻¹ : Rˣ) : R) * bloop) :
    bkink = (((writheUnit A)⁻¹ : Rˣ) : R) * b := by
  have hA : (A : R) * ((A⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul]; simp
  subst hloop; subst hskein
  simp only [kauffmanDelta, writheUnit]
  have hval : (((-A ^ 3 : Rˣ)⁻¹ : Rˣ) : R) = -(((A⁻¹ : Rˣ) : R)) ^ 3 := by
    rw [inv_neg, ← inv_pow]
    simp
  rw [hval]
  linear_combination (-((A : R) * b)) * hA

/-- **Reidemeister II, bracket level.**  Expanding the two crossings of an R2 configuration
via the Kauffman skein relation gives back the bracket of the simplified diagram. -/
lemma bracket_R2 (A : Rˣ) (bI bU bloopU b1 b2 bT : R)
    (hloop : bloopU = kauffmanDelta A * bU)
    (h1 : b1 = (A : R) * bU + ((A⁻¹ : Rˣ) : R) * bI)
    (h2 : b2 = (A : R) * bloopU + ((A⁻¹ : Rˣ) : R) * bU)
    (hT : bT = (A : R) * b1 + ((A⁻¹ : Rˣ) : R) * b2) :
    bT = bI := by
  have hA : (A : R) * ((A⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul]; simp
  subst hloop; subst h1; subst h2; subst hT
  simp only [kauffmanDelta]
  linear_combination (bI - (A : R) ^ 2 * bU - ((A⁻¹ : Rˣ) : R) ^ 2 * bU) * hA

/-- **Reidemeister III, bracket level.**  Expanding the distinguished crossing in each of the
two diagrams, the `0`-smoothings agree by planar isotopy while the `∞`-smoothings agree by
Reidemeister II invariance; hence the two brackets agree. -/
lemma bracket_R3 (A : Rˣ) (bL bL' b0 bInf bInf' : R)
    (hL : bL = (A : R) * b0 + ((A⁻¹ : Rˣ) : R) * bInf)
    (hL' : bL' = (A : R) * b0 + ((A⁻¹ : Rˣ) : R) * bInf')
    (hR2 : bInf = bInf') :
    bL = bL' := by
  rw [hL, hL', hR2]

/-- **The Jones polynomial is a link invariant.**

For any commutative coefficient ring `R` and any invertible variable `A ∈ Rˣ`, the
Kauffman-normalised bracket `jones A w b = (-A³)^(-w) · b` is unchanged by all three
Reidemeister moves:

* `R1⁺`: a positive kink multiplies the writhe by `+1` and the bracket by `-A³`;
* `R1⁻`: a negative kink changes the writhe by `-1` and the bracket by `-A⁻³`;
* `R2`: the writhe is unchanged and the bracket is unchanged;
* `R3`: the writhe is unchanged and the bracket is unchanged.

In each case the hypotheses are exactly the Kauffman skein relation
`⟨D⟩ = A⟨D₀⟩ + A⁻¹⟨D∞⟩` together with the loop relation `⟨D ⊔ ○⟩ = (-A² - A⁻²)⟨D⟩`
applied to the local configurations occurring in the move. -/
theorem jones_polynomial_invariant {R : Type*} [CommRing R] (A : Rˣ) :
    (∀ (w : ℤ) (b bloop bkink : R),
        bloop = kauffmanDelta A * b →
        bkink = (A : R) * bloop + ((A⁻¹ : Rˣ) : R) * b →
        jones A (w + 1) bkink = jones A w b) ∧
    (∀ (w : ℤ) (b bloop bkink : R),
        bloop = kauffmanDelta A * b →
        bkink = (A : R) * b + ((A⁻¹ : Rˣ) : R) * bloop →
        jones A (w - 1) bkink = jones A w b) ∧
    (∀ (w : ℤ) (bI bU bloopU b1 b2 bT : R),
        bloopU = kauffmanDelta A * bU →
        b1 = (A : R) * bU + ((A⁻¹ : Rˣ) : R) * bI →
        b2 = (A : R) * bloopU + ((A⁻¹ : Rˣ) : R) * bU →
        bT = (A : R) * b1 + ((A⁻¹ : Rˣ) : R) * b2 →
        jones A w bT = jones A w bI) ∧
    (∀ (w : ℤ) (bL bL' b0 bInf bInf' : R),
        bL = (A : R) * b0 + ((A⁻¹ : Rˣ) : R) * bInf →
        bL' = (A : R) * b0 + ((A⁻¹ : Rˣ) : R) * bInf' →
        bInf = bInf' →
        jones A w bL = jones A w bL') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w b bloop bkink hloop hskein
    rw [bracket_R1_pos A b bloop bkink hloop hskein, jones_smul_writheUnit]
  · intro w b bloop bkink hloop hskein
    rw [bracket_R1_neg A b bloop bkink hloop hskein, jones_smul_writheUnit_inv]
  · intro w bI bU bloopU b1 b2 bT hloop h1 h2 hT
    rw [bracket_R2 A bI bU bloopU b1 b2 bT hloop h1 h2 hT]
  · intro w bL bL' b0 bInf bInf' hL hL' hR2
    rw [bracket_R3 A bL bL' b0 bInf bInf' hL hL' hR2]

/-! ### A concrete instantiation over the Laurent polynomial ring `ℤ[A, A⁻¹]`

This section checks that the hypotheses above are not vacuous: they are satisfied by the
standard Kauffman variable `A = T 1` in `ℤ[A, A⁻¹]`, and the invariance statement has
nontrivial content there (the unknot and its once-kinked diagram both get the value `1`). -/

open LaurentPolynomial in
/-- The Kauffman variable `A` as a unit of the Laurent polynomial ring `ℤ[A, A⁻¹]`. -/
noncomputable def laurentA : (LaurentPolynomial ℤ)ˣ :=
  ⟨T 1, T (-1), by rw [← T_add]; simp, by rw [← T_add]; simp⟩

open LaurentPolynomial in
/-- Over `ℤ[A, A⁻¹]`: the once-kinked unknot diagram has writhe `1` and Kauffman bracket
`-A³`, the unknot diagram has writhe `0` and bracket `1`, and both have normalised
Jones value `1`. -/
theorem jones_unknot_kink :
    jones laurentA 1 (-(T 3 : LaurentPolynomial ℤ)) = jones laurentA 0 1 ∧
      jones laurentA 0 (1 : LaurentPolynomial ℤ) = 1 := by
  have h : (T 1 : LaurentPolynomial ℤ) ^ 3 = T 3 := by
    rw [show (3 : ℤ) = 1 + 1 + 1 by ring, T_add, T_add]; ring
  have hval : ((writheUnit laurentA : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) * 1
      = -(T 3 : LaurentPolynomial ℤ) := by
    simp only [writheUnit, mul_one, Units.val_neg, Units.val_pow_eq_pow_val]
    rw [show ((laurentA : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) = T 1 from rfl, h]
  refine ⟨?_, by simp [jones]⟩
  rw [← hval, show (1 : ℤ) = 0 + 1 from rfl, jones_smul_writheUnit]

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

