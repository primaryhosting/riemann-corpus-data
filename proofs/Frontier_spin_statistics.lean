/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-!
## The spin–statistics connection

The spin–statistics theorem of relativistic quantum field theory states that a field of
integer spin must be quantized with commutators (Bose statistics) and a field of
half-odd-integer spin with anticommutators (Fermi statistics); equivalently, the exchange
phase of a field of spin `j` is `(-1)^(2j)`.  Quantizing with the *wrong* statistics forces
the field to vanish identically (Pauli's argument, in the Wightman framework:
Streater–Wightman, *PCT, Spin and Statistics, and All That*).

Below, spin is recorded by the natural number `s = 2j` ("twice the spin"), so that integer
spin means `Even s` and half-odd-integer spin means `Odd s`.  The exchange phase is
`exchangePhase s = (-1)^s`.

The main theorem `Frontier.spin_statistics` is the Pauli argument, formalized as a
Lean-checked *reduction*: from
* the abstract Wightman data (a complex inner-product space of states, a vacuum vector,
  smeared field operators together with their adjoints), and
* the identity relating the two orders of the two-point function which the analytic
  continuation step of the proof (Lorentz covariance + locality + edge-of-the-wedge)
  produces, carrying the sign `ε · (-1)^s`,

positivity of the inner product forces the field and its adjoint to annihilate the vacuum
whenever `ε ≠ (-1)^s`, i.e. whenever the statistics is wrong for the spin.  If in addition
the vacuum is separating, the field vanishes identically.

The only genuinely nontrivial Mathlib input is positivity of the inner product,
`inner_self_eq_norm_sq_to_K` together with `inner_self_eq_zero`.
-/

/-- The exchange phase of a field of spin `j`, where `s = 2j` is twice the spin:
`(-1)^(2j)`. -/
def exchangePhase (s : ℕ) : ℤ := (-1) ^ s

/-- A field has *Bose* statistics exactly when its spin is an integer, i.e. `s = 2j` is even. -/
def IsBosonic (s : ℕ) : Prop := Even s

/-- A field has *Fermi* statistics exactly when its spin is half-odd-integral,
i.e. `s = 2j` is odd. -/
def IsFermionic (s : ℕ) : Prop := Odd s

@[simp] lemma exchangePhase_eq_one_iff (s : ℕ) : exchangePhase s = 1 ↔ IsBosonic s := by
  simpa [exchangePhase, IsBosonic] using (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num))

@[simp] lemma exchangePhase_eq_neg_one_iff (s : ℕ) : exchangePhase s = -1 ↔ IsFermionic s := by
  constructor
  · intro h
    rcases Nat.even_or_odd s with he | ho
    · rw [exchangePhase, he.neg_one_pow] at h; norm_num at h
    · exact ho
  · intro h
    simpa [exchangePhase] using h.neg_one_pow

lemma exchangePhase_eq_one_or_neg_one (s : ℕ) :
    exchangePhase s = 1 ∨ exchangePhase s = -1 :=
  neg_one_pow_eq_or ℤ s

/-- Abstract Wightman data for a single (smeared) quantum field: a complex inner-product
space of states, a vacuum vector, an operator `field f` for each test function `f : T`,
and its adjoint `fieldStar f`. -/
structure WightmanField (T : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vacuum state. -/
  vacuum : H
  /-- The field operator smeared with a test function. -/
  field : T → (H →ₗ[ℂ] H)
  /-- The adjoint (conjugate) field operator. -/
  fieldStar : T → (H →ₗ[ℂ] H)
  /-- `fieldStar f` is the adjoint of `field f`. -/
  adjoint : ∀ (f : T) (x y : H), inner ℂ (field f x) y = inner ℂ x (fieldStar f y)

namespace WightmanField

variable {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The adjoint relation, read in the other direction. -/
lemma adjoint' (F : WightmanField T H) (f : T) (x y : H) :
    inner ℂ (F.fieldStar f x) y = inner ℂ x (F.field f y) := by
  have h := F.adjoint f y x
  have h2 : (starRingEnd ℂ) (inner ℂ (F.field f y) x)
      = (starRingEnd ℂ) (inner ℂ y (F.fieldStar f x)) := by rw [h]
  simpa [inner_conj_symm] using h2.symm

/-- The vacuum expectation `⟪Ω, φ(f) φ*(f) Ω⟫` is the squared norm of `φ*(f) Ω`. -/
lemma inner_vacuum_field_fieldStar (F : WightmanField T H) (f : T) :
    inner ℂ F.vacuum (F.field f (F.fieldStar f F.vacuum))
      = (‖F.fieldStar f F.vacuum‖ : ℂ) ^ 2 := by
  rw [← F.adjoint' f F.vacuum (F.fieldStar f F.vacuum), inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The vacuum expectation `⟪Ω, φ*(f) φ(f) Ω⟫` is the squared norm of `φ(f) Ω`. -/
lemma inner_vacuum_fieldStar_field (F : WightmanField T H) (f : T) :
    inner ℂ F.vacuum (F.fieldStar f (F.field f F.vacuum))
      = (‖F.field f F.vacuum‖ : ℂ) ^ 2 := by
  rw [← F.adjoint f F.vacuum (F.field f F.vacuum), inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The vacuum is *separating* for the field if no nonzero field operator annihilates it. -/
def SeparatingVacuum (F : WightmanField T H) : Prop :=
  ∀ f : T, (F.field f F.vacuum = 0 → F.field f = 0) ∧
           (F.fieldStar f F.vacuum = 0 → F.fieldStar f = 0)

end WightmanField

/-- **Spin–statistics (Pauli's argument), Lean-checked reduction.**

Let `F` be Wightman data for a field of spin `j`, with `s = 2j`, quantized with exchange
sign `ε ∈ {+1, -1}` (`ε = +1`: commutators/Bose, `ε = -1`: anticommutators/Fermi).

Hypothesis `hW` is the output of the analytic-continuation step of the Wightman proof: the
two orders of the two-point function at coincident points are related by the sign
`ε · (-1)^s` (this sign is `+1` precisely for the statistics matching the spin).

If the statistics is *wrong* for the spin, i.e. `ε ≠ (-1)^s`, then both the field and its
adjoint annihilate the vacuum.  (The proof is pure positivity: the two squared norms
`‖φ(f)Ω‖²` and `‖φ*(f)Ω‖²` are then negatives of each other, hence both vanish.) -/
theorem spin_statistics {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : WightmanField T H) (s : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hwrong : ε ≠ exchangePhase s)
    (hW : ∀ f : T, inner ℂ F.vacuum (F.field f (F.fieldStar f F.vacuum))
        = ((ε * exchangePhase s : ℤ) : ℂ) *
            inner ℂ F.vacuum (F.fieldStar f (F.field f F.vacuum))) :
    ∀ f : T, F.field f F.vacuum = 0 ∧ F.fieldStar f F.vacuum = 0 := by
  -- Wrong statistics means the sign produced by the analytic continuation is `-1`.
  have hsign : ε * exchangePhase s = -1 := by
    rcases hε with h | h <;> rcases exchangePhase_eq_one_or_neg_one s with h' | h' <;>
      simp_all
  intro f
  have h := hW f
  rw [F.inner_vacuum_field_fieldStar f, F.inner_vacuum_fieldStar_field f, hsign] at h
  -- `‖φ*(f)Ω‖² = -‖φ(f)Ω‖²`, with both sides real; positivity forces both to vanish.
  have hre : ‖F.fieldStar f F.vacuum‖ ^ 2 = -(‖F.field f F.vacuum‖ ^ 2) := by
    have h' := congrArg Complex.re h
    simp [← Complex.ofReal_pow] at h'
    linarith [h']
  have h1 : ‖F.field f F.vacuum‖ = 0 := by
    nlinarith [norm_nonneg (F.field f F.vacuum), norm_nonneg (F.fieldStar f F.vacuum),
      sq_nonneg ‖F.field f F.vacuum‖, sq_nonneg ‖F.fieldStar f F.vacuum‖]
  have h2 : ‖F.fieldStar f F.vacuum‖ = 0 := by
    nlinarith [norm_nonneg (F.fieldStar f F.vacuum), sq_nonneg ‖F.fieldStar f F.vacuum‖]
  exact ⟨norm_eq_zero.mp h1, norm_eq_zero.mp h2⟩

/-- With a separating vacuum, a field quantized with the wrong statistics for its spin
vanishes identically. -/
theorem spin_statistics_field_eq_zero {T H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : WightmanField T H) (s : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hwrong : ε ≠ exchangePhase s)
    (hW : ∀ f : T, inner ℂ F.vacuum (F.field f (F.fieldStar f F.vacuum))
        = ((ε * exchangePhase s : ℤ) : ℂ) *
            inner ℂ F.vacuum (F.fieldStar f (F.field f F.vacuum)))
    (hsep : F.SeparatingVacuum) :
    ∀ f : T, F.field f = 0 ∧ F.fieldStar f = 0 := by
  intro f
  obtain ⟨h1, h2⟩ := spin_statistics F s ε hε hwrong hW f
  exact ⟨(hsep f).1 h1, (hsep f).2 h2⟩

/-- **Base case: a scalar field cannot be a fermion.**  A spin-`0` field (`s = 0`)
quantized with anticommutators (`ε = -1`) annihilates the vacuum. -/
theorem spin_statistics_scalar_not_fermionic {T H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : WightmanField T H)
    (hW : ∀ f : T, inner ℂ F.vacuum (F.field f (F.fieldStar f F.vacuum))
        = ((-1 : ℤ) : ℂ) * inner ℂ F.vacuum (F.fieldStar f (F.field f F.vacuum))) :
    ∀ f : T, F.field f F.vacuum = 0 ∧ F.fieldStar f F.vacuum = 0 := by
  refine spin_statistics F 0 (-1) (Or.inr rfl) (by decide) ?_
  simpa [exchangePhase] using hW

/-- **Base case: a spin-`1/2` field cannot be a boson.**  A field with `s = 1`
quantized with commutators (`ε = 1`) annihilates the vacuum. -/
theorem spin_statistics_spinor_not_bosonic {T H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : WightmanField T H)
    (hW : ∀ f : T, inner ℂ F.vacuum (F.field f (F.fieldStar f F.vacuum))
        = ((-1 : ℤ) : ℂ) * inner ℂ F.vacuum (F.fieldStar f (F.field f F.vacuum))) :
    ∀ f : T, F.field f F.vacuum = 0 ∧ F.fieldStar f F.vacuum = 0 := by
  refine spin_statistics F 1 1 (Or.inl rfl) (by decide) ?_
  simpa [exchangePhase] using hW

end Frontier

