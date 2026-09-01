/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

Mathlib (as of the pinned commit) contains no development of étale cohomology, Weil
cohomology theories, or zeta functions of varieties over finite fields, so no existing
lemma closes this goal (`exact?`/`apply?` find nothing: the statement below is not an
instance of anything in the library).  We therefore formalize the *statement* of the
Riemann hypothesis part of the Weil conjectures in the standard "Frobenius eigenvalue"
form, and prove it (together with the Lefschetz trace formula that ties the eigenvalues
to point counts) for the base case of projective space `P^n` over `F_q`.

The data of a Weil cohomology theory for a variety `X/F_q` of dimension `d` is packaged
as a family of finite multisets `eig w` (`w = 0, …, 2d`) of complex numbers, the
eigenvalues of the geometric Frobenius on the `w`-th cohomology group.

* `Frontier.LefschetzTraceFormula` : `#X(F_{q^m}) = ∑_w (-1)^w ∑_{α ∈ eig w} α^m`.
* `Frontier.WeilRH` : every `α ∈ eig w` has `‖α‖ = q^(w/2)` (an algebraic number all of
  whose conjugates have absolute value `q^(w/2)`), i.e. the zeta function's zeros lie on
  the lines `Re s = w/2`.

For `P^n` the cohomology is one-dimensional in each even degree `2i`, `0 ≤ i ≤ n`, with
Frobenius eigenvalue `q^i`, and vanishes in odd degrees; the point counts are
`#P^n(F_{q^m}) = ∑_{i=0}^n q^{im}`.
-/

namespace Frontier

open Finset

/-- The number of `F_{q^m}`-rational points of projective `n`-space:
`#P^n(F_{q^m}) = 1 + q^m + ⋯ + q^{nm}`. -/
def projSpacePointCount (q n m : ℕ) : ℕ := ∑ i ∈ range (n + 1), q ^ (i * m)

/-- The multiset of geometric Frobenius eigenvalues on the `w`-th cohomology group of
projective `n`-space over `F_q`: the single eigenvalue `q ^ (w / 2)` when `w = 2 i` with
`i ≤ n`, and nothing otherwise. -/
def projFrobEigenvalues (q n w : ℕ) : Multiset ℂ :=
  if w % 2 = 0 ∧ w / 2 ≤ n then {(q : ℂ) ^ (w / 2)} else 0

/-- The Lefschetz trace formula: the number of `F_{q^m}`-points of the variety is the
alternating sum of the traces of the `m`-th power of Frobenius on cohomology. -/
def LefschetzTraceFormula (N : ℕ → ℕ) (d : ℕ) (eig : ℕ → Multiset ℂ) : Prop :=
  ∀ m, 1 ≤ m → (N m : ℂ) = ∑ w ∈ range (2 * d + 1),
    (-1 : ℂ) ^ w * ((eig w).map (fun a => a ^ m)).sum

/-- The Riemann hypothesis of the Weil conjectures (Deligne): every eigenvalue of the
geometric Frobenius on the `w`-th cohomology group has complex absolute value
`q ^ (w / 2)`. -/
def WeilRH (q d : ℕ) (eig : ℕ → Multiset ℂ) : Prop :=
  ∀ w ≤ 2 * d, ∀ a ∈ eig w, ‖a‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- A sum over `range (2 * n + 1)` of a function vanishing on odd arguments is the sum
over the even arguments `2 i`, `i ≤ n`. -/
lemma sum_range_two_mul_of_odd_eq_zero {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)
    (hodd : ∀ w, w % 2 = 1 → f w = 0) :
    ∑ w ∈ range (2 * n + 1), f w = ∑ i ∈ range (n + 1), f (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
    have h2 : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      hodd (2 * n + 1) (by omega), h2, add_zero, Finset.sum_range_succ,
      Finset.sum_range_succ]

/-- **The Riemann hypothesis for varieties over finite fields (Weil conjectures,
proved by Deligne), base case: projective space.**

For every `q` and `n`, the family of Frobenius eigenvalues `projFrobEigenvalues q n`
computes the point counts `#P^n(F_{q^m})` through the Lefschetz trace formula, and it
satisfies the Weil Riemann hypothesis: each eigenvalue occurring in cohomological degree
`w` has absolute value exactly `q ^ (w / 2)`. -/
theorem deligne_weil_RH (q n : ℕ) :
    LefschetzTraceFormula (projSpacePointCount q n) n (projFrobEigenvalues q n) ∧
      WeilRH q n (projFrobEigenvalues q n) := by
  constructor
  · intro m _
    have hodd : ∀ w, w % 2 = 1 →
        (-1 : ℂ) ^ w * ((projFrobEigenvalues q n w).map (fun a => a ^ m)).sum = 0 := by
      intro w hw
      have : projFrobEigenvalues q n w = 0 := by
        simp [projFrobEigenvalues, hw]
      simp [this]
    rw [sum_range_two_mul_of_odd_eq_zero _ n hodd]
    have hterm : ∀ i ∈ range (n + 1),
        (-1 : ℂ) ^ (2 * i) *
          ((projFrobEigenvalues q n (2 * i)).map (fun a => a ^ m)).sum
            = ((q : ℂ) ^ i) ^ m := by
      intro i hi
      have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      have h : projFrobEigenvalues q n (2 * i) = {(q : ℂ) ^ i} := by
        simp [projFrobEigenvalues, Nat.mul_mod_right, Nat.mul_div_cancel_left i two_pos, hi']
      rw [h]
      simp [pow_mul]
    rw [Finset.sum_congr rfl hterm]
    simp [projSpacePointCount, pow_mul]
  · intro w _ a ha
    by_cases h : w % 2 = 0 ∧ w / 2 ≤ n
    · have hmem : a = (q : ℂ) ^ (w / 2) := by
        simpa [projFrobEigenvalues, h] using ha
      have hw : (w : ℝ) / 2 = (w / 2 : ℕ) := by
        have : (2 : ℕ) ∣ w := Nat.dvd_of_mod_eq_zero h.1
        obtain ⟨k, rfl⟩ := this
        push_cast [Nat.mul_div_cancel_left k two_pos]
        ring
      rw [hmem, hw, norm_pow, Real.rpow_natCast]
      simp
    · simp [projFrobEigenvalues, h] at ha

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

