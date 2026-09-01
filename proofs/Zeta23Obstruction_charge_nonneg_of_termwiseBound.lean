import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Zeta23Obstruction

/-!
## The abstract model

We model a "fixed-kernel pointwise-discard linear certificate" in a finite-dimensional,
purely combinatorial way.

* A **kernel** is a fixed function `R : ℝ → ℝ`.  In the intended application `R` is the
  (analytically continued) remainder kernel of the certificate; only its *values* matter here.
* A **deep region** is a set `D : Set ℝ` of admissible evaluation points ("deep points").
* A **deep-pair configuration** consists of two species, each placed at a deep point and
  carrying a strictly positive weight.  (Two species is exactly the "deep-pair" situation:
  the argument needs no more, and works verbatim for any positive number of species.)
* The certificate charges a configuration linearly, `charge R C = ∑ i, w i * R (z i)`, and the
  *pointwise discard* step of the chain is only licensed if every individual term is
  nonnegative, i.e. if `R` is nonnegative at each deep point of the configuration.

`Valid R D` is exactly the assertion that the pointwise-discard step is licensed for every
deep-pair configuration.  The obstruction says: one deep point `z ∈ D` with `R z < 0`
destroys validity, and exhibits an explicit configuration on which the termwise bound fails
and the total charge is negative.
-/

/-- A deep-pair configuration over the deep region `D`: two species, each located at a deep
point and carrying a strictly positive weight. -/
structure DeepPairConfig (D : Set ℝ) where
  /-- the location of each species -/
  pt : Fin 2 → ℝ
  /-- the (positive) weight of each species -/
  wt : Fin 2 → ℝ
  /-- all species sit at deep points -/
  pt_deep : ∀ i, pt i ∈ D
  /-- all weights are strictly positive -/
  wt_pos : ∀ i, 0 < wt i

/-- The linear charge of a configuration against a fixed kernel `R`. -/
def charge (R : ℝ → ℝ) {D : Set ℝ} (C : DeepPairConfig D) : ℝ :=
  ∑ i, C.wt i * R (C.pt i)

/-- The termwise bound required by the pointwise-discard step: the kernel must be
nonnegative at each deep point of the configuration. -/
def TermwiseBound (R : ℝ → ℝ) {D : Set ℝ} (C : DeepPairConfig D) : Prop :=
  ∀ i, 0 ≤ R (C.pt i)

/-- Validity of the fixed-kernel pointwise-discard certificate: the termwise bound holds for
every deep-pair configuration. -/
def Valid (R : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ C : DeepPairConfig D, TermwiseBound R C

/-- A valid pointwise-discard certificate always yields a nonnegative charge: this is the
"linear charging" half of the chain, and it is the only thing the chain gets out of the
discard step. -/
theorem charge_nonneg_of_termwiseBound {R : ℝ → ℝ} {D : Set ℝ} (C : DeepPairConfig D)
    (h : TermwiseBound R C) : 0 ≤ charge R C := by
  refine Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (C.wt_pos i)) (h i)

/-- Validity of the certificate is *equivalent* to pointwise nonnegativity of the fixed kernel
on the deep region: the quantifier structure of the chain leaves no room for cancellation. -/
theorem valid_iff (R : ℝ → ℝ) (D : Set ℝ) :
    Valid R D ↔ ∀ z ∈ D, 0 ≤ R z := by
  constructor
  · intro hV z hz
    exact hV ⟨fun _ => z, fun _ => 1, fun _ => hz, fun _ => one_pos⟩ 0
  · intro h C i
    exact h _ (C.pt_deep i)

/-!
## The obstruction

Fixed kernel + pointwise discard + one bad deep value ⟹ invalid.
-/

/-- **Subclass obstruction.**  Let `R : ℝ → ℝ` be the fixed kernel of a pointwise-discard
linear certificate and let `D` be the deep region.  If the (analytically continued) kernel
takes a strictly negative value at some deep point `z` — as in the repaired witness — then:

* there is an explicit deep-pair configuration, with both species sitting at `z`, on which the
  chain's termwise bound fails and whose total charge is strictly negative; and
* the certificate is invalid, i.e. `¬ Valid R D`.

Equivalently (contrapositive), a valid certificate forces `0 ≤ R z` at every deep point, so no
fixed kernel with a negative deep value can support the chain. -/
theorem subclass_obstruction_statement
    (R : ℝ → ℝ) (D : Set ℝ) (z : ℝ) (hzD : z ∈ D) (hz : R z < 0) :
    (∃ C : DeepPairConfig D,
        (∀ i, C.pt i = z) ∧ ¬ TermwiseBound R C ∧ charge R C < 0) ∧
      ¬ Valid R D := by
  refine ⟨⟨⟨fun _ => z, fun _ => 1, fun _ => hzD, fun _ => one_pos⟩, fun _ => rfl, ?_, ?_⟩, ?_⟩
  · intro h
    exact absurd (h 0) (not_le.mpr hz)
  · have : charge R ⟨fun _ => z, fun _ => 1, fun _ => hzD, fun _ => one_pos⟩
        = 2 * R z := by
      simp [charge]
    rw [this]
    linarith
  · intro hV
    exact absurd ((valid_iff R D).mp hV z hzD) (not_le.mpr hz)

/-- Consequence for a certificate that *claims* pointwise nonnegativity of its fixed kernel:
such a claim is incompatible with a negative deep value. -/
theorem no_certificate_with_negative_deep_value
    (R : ℝ → ℝ) (h_pos : ∀ x, 0 ≤ R x) (z : ℝ) : ¬ R z < 0 :=
  not_lt.mpr (h_pos z)

end Zeta23Obstruction

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

