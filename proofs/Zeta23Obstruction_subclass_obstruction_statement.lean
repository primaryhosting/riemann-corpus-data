import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace Zeta23Obstruction

/-- A *deep-pair configuration*: two distinct "deep points" carrying strictly positive
species weights.  This is the abstract finite-dimensional model of the configuration data
a fixed-kernel certificate is tested against. -/
structure DeepPairConfig where
  /-- The (strictly positive) per-species weights. -/
  weight : Fin 2 → ℝ
  /-- The deep points at which the fixed kernel is evaluated. -/
  deep : Fin 2 → ℝ
  weight_pos : ∀ i, 0 < weight i
  deep_distinct : deep 0 ≠ deep 1

/-- The *pointwise discard* step of the certificate chain: each species' contribution is
discarded separately, so the chain's bound requires each term `weight i * R (deep i)` to be
nonnegative. -/
def TermwiseBound (R : ℝ → ℝ) (c : DeepPairConfig) : Prop :=
  ∀ i : Fin 2, 0 ≤ c.weight i * R (c.deep i)

/-- The linear charge functional attached to a configuration by a fixed kernel `R`. -/
noncomputable def charge (R : ℝ → ℝ) (c : DeepPairConfig) : ℝ :=
  ∑ i : Fin 2, c.weight i * R (c.deep i)

/-- Soundness of the certificate scheme under the pointwise-positivity hypothesis
`h_pos : ∀ x, 0 ≤ R x`: with a globally nonnegative kernel, both the termwise (pointwise
discard) bound and the resulting linear charge bound hold on every configuration. -/
theorem certificate_sound_of_kernel_nonneg (R : ℝ → ℝ) (h_pos : ∀ x, 0 ≤ R x)
    (c : DeepPairConfig) : TermwiseBound R c ∧ 0 ≤ charge R c := by
  have hterm : TermwiseBound R c := fun i =>
    mul_nonneg (c.weight_pos i).le (h_pos _)
  refine ⟨hterm, ?_⟩
  exact Finset.sum_nonneg fun i _ => hterm i

/-- **Abstract subclass obstruction.**

For a certificate with *fixed kernel* `R : ℝ → ℝ`, used via *pointwise discard* and
per-species linear charging, the existence of a single point `z` with `R z < 0` (the
"bad deep value" of the repaired witness) is *equivalent* to the existence of a deep-pair
configuration on which both the termwise bound and the linear charge bound fail.

Thus: fixed kernel + pointwise discard + one bad deep value ⟹ the certificate is invalid
against deep-pair configurations. -/
theorem subclass_obstruction_statement (R : ℝ → ℝ) :
    (∃ z : ℝ, R z < 0) ↔
      ∃ c : DeepPairConfig, ¬ TermwiseBound R c ∧ charge R c < 0 := by
  constructor
  · rintro ⟨z, hz⟩
    set b : ℝ := R (z + 1) with hb
    have hden : 0 < -R z := by linarith
    have hnum : (0 : ℝ) < 1 + |b| := by positivity
    set w : ℝ := (1 + |b|) / (-R z) with hw
    have hwpos : 0 < w := div_pos hnum hden
    have hkey : w * R z = -(1 + |b|) := by
      rw [hw, div_mul_eq_mul_div, div_eq_iff (ne_of_gt hden)]
      ring
    refine ⟨⟨![w, 1], ![z, z + 1], ?_, ?_⟩, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hwpos
      · norm_num
    · simp
    · intro h
      have h0 := h 0
      simp only [Matrix.cons_val_zero] at h0
      rw [hkey] at h0
      linarith
    · have habs : b ≤ |b| := le_abs_self b
      simp only [charge, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_mul]
      rw [hkey, ← hb]
      linarith
  · rintro ⟨c, -, hcharge⟩
    by_contra hcon
    push_neg at hcon
    have : 0 ≤ charge R c :=
      Finset.sum_nonneg fun i _ => mul_nonneg (c.weight_pos i).le (hcon _)
    linarith

end Zeta23Obstruction

