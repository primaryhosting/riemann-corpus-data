/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a `/-!` module docstring before `import`; the requested header is
-- reproduced verbatim above as a block comment and again as a module docstring below.)

import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Asymptotics Filter

namespace Math2

/-- `capSetNumber n` is the largest size of a *cap set* in `𝔽₃ⁿ`, i.e. of a subset of
`Fin n → ZMod 3` containing no three-term arithmetic progression `a, b, c` with `a + c = b + b`
other than the trivial ones `a = b = c`. -/
noncomputable def capSetNumber (n : ℕ) : ℕ :=
  addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))

/-- Any 3AP-free (cap) set in `𝔽₃ⁿ` has size at most `capSetNumber n`. -/
theorem card_le_capSetNumber {n : ℕ} (A : Finset (Fin n → ZMod 3))
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) : #A ≤ capSetNumber n :=
  hA.le_addRothNumber (Finset.subset_univ _)

/-- **The cap set theorem**: subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression
have size `o(3ⁿ)`. -/
theorem cap_set :
    IsLittleO atTop (fun n : ℕ ↦ (capSetNumber n : ℝ)) (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  rw [isLittleO_iff]
  intro ε hε
  rw [eventually_atTop]
  refine ⟨cornersTheoremBound ε, fun n hn ↦ ?_⟩
  obtain ⟨A, -, hcard, hAfree⟩ := addRothNumber_spec (Finset.univ : Finset (Fin n → ZMod 3))
  have hcard3 : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by simp
  have hG : cornersTheoremBound ε ≤ Fintype.card (Fin n → ZMod 3) := by
    rw [hcard3]
    exact hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  have hroth := roth_3ap_theorem ε hε hG A
  rw [hcard3] at hroth
  have h2 : ¬ ((ε : ℝ) * 3 ^ n ≤ (#A : ℝ)) := fun h ↦
    hroth (by push_cast at h ⊢; linarith) hAfree
  rw [capSetNumber, ← hcard]
  simp only [Real.norm_natCast, norm_pow, Real.norm_ofNat]
  linarith [not_le.1 h2]

/-- Explicit `ε`-`N` form of the cap set theorem: for every `ε > 0`, every cap set in `𝔽₃ⁿ`
has size at most `ε · 3ⁿ` once `n` is large enough. -/
theorem cap_set_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (isLittleO_iff.1 cap_set hε)
  refine ⟨N, fun n hn A hA ↦ ?_⟩
  have h := hN n hn
  simp only [Real.norm_natCast, norm_pow, Real.norm_ofNat] at h
  exact le_trans (by exact_mod_cast card_le_capSetNumber A hA) h

end Math2

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

