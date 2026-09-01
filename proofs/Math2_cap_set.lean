import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Filter Finset

/-- The *cap set number* `capSetNumber n` is the largest size of a subset of `𝔽₃ⁿ`
containing no non-trivial three-term arithmetic progression (a *cap set*).

Here `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`, and `ThreeAPFree` is Mathlib's predicate saying
that `a + c = b + b` with `a, b, c` in the set forces `a = b` (hence `a = b = c`). -/
noncomputable def capSetNumber (n : ℕ) : ℕ :=
  addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))

/-- The cardinality of `𝔽₃ⁿ` is `3 ^ n`. -/
lemma card_space (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp [ZMod.card]

/-- Every 3AP-free subset of `𝔽₃ⁿ` has size at most `capSetNumber n`. -/
lemma card_le_capSetNumber {n : ℕ} (A : Finset (Fin n → ZMod 3))
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) : #A ≤ capSetNumber n :=
  ThreeAPFree.le_addRothNumber hA (Finset.subset_univ _)

/-- Quantitative form of the cap set bound, coming from Roth's theorem for finite abelian
groups: if `3 ^ n` is large enough in terms of `ε`, then every 3AP-free subset of `𝔽₃ⁿ`
has size at most `ε * 3 ^ n`. -/
lemma capSetNumber_le_of_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : cornersTheoremBound ε ≤ 3 ^ n) : (capSetNumber n : ℝ) ≤ ε * 3 ^ n := by
  by_contra h
  push_neg at h
  obtain ⟨A, -, hAcard, hA⟩ :=
    addRothNumber_spec (s := (Finset.univ : Finset (Fin n → ZMod 3)))
  refine roth_3ap_theorem ε hε (by rwa [card_space]) A ?_ hA
  rw [card_space]
  rw [capSetNumber] at h
  rw [hAcard]
  exact_mod_cast h.le

/-- The **cap set theorem**: a subset of `𝔽₃ⁿ` with no non-trivial three-term arithmetic
progression has size at most `ε * 3 ^ n` once `n` is large enough (depending on `ε`). -/
theorem cap_set_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn A hA ↦ ?_⟩
  have hpow : cornersTheoremBound ε ≤ 3 ^ n :=
    hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  refine le_trans ?_ (capSetNumber_le_of_le hε hpow)
  exact_mod_cast card_le_capSetNumber A hA

/-- The **cap set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt, here obtained from Roth's
theorem for finite abelian groups): the maximal size of a subset of `𝔽₃ⁿ` without non-trivial
three-term arithmetic progressions is `o(3 ^ n)`. -/
theorem cap_set :
    (fun n : ℕ ↦ (capSetNumber n : ℝ)) =o[atTop] (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (cornersTheoremBound ε)] with n hn
  have hpow : cornersTheoremBound ε ≤ 3 ^ n :=
    hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  have h := capSetNumber_le_of_le hε hpow
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h

end Math2

