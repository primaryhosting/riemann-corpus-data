import Mathlib

/-!
# k-hyperperfect numbers

A perfect number satisfies `σ(n) = 2n`, where `σ` is the sum of all divisors.
D. Minoli and R. Bear introduced the **k-hyperperfect** numbers as a one-parameter
generalization: `n` is *k-hyperperfect* when
`k · σ(n) = (k + 1) · n + (k − 1)`.

Setting `k = 1` gives `σ(n) = 2n + 0`, i.e. the ordinary perfect-number equation, so the
perfect numbers are exactly the `1`-hyperperfect numbers. Known small examples include
`6, 28` (`k = 1`), `21` and `2133` (`k = 2`), and `301` (`k = 6`).

This file proves specific `k`-hyperperfect instances (concrete, kernel-verified),
establishes the perfect-number specialization `k = 1 ↔ σ(n) = 2n`, and records the two
standard OPEN questions as unproven `def`s:

* whether a `k`-hyperperfect number exists for **every** `k ≥ 1`, and
* whether there are **infinitely many** `k`-hyperperfect numbers for each fixed `k`.

Neither open question is claimed to be resolved here.
-/

namespace Brockian.HyperperfectNumbers

/-- Sum of all divisors, `σ(n) = ∑_{d ∣ n} d`. For small literals `sigma1 n` reduces
under `decide`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is **k-hyperperfect**: `k · σ(n) = (k + 1) · n + (k − 1)` (with `n > 0`).
The subtraction `k - 1` is truncated ℕ subtraction, which is the intended value for the
relevant range `k ≥ 1`. -/
def Hyperperfect (k n : ℕ) : Prop := 0 < n ∧ k * sigma1 n = (k + 1) * n + (k - 1)

/-- OPEN: for every `k ≥ 1` there exists a `k`-hyperperfect number. Recorded as an
unproven `def`; this file does **not** prove it. -/
def HyperperfectAllK : Prop := ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, Hyperperfect k n

/-- OPEN: for each `k ≥ 1` there are infinitely many `k`-hyperperfect numbers. Recorded as
an unproven `def`; this file does **not** prove it. -/
def HyperperfectInfinitude : Prop :=
    ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Hyperperfect k n

/-! ## Concrete verified k-hyperperfect numbers -/

/-- FLAGSHIP — `6` is `1`-hyperperfect (i.e. perfect): `σ(6) = 12`, `1·12 = 2·6 + 0`. -/
theorem hyperperfect_1_6 : Hyperperfect 1 6 :=
  ⟨by norm_num, by decide⟩

/-- FLAGSHIP — `28` is `1`-hyperperfect (i.e. perfect): `σ(28) = 56`, `1·56 = 2·28 + 0`. -/
theorem hyperperfect_1_28 : Hyperperfect 1 28 :=
  ⟨by norm_num, by decide⟩

set_option maxRecDepth 4000 in
/-- FLAGSHIP — `21` is `2`-hyperperfect: `σ(21) = 32`, `2·32 = 64 = 3·21 + 1`. -/
theorem hyperperfect_2_21 : Hyperperfect 2 21 :=
  ⟨by norm_num, by decide⟩

set_option maxRecDepth 20000 in
/-- FLAGSHIP — `301` is `6`-hyperperfect: `301 = 7·43`, `σ(301) = 352`,
`6·352 = 2112 = 7·301 + 5`. -/
theorem hyperperfect_6_301 : Hyperperfect 6 301 :=
  ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
/-- FLAGSHIP — `2133` is `2`-hyperperfect: `2133 = 3³·79`, `σ(2133) = 40·80 = 3200`,
`2·3200 = 6400 = 3·2133 + 1`. -/
theorem hyperperfect_2_2133 : Hyperperfect 2 2133 :=
  ⟨by norm_num, by decide⟩

/-! ## The perfect-number specialization (k = 1) -/

/-- FLAGSHIP STRUCTURAL — `1`-hyperperfect is exactly the perfect-number condition.
With `k = 1` the defining equation `1·σ(n) = 2·n + (1−1)` collapses to `σ(n) = 2n`. -/
theorem hyperperfect_one_iff_sigma_two_mul {n : ℕ} (hn : 0 < n) :
    Hyperperfect 1 n ↔ sigma1 n = 2 * n := by
  unfold Hyperperfect
  constructor
  · rintro ⟨_, h⟩; omega
  · intro h; exact ⟨hn, by omega⟩

/-! ## A non-example -/

/-- `6` is perfect (`1`-hyperperfect) but **not** `2`-hyperperfect:
`2·σ(6) = 2·12 = 24`, whereas `3·6 + 1 = 19`. -/
theorem not_hyperperfect_2_6 : ¬ Hyperperfect 2 6 := by
  unfold Hyperperfect
  decide

end Brockian.HyperperfectNumbers
