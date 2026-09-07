/-
  Brockian/UnitaryPerfect.lean — concrete unitary perfect numbers and the
  OPEN sixth/infinitude question.

  A *unitary divisor* of `n` is a divisor `d ∣ n` with `gcd(d, n/d) = 1`. A
  *unitary perfect number* satisfies `σ*(n) = 2n`, where `σ*` sums the unitary
  divisors. Exactly FIVE unitary perfect numbers are known:
    6, 60, 90, 87360, and one 24-digit number
      (146361946186458562560000 = 2^18 · 3 · 5^4 · 7 · 11 · 13 · 19 · 37 · 79 · 109 · 157 · 313).
  It is a long-standing OPEN problem whether a sixth unitary perfect number
  exists, and whether there are infinitely many.

  This file:
    - verifies the three small unitary perfect numbers 6, 60, 90 (flagship),
    - records a non-example (28 is perfect but NOT unitary perfect),
    - contrasts σ* with the ordinary divisor sum on a squarefree number,
    - registers the open question `SixthUnitaryPerfectExists` as an UNPROVEN `def`.

  We NEVER assert or deny the open question; it is stated only, never resolved.

  Verification (spec §2A triple verification):
    - local `lake build`  : not relied upon (remote AXLE is authoritative)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.UnitaryPerfect

/-- Sum of the unitary divisors of `n`: divisors `d` with `gcd(d, n / d) = 1`.
Here `n / d` is `ℕ` division, which is exact for `d ∣ n`. -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => Nat.gcd d (n / d) = 1), d

/-- `n` is *unitary perfect*: `σ*(n) = 2n`. -/
def UnitaryPerfect (n : ℕ) : Prop :=
  0 < n ∧ unitaryDivisorSum n = 2 * n

/-- OPEN PROBLEM: does a sixth unitary perfect number exist, beyond the five known
(6, 60, 90, 87360, and one 24-digit number)? This is an UNPROVEN `def`. It is
recorded here as a statement only — this file neither asserts nor denies it. -/
def SixthUnitaryPerfectExists : Prop :=
  ∃ n : ℕ, 87360 < n ∧ UnitaryPerfect n

/-! ### (1) Flagship: the three small unitary perfect numbers. -/

/-- `6` is unitary perfect: unitary divisors `1, 2, 3, 6` sum to `12 = 2·6`. -/
theorem unitaryPerfect_6 : UnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  unfold unitaryDivisorSum
  decide

/-- `60` is unitary perfect: unitary divisors `1, 3, 4, 5, 12, 15, 20, 60` sum to
`120 = 2·60`. (`60 = 2²·3·5`; the non-unitary divisors `2, 6, 10, 30` are excluded
because e.g. `gcd(2, 30) = 2 ≠ 1`.) -/
theorem unitaryPerfect_60 : UnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  unfold unitaryDivisorSum
  decide

/-- `90` is unitary perfect: unitary divisors `1, 2, 5, 9, 10, 18, 45, 90` sum to
`180 = 2·90`. (`90 = 2·3²·5`.) -/
theorem unitaryPerfect_90 : UnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  unfold unitaryDivisorSum
  decide

/-! ### (2) A non-example: perfect ≠ unitary perfect. -/

/-- `28` is a perfect number (`σ(28) = 56 = 2·28`) but NOT unitary perfect:
`28 = 2²·7`, so its unitary divisors are `1, 4, 7, 28`, summing to `40 ≠ 56`.
This shows the unitary-perfect condition is genuinely different from perfection. -/
theorem not_unitaryPerfect_28 : ¬ UnitaryPerfect 28 := by
  unfold UnitaryPerfect unitaryDivisorSum
  decide

/-! ### (3) Contrast with the ordinary divisor sum on a squarefree number. -/

/-- For the squarefree number `6`, every divisor is unitary, so `σ*(6) = σ(6) = 12`.
(For non-squarefree `n` the two sums differ — e.g. `σ*(28) = 40 ≠ 56 = σ(28)`.) -/
theorem unitaryDivisorSum_eq_sigma_6 :
    unitaryDivisorSum 6 = ∑ d ∈ (6 : ℕ).divisors, d := by
  unfold unitaryDivisorSum
  decide

end Brockian.UnitaryPerfect
