import Mathlib

/-!
# Weird numbers and the open odd-weird question

A **weird number** is a natural number that is **abundant** — the sum of its proper
divisors exceeds it — but **not semiperfect**: no subset of its proper divisors sums
to the number itself.  The smallest weird number is `70`; the next is `836`.

Weird numbers sit beside perfect numbers, amicable numbers, and Giuga numbers as an
old aliquot-flavoured problem.  Abundance alone is common (`12`, `18`, `20`, `24`, …
are all abundant), and the vast majority of abundant numbers are semiperfect, so the
failure of semiperfection is what makes weirdness rare.  It is a genuinely **OPEN**
question whether an **odd** weird number exists — none is known, exactly parallel to
the odd perfect number and odd Giuga number problems.

This file
* verifies the flagship weird number `70`, kernel-checked over its `2⁷ = 128`
  divisor subsets;
* contrasts weirdness with mere abundance by showing `12` and `20` are abundant yet
  semiperfect, hence **not** weird — so weirdness is strictly stronger than abundance;
* attempts the second weird number `836` as a bonus; and
* records the odd-weird existence question as an unproven `def`.

It is **not** claimed here that odd weird numbers do or do not exist.

Verification (spec §2A triple verification):
  - `#print axioms`  : [propext, Classical.choice, Quot.sound]  (clean)
  - AXLE independent : verified @ lean-4.32.0
-/

namespace Brockian.WeirdNumbers

/-- Sum of proper divisors of `n` (the aliquot sum). -/
def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `n` is **abundant**: its proper divisors sum to more than `n`. -/
def Abundant (n : ℕ) : Prop := n < aliquot n

/-- `n` is **semiperfect**: some subset of its proper divisors sums to `n`. -/
def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

/-- `n` is **weird**: abundant but not semiperfect. -/
def Weird (n : ℕ) : Prop := Abundant n ∧ ¬ Semiperfect n

/-- OPEN: does an **odd** weird number exist?  Recorded as an unproven `def`, exactly
parallel to the odd perfect number problem; this file does **not** resolve it. -/
def OddWeirdExists : Prop := ∃ n : ℕ, Odd n ∧ Weird n

/-! ## The flagship weird number 70 -/

set_option maxRecDepth 4000 in
/-- FLAGSHIP — `70 = 2·5·7` is a weird number.

Its proper divisors are `{1, 2, 5, 7, 10, 14, 35}`, summing to
`1 + 2 + 5 + 7 + 10 + 14 + 35 = 74 > 70`, so `70` is abundant.  Yet none of the
`2⁷ = 128` subsets of those divisors sums to exactly `70`, so `70` is not
semiperfect.  Both halves are decidable and kernel-checked. -/
theorem weird_70 : Weird 70 := by
  have ha : Abundant 70 := by unfold Abundant aliquot; decide
  have hs : ¬ Semiperfect 70 := by unfold Semiperfect; decide
  exact ⟨ha, hs⟩

/-! ## Contrast: abundant but semiperfect ⇒ not weird -/

/-- `12` is abundant: `1 + 2 + 3 + 4 + 6 = 16 > 12`. -/
theorem twelve_abundant : Abundant 12 := by unfold Abundant aliquot; decide

/-- `12` is semiperfect: the subset `{2, 4, 6}` of its proper divisors sums to `12`. -/
theorem twelve_semiperfect : Semiperfect 12 := by unfold Semiperfect; decide

/-- `12` is **not** weird: it is abundant, but being semiperfect defeats weirdness.
This is the contrast that shows weirdness is strictly stronger than abundance. -/
theorem twelve_not_weird : ¬ Weird 12 := fun h => h.2 twelve_semiperfect

/-- `20` is abundant (`1 + 2 + 4 + 5 + 10 = 22 > 20`) and semiperfect
(`1 + 4 + 5 + 10 = 20`), hence **not** weird. -/
theorem twenty_not_weird : ¬ Weird 20 := by
  have hs : Semiperfect 20 := by unfold Semiperfect; decide
  exact fun h => h.2 hs

/-! ## Bonus: the second weird number 836 -/

set_option maxRecDepth 20000 in
/-- BONUS — `836 = 2²·11·19` is the second weird number.

Its proper divisors are `{1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418}`, summing to
`844 > 836` (abundant), and none of the `2¹¹ = 2048` subsets sums to exactly `836`
(not semiperfect).  The kernel checks both halves; `native_decide` is deliberately
avoided. -/
theorem weird_836 : Weird 836 := by
  have ha : Abundant 836 := by unfold Abundant aliquot; decide
  have hs : ¬ Semiperfect 836 := by unfold Semiperfect; decide
  exact ⟨ha, hs⟩

end Brockian.WeirdNumbers
