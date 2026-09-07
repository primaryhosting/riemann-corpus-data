import Mathlib

/-!
# Harmonic divisor (Ore) numbers

A **harmonic divisor number** — also called an **Ore number** after Øystein Ore — is a
positive integer `n` whose divisors have an **integer harmonic mean**. Writing `σ(n)` for
the sum of divisors and `τ(n)` for the number of divisors, the harmonic mean of the
divisors of `n` is
`H(n) = n · τ(n) / σ(n)`,
so `n` is harmonic exactly when `σ(n) ∣ n · τ(n)` (equivalently `H(n) ∈ ℤ`). The smallest
examples are `1, 6, 28, 140, 270, 496, 672, …`.

Every **perfect** number is harmonic: if `σ(n) = 2n` then `σ(n) = 2n ∣ n · τ(n)` whenever
`τ(n)` is even, and `τ(n)` is even for every non-square, in particular for every even
perfect number. Ore conjectured that **there is no odd harmonic divisor number greater
than `1`**. This is still OPEN, and its truth would imply that **no odd perfect number
exists** (an odd perfect number would be an odd harmonic number `> 1`). See the connection
recorded in the docstring of `OddHarmonicExists` below.

This file:

* proves concrete, kernel-verified harmonic divisor numbers `6, 28, 140, 270, 496`;
* records a non-example (`4` is not harmonic); and
* records Ore's OPEN odd-harmonic question as an **unproven `def`**, `OddHarmonicExists`.

Ore's conjecture is neither asserted nor denied here.
-/

namespace Brockian.OreHarmonicNumbers

/-- Sum of all divisors, `σ(n) = ∑_{d ∣ n} d`. For small literals `sigma1 n` reduces
under `decide`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Number of divisors, `τ(n) = #{d : d ∣ n}`. For small literals `tau n` reduces under
`decide`. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- `n` is a **harmonic divisor (Ore) number**: `n > 0` and `σ(n) ∣ n · τ(n)`, i.e. the
harmonic mean `H(n) = n · τ(n) / σ(n)` of the divisors of `n` is an integer. -/
def Harmonic (n : ℕ) : Prop := 0 < n ∧ sigma1 n ∣ n * tau n

/-- OPEN (Ore's conjecture, in negated form): **does an odd harmonic divisor number
greater than `1` exist?** Its non-existence is Ore's conjecture, which would imply that
there is no odd perfect number (every perfect number is harmonic, so an odd perfect number
would be an odd harmonic number `> 1`). Recorded here as an **unproven `def`**; this file
neither proves nor disproves it. -/
def OddHarmonicExists : Prop := ∃ n : ℕ, 1 < n ∧ Odd n ∧ Harmonic n

/-! ## Concrete verified harmonic divisor numbers -/

/-- FLAGSHIP — `6` is harmonic: `σ(6) = 12`, `τ(6) = 4`, `6·4 = 24`, and `12 ∣ 24`
(harmonic mean `H(6) = 2`). `6` is the smallest harmonic number `> 1` (and is perfect). -/
theorem harmonic_6 : Harmonic 6 :=
  ⟨by norm_num, by decide⟩

/-- FLAGSHIP — `28` is harmonic: `σ(28) = 56`, `τ(28) = 6`, `28·6 = 168`, and `56 ∣ 168`
(harmonic mean `H(28) = 3`). `28` is perfect. -/
theorem harmonic_28 : Harmonic 28 :=
  ⟨by norm_num, by decide⟩

set_option maxRecDepth 4000 in
/-- FLAGSHIP — `140` is harmonic: `σ(140) = 336`, `τ(140) = 12`, `140·12 = 1680`, and
`336 ∣ 1680` (harmonic mean `H(140) = 5`). `140` is the first non-perfect harmonic number. -/
theorem harmonic_140 : Harmonic 140 :=
  ⟨by norm_num, by decide⟩

set_option maxRecDepth 8000 in
/-- FLAGSHIP — `270` is harmonic: `σ(270) = 720`, `τ(270) = 16`, `270·16 = 4320`, and
`720 ∣ 4320` (harmonic mean `H(270) = 6`). -/
theorem harmonic_270 : Harmonic 270 :=
  ⟨by norm_num, by decide⟩

set_option maxRecDepth 16000 in
/-- FLAGSHIP — `496` is harmonic: `σ(496) = 992`, `τ(496) = 10`, `496·10 = 4960`, and
`992 ∣ 4960` (harmonic mean `H(496) = 5`). `496` is perfect. -/
theorem harmonic_496 : Harmonic 496 :=
  ⟨by norm_num, by decide⟩

/-! ## A non-example -/

/-- `4` is **not** harmonic: `σ(4) = 7`, `τ(4) = 3`, `4·3 = 12`, and `7 ∤ 12`
(harmonic mean `H(4) = 12/7 ∉ ℤ`). -/
theorem not_harmonic_4 : ¬ Harmonic 4 := by
  unfold Harmonic
  decide

end Brockian.OreHarmonicNumbers
