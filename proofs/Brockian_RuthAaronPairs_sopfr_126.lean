/-
  Brockian/RuthAaronPairs.lean — Ruth–Aaron pairs and the open infinitude.

  `sopfr n` is the sum of the prime factors of `n` counted WITH multiplicity (the
  "integer logarithm"). A Ruth–Aaron pair is a pair of consecutive integers `(n, n+1)`
  with `sopfr n = sopfr (n+1)`. The name commemorates the game in which Hank Aaron's
  715th home run passed Babe Ruth's record of 714:
      714 = 2·3·7·17   (sopfr 714 = 2+3+7+17 = 29)
      715 = 5·11·13    (sopfr 715 = 5+11+13   = 29).
  Carl Pomerance popularized the pair after a student, Carol Nelson, noticed the
  coincidence. It is a well-known OPEN problem whether there are infinitely many
  Ruth–Aaron pairs; only heuristic (Erdős–Pomerance) evidence is known.

  What is proved here: concrete Ruth–Aaron pairs (5, 77, 125, and the namesake 714),
  their shared sopfr values, and a non-example. The infinitude statement is recorded
  ONLY as an unproven `def` (a Prop container) and is never asserted as a theorem.

  Verification note: `Nat.primeFactorsList` is defined by well-founded recursion, so it
  does NOT reduce under `decide`/`rfl` in the kernel (and `native_decide` is barred).
  Instead each concrete factor list is validated by `Nat.primeFactorsList_unique`
  (product = n, all entries prime ⇒ the list is a permutation of `primeFactorsList n`),
  and `List.Perm.sum_eq` transports the sum — which is permutation-invariant — to the
  literal value. No `sorry`/`admit`, no added axioms, no `native_decide`.

  Verification (spec §2A triple verification):
    - `#print axioms`  : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.RuthAaronPairs

/-- Sum of prime factors of `n` with multiplicity (sopfr / integer logarithm). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- `(n, n+1)` is a Ruth–Aaron pair: equal sum-of-prime-factors-with-multiplicity. -/
def RuthAaron (n : ℕ) : Prop := sopfr n = sopfr (n + 1)

/-- **OPEN.** There are infinitely many Ruth–Aaron pairs. This is an unresolved
conjecture (Erdős–Pomerance heuristics only); it is recorded here as an unproven `def`,
a Prop container, and is *never* asserted as a theorem anywhere in this file. -/
def RuthAaronInfinitude : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ RuthAaron n

/-- Compute `sopfr n` from an explicit prime factorization. If `l` is a list of primes
whose product is `n`, then by uniqueness of prime factorization `l` is a permutation of
`Nat.primeFactorsList n`, and since the sum of a list is permutation-invariant,
`sopfr n = l.sum`. This is the kernel-reduction-free workhorse for the concrete pairs
below (`primeFactorsList` is well-founded recursion and will not `decide`). -/
theorem sopfr_eq {n s : ℕ} {l : List ℕ}
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, Nat.Prime p) (hsum : l.sum = s) :
    sopfr n = s := by
  have h : List.Perm l (Nat.primeFactorsList n) :=
    Nat.primeFactorsList_unique hprod hprime
  unfold sopfr
  rw [← h.sum_eq, hsum]

/-! ### The shared sopfr values (illustrative) -/

/-- `sopfr 714 = 2 + 3 + 7 + 17 = 29` (Babe Ruth's home-run record). -/
theorem sopfr_714 : sopfr 714 = 29 :=
  sopfr_eq (l := [2, 3, 7, 17]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 715 = 5 + 11 + 13 = 29` (Hank Aaron's 715th home run). -/
theorem sopfr_715 : sopfr 715 = 29 :=
  sopfr_eq (l := [5, 11, 13]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-! ### Concrete Ruth–Aaron pairs (flagship) -/

/-- `sopfr 5 = 5` and `sopfr 6 = 2 + 3 = 5`. -/
theorem sopfr_5 : sopfr 5 = 5 :=
  sopfr_eq (l := [5]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 6 = 2 + 3 = 5`. -/
theorem sopfr_6 : sopfr 6 = 5 :=
  sopfr_eq (l := [2, 3]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 7 = 7`. -/
theorem sopfr_7 : sopfr 7 = 7 :=
  sopfr_eq (l := [7]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 77 = 7 + 11 = 18`. -/
theorem sopfr_77 : sopfr 77 = 18 :=
  sopfr_eq (l := [7, 11]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 78 = 2 + 3 + 13 = 18`. -/
theorem sopfr_78 : sopfr 78 = 18 :=
  sopfr_eq (l := [2, 3, 13]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 125 = 5 + 5 + 5 = 15` (125 = 5³). -/
theorem sopfr_125 : sopfr 125 = 15 :=
  sopfr_eq (l := [5, 5, 5]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `sopfr 126 = 2 + 3 + 3 + 7 = 15` (126 = 2·3²·7). -/
theorem sopfr_126 : sopfr 126 = 15 :=
  sopfr_eq (l := [2, 3, 3, 7]) (by norm_num)
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num)

/-- `(5, 6)` is a Ruth–Aaron pair: `sopfr 5 = 5 = sopfr 6`. -/
theorem ruthAaron_5 : RuthAaron 5 := by
  show sopfr 5 = sopfr 6
  rw [sopfr_5, sopfr_6]

/-- `(77, 78)` is a Ruth–Aaron pair: `sopfr 77 = 18 = sopfr 78`. -/
theorem ruthAaron_77 : RuthAaron 77 := by
  show sopfr 77 = sopfr 78
  rw [sopfr_77, sopfr_78]

/-- `(125, 126)` is a Ruth–Aaron pair: `sopfr 125 = 15 = sopfr 126`. -/
theorem ruthAaron_125 : RuthAaron 125 := by
  show sopfr 125 = sopfr 126
  rw [sopfr_125, sopfr_126]

/-- **The namesake.** `(714, 715)` is a Ruth–Aaron pair: `sopfr 714 = 29 = sopfr 715`. -/
theorem ruthAaron_714 : RuthAaron 714 := by
  show sopfr 714 = sopfr 715
  rw [sopfr_714, sopfr_715]

/-! ### A non-example -/

/-- `(6, 7)` is *not* a Ruth–Aaron pair: `sopfr 6 = 5 ≠ 7 = sopfr 7`. -/
theorem not_ruthAaron_6 : ¬ RuthAaron 6 := by
  show ¬ (sopfr 6 = sopfr 7)
  rw [sopfr_6, sopfr_7]
  decide

end Brockian.RuthAaronPairs
