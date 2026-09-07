/-
  Brockian/PerfectTotient.lean — perfect totient numbers and the OPEN infinitude.

  A *perfect totient number* `n` satisfies
      n = φ(n) + φ(φ(n)) + φ(φ(φ(n))) + … + 1,
  the sum of its iterated Euler totients, taken until the iteration reaches `1`.
  The first few are 3, 9, 15, 27, 39, 81, 111, 183, 243, …  (the powers of 3
  are all perfect totient). Whether there are INFINITELY MANY perfect totient
  numbers is an OPEN problem; we record the statement as an unproven `def`
  (`PerfectTotientInfinitude`) and NEVER assert it.

  This module verifies concrete instances only. Each `PerfectTotient k` reduces to
  a decidable equality over `Nat.totient` (computable) and closes by `decide`.

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (remote AXLE is)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0

  Register: COMPUTATION (finite decidable checks of φ-iteration identities).
  The infinitude is a CONJECTURE and is NOT proved.
-/
import Mathlib

namespace Brockian.PerfectTotient

/-- Sum of the iterated Euler totients of `m`, until reaching `1` (fuel-bounded;
`fuel = m` suffices since `φ` strictly decreases below any `m > 1`). -/
def totientSumAux : ℕ → ℕ → ℕ
  | 0,        _ => 0
  | (fuel+1), m => if m ≤ 1 then 0 else Nat.totient m + totientSumAux fuel (Nat.totient m)

/-- `φ(n) + φ(φ(n)) + … + 1`. -/
def iteratedTotientSum (n : ℕ) : ℕ := totientSumAux n n

/-- `n` is a *perfect totient number*: the iterated-totient sum equals `n`. -/
def PerfectTotient (n : ℕ) : Prop := 1 < n ∧ iteratedTotientSum n = n

/-- **OPEN.** There are infinitely many perfect totient numbers. This is an
unproven `def` recording the conjecture; it is NEVER asserted or resolved here. -/
def PerfectTotientInfinitude : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ PerfectTotient n

/-! ### Concrete perfect totient numbers (flagship, all by decidable `φ`-iteration) -/

/-- `3` is perfect totient: φ(3)=2, φ(2)=1 → 2+1 = 3. -/
theorem pt_3 : PerfectTotient 3 := by unfold PerfectTotient; decide

/-- `9` is perfect totient: 6+2+1 = 9. -/
theorem pt_9 : PerfectTotient 9 := by unfold PerfectTotient; decide

/-- `15` is perfect totient: 8+4+2+1 = 15. -/
theorem pt_15 : PerfectTotient 15 := by unfold PerfectTotient; decide

/-- `27` is perfect totient: 18+6+2+1 = 27. -/
theorem pt_27 : PerfectTotient 27 := by unfold PerfectTotient; decide

/-- `39` is perfect totient: 24+8+4+2+1 = 39. -/
theorem pt_39 : PerfectTotient 39 := by unfold PerfectTotient; decide

set_option maxRecDepth 4000 in
/-- `81` is perfect totient: 54+18+6+2+1 = 81 (a power of 3). -/
theorem pt_81 : PerfectTotient 81 := by unfold PerfectTotient; decide

set_option maxRecDepth 4000 in
/-- `111` is perfect totient: 72+24+8+4+2+1 = 111. -/
theorem pt_111 : PerfectTotient 111 := by unfold PerfectTotient; decide

set_option maxRecDepth 4000 in
/-- `183` is perfect totient: 120+32+16+8+4+2+1 = 183. -/
theorem pt_183 : PerfectTotient 183 := by unfold PerfectTotient; decide

/-! ### Bonus — powers of 3 pattern: 3, 9, 27, 81, 243 = 3^1..3^5 are all perfect totient -/

set_option maxRecDepth 8000 in
/-- `243 = 3^5` is perfect totient: 162+54+18+6+2+1 = 243. -/
theorem pt_243 : PerfectTotient 243 := by unfold PerfectTotient; decide

/-! ### Bonus — a non-example -/

/-- `4` is NOT perfect totient: φ(4)=2, φ(2)=1 → 2+1 = 3 ≠ 4. -/
theorem not_pt_4 : ¬ PerfectTotient 4 := by unfold PerfectTotient; decide

end Brockian.PerfectTotient
