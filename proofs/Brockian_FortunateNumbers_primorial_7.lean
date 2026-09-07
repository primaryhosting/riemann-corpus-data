/-
  Brockian/FortunateNumbers.lean — FORTUNATE NUMBERS & FORTUNE'S CONJECTURE.

  For a primorial P (the product of the first primes), the *Fortunate number*
  is the smallest m > 1 for which P + m is prime. Reo Fortune conjectured
  (still OPEN) that every Fortunate number is prime.

  This module records CONCRETE, machine-checked instances:

    P =   2  →  m = 3    (2 + 3   = 5   prime; 2 + 2 = 4   composite)
    P =   6  →  m = 5    (6 + 5   = 11  prime; 6 + {2,3,4}   = 8,9,10   composite)
    P =  30  →  m = 7    (30 + 7  = 37  prime; 30 + {2..6}   = 32..36   composite)
    P = 210  →  m = 13   (210 + 13 = 223 prime; 210 + {2..12} = 212..222 composite)

  The four bases 2, 6, 30, 210 are exactly Mathlib's `primorial` at 2, 3, 5, 7
  (identities recorded below). Each of the four Fortunate numbers 3, 5, 7, 13
  is prime — the small-case evidence FOR Fortune's conjecture.

  Fortune's conjecture itself is stored as an UNPROVEN `def` (`FortuneConjecture`).
  It is never asserted or proved here: it remains open.

  Mathlib note: the primorial lives at the ROOT namespace as `primorial`
  (`primorial n = ∏ p ∈ Finset.range (n+1) with p.Prime, p`); there is no
  `Nat.primorial`. So `primorial 2 = 2`, `primorial 3 = 6`, `primorial 5 = 30`,
  `primorial 7 = 210`.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.FortunateNumbers

/-- `m` is the Fortunate number for base `P`: the smallest integer `> 1` with
`P + m` prime. -/
def FortunateFor (P m : ℕ) : Prop :=
  1 < m ∧ (P + m).Prime ∧ ∀ k : ℕ, 1 < k → k < m → ¬ (P + k).Prime

/-- Fortune's conjecture (OPEN): every Fortunate number, taken over a primorial
base `P = primorial n`, is prime. Recorded as an UNPROVEN `def` — never asserted,
never proved. -/
def FortuneConjecture : Prop :=
  ∀ n P m : ℕ, P = primorial n → FortunateFor P m → m.Prime

/-! ### (1) Flagship — concrete Fortunate numbers -/

/-- `P = 2`: the Fortunate number is `3` (`2+3 = 5` prime, `2+2 = 4` composite). -/
theorem fortunate_2 : FortunateFor 2 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-- `P = 6`: the Fortunate number is `5` (`6+5 = 11` prime, `6+{2,3,4}` composite). -/
theorem fortunate_6 : FortunateFor 6 5 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-- `P = 30`: the Fortunate number is `7` (`30+7 = 37` prime, `30+{2..6}` composite). -/
theorem fortunate_30 : FortunateFor 30 7 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-- `P = 210`: the Fortunate number is `13` (`210+13 = 223` prime,
`210+{2..12} = 212..222` all composite). -/
theorem fortunate_210 : FortunateFor 210 13 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-! ### (2) The Fortunate numbers are prime (Fortune's conjecture, small cases) -/

/-- Each concrete Fortunate number `3, 5, 7, 13` is prime — the evidence for
Fortune's conjecture in the recorded cases. -/
theorem fortunate_values_prime :
    (3 : ℕ).Prime ∧ (5 : ℕ).Prime ∧ (7 : ℕ).Prime ∧ (13 : ℕ).Prime := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ### (3) Primorial identities — tie the bases to Mathlib's `primorial` -/

/-- `primorial 2 = 2`. -/
theorem primorial_2 : primorial 2 = 2 := by decide

/-- `primorial 3 = 6`. -/
theorem primorial_3 : primorial 3 = 6 := by decide

/-- `primorial 5 = 30`. -/
theorem primorial_5 : primorial 5 = 30 := by decide

/-- `primorial 7 = 210`. -/
theorem primorial_7 : primorial 7 = 210 := by decide

end Brockian.FortunateNumbers
