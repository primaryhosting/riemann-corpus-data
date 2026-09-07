/-
  Brockian/AndricaConjecture.lean — Andrica's conjecture: concrete instances,
  the OPEN conjecture (recorded, never asserted), and the integer↔√ bridge.

  Andrica's conjecture (OPEN, due to Dorin Andrica, 1986): for consecutive primes
  pₙ < pₙ₊₁ one has  √pₙ₊₁ − √pₙ < 1.  Writing the gap g = pₙ₊₁ − pₙ ≥ 1, this is
  equivalent to the purely integer inequality  (g − 1)² < 4·pₙ, which is
  decide-checkable and avoids `Real.sqrt` entirely.

  This module does NOT resolve Andrica's conjecture — it remains open. We:
    1. verify the integer inequality on concrete consecutive-prime pairs (flagship),
    2. record the conjecture as an unproven `def` (never asserted as a theorem),
    3. prove the honest bridge `AndricaInt ↔ (√q − √p < 1)` (the classical form).

  Verification (spec §2A triple verification):
    - local `lake build`  : see PORT-QUEUE.md
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.AndricaConjecture

/-- `p, q` are consecutive primes: both prime, `p < q`, and no prime strictly
between them. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

/-- Andrica's inequality in integer form: `(q − p − 1)² < 4·p`. For consecutive
primes with gap `g = q − p`, this is `(g − 1)² < 4·p`, equivalent to
`√q − √p < 1` (see `andricaInt_iff_sqrt`). -/
def AndricaInt (p q : ℕ) : Prop := (q - p - 1) ^ 2 < 4 * p

/-- **Andrica's conjecture (OPEN).** The integer inequality holds for *all*
consecutive primes. This is an unproven `def` — it is recorded here, NOT asserted
as a theorem. No result in this file proves it. -/
def AndricaConjecture : Prop := ∀ p q : ℕ, ConsecutivePrimes p q → AndricaInt p q

/-! ### (1) Flagship: concrete consecutive-prime Andrica instances -/

/-- Andrica at the pair `(2, 3)` — gap 2, `(2−1)²=1`? no: `(3−2−1)²=0 < 8`. -/
theorem andrica_2_3 : ConsecutivePrimes 2 3 ∧ AndricaInt 2 3 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by unfold AndricaInt; decide⟩
  intro r hr hr'
  interval_cases r <;> norm_num

/-- Andrica at the pair `(7, 11)` — gap 4, `(11−7−1)²=9 < 28`. -/
theorem andrica_7_11 : ConsecutivePrimes 7 11 ∧ AndricaInt 7 11 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by unfold AndricaInt; decide⟩
  intro r hr hr'
  interval_cases r <;> norm_num

/-- Andrica at the pair `(23, 29)` — gap 6, `(29−23−1)²=25 < 92`. -/
theorem andrica_23_29 : ConsecutivePrimes 23 29 ∧ AndricaInt 23 29 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by unfold AndricaInt; decide⟩
  intro r hr hr'
  interval_cases r <;> norm_num

/-- Andrica at the pair `(89, 97)` — gap 8, `(97−89−1)²=49 < 356`. -/
theorem andrica_89_97 : ConsecutivePrimes 89 97 ∧ AndricaInt 89 97 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by unfold AndricaInt; decide⟩
  intro r hr hr'
  interval_cases r <;> norm_num

/-- Andrica at the pair `(113, 127)` — gap 14 (widest small prime gap here),
`(127−113−1)²=169 < 452`. This is the stress case for the "no prime between"
obligation (13 composites 114..126). -/
theorem andrica_113_127 : ConsecutivePrimes 113 127 ∧ AndricaInt 113 127 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by unfold AndricaInt; decide⟩
  intro r hr hr'
  interval_cases r <;> norm_num

/-! ### (2) Bonus: the integer ↔ √ bridge (the classical statement) -/

/-- **The honest bridge.** For `0 < p` and `p < q`, the integer inequality
`AndricaInt p q` is *equivalent* to the classical Andrica inequality
`√q − √p < 1`. This makes the decide-checkable form (1) faithful to the
conjecture as stated over the reals. -/
theorem andricaInt_iff_sqrt {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    AndricaInt p q ↔ Real.sqrt q - Real.sqrt p < 1 := by
  have hpq' : p ≤ q := le_of_lt hpq
  have h1 : 1 ≤ q - p := by omega
  have hpR : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hsp : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hspp : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hpR
  -- cast of the ℕ triple subtraction into a genuine ℝ subtraction
  have hcast : ((q - p - 1 : ℕ) : ℝ) = (q : ℝ) - (p : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_sub hpq', Nat.cast_one]
  -- 2·√p = √(4p)
  have h4p : Real.sqrt (4 * (p : ℝ)) = 2 * Real.sqrt p := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  -- (1 + √p)² = 1 + 2√p + p
  have hsq : (1 + Real.sqrt p) ^ 2 = 1 + 2 * Real.sqrt p + (p : ℝ) := by
    rw [add_sq, hspp]; ring
  -- integer inequality ↔ the cast real inequality
  have hstep0 : AndricaInt p q ↔ ((q - p - 1 : ℕ) : ℝ) ^ 2 < 4 * (p : ℝ) := by
    unfold AndricaInt
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  calc
    AndricaInt p q
        ↔ ((q - p - 1 : ℕ) : ℝ) ^ 2 < 4 * (p : ℝ) := hstep0
    _ ↔ ((q - p - 1 : ℕ) : ℝ) < Real.sqrt (4 * (p : ℝ)) :=
        (Real.lt_sqrt (Nat.cast_nonneg _)).symm
    _ ↔ ((q - p - 1 : ℕ) : ℝ) < 2 * Real.sqrt p := by rw [h4p]
    _ ↔ (q : ℝ) - (p : ℝ) - 1 < 2 * Real.sqrt p := by rw [hcast]
    _ ↔ (q : ℝ) < 1 + 2 * Real.sqrt p + (p : ℝ) := by
        constructor <;> intro h <;> linarith
    _ ↔ (q : ℝ) < (1 + Real.sqrt p) ^ 2 := by rw [hsq]
    _ ↔ Real.sqrt q < 1 + Real.sqrt p := (Real.sqrt_lt' (by positivity)).symm
    _ ↔ Real.sqrt q - Real.sqrt p < 1 := by
        constructor <;> intro h <;> linarith

end Brockian.AndricaConjecture
