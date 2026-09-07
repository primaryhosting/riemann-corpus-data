/-
  Brockian/CullenWoodall.lean — Cullen numbers `C_n = n·2ⁿ + 1` and Woodall
  numbers `W_n = n·2ⁿ − 1`: concrete primes and composites, elementary structural
  relations, and the OPEN infinitude conjectures (recorded, never asserted).

  It is OPEN whether there are infinitely many Cullen primes, and (separately)
  whether there are infinitely many Woodall primes. This module does NOT resolve
  either question. It:
    - verifies concrete Cullen/Woodall primes (`C₁ = 3`, `W₂ = 7`, `W₃ = 23`,
      `W₆ = 383`) by `norm_num`;
    - verifies concrete composites (`C₂ = 9`, `C₃ = 25`, `W₄ = 63`, `W₅ = 159`);
    - proves elementary structural relations: `C_n = W_n + 2` (n ≥ 1), and that
      both `C_n` and `W_n` are odd for `n ≥ 1`;
    - records `CullenPrimeInfinitude` and `WoodallPrimeInfinitude` as UNPROVEN
      `def`s — statements, not theorems. They are never asserted here.

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (see PORT-QUEUE.md)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C_n = n·2ⁿ + 1`. -/
def cullen  (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- The `n`-th Woodall number `W_n = n·2ⁿ − 1` (truncated ℕ subtraction). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- **OPEN**: there are infinitely many Cullen primes. This is an UNPROVEN `def`
recording the statement — it is never asserted as a theorem here. -/
def CullenPrimeInfinitude  : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ (cullen n).Prime

/-- **OPEN**: there are infinitely many Woodall primes. This is an UNPROVEN `def`
recording the statement — it is never asserted as a theorem here. -/
def WoodallPrimeInfinitude : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ (woodall n).Prime

/-! ## (1) Concrete Cullen / Woodall primes -/

/-- `C₁ = 1·2 + 1 = 3` is prime. -/
theorem cullen_1_prime  : (cullen 1).Prime  := by norm_num [cullen]

/-- `W₂ = 2·4 − 1 = 7` is prime. -/
theorem woodall_2_prime : (woodall 2).Prime := by norm_num [woodall]

/-- `W₃ = 3·8 − 1 = 23` is prime. -/
theorem woodall_3_prime : (woodall 3).Prime := by norm_num [woodall]

/-- `W₆ = 6·64 − 1 = 383` is prime. -/
theorem woodall_6_prime : (woodall 6).Prime := by norm_num [woodall]

/-! ## (2) Concrete Cullen / Woodall composites -/

/-- `C₂ = 2·4 + 1 = 9 = 3·3` is not prime. -/
theorem cullen_2_not_prime  : ¬ (cullen 2).Prime  := by norm_num [cullen]

/-- `C₃ = 3·8 + 1 = 25 = 5·5` is not prime. -/
theorem cullen_3_not_prime  : ¬ (cullen 3).Prime  := by norm_num [cullen]

/-- `W₄ = 4·16 − 1 = 63 = 7·9` is not prime. -/
theorem woodall_4_not_prime : ¬ (woodall 4).Prime := by norm_num [woodall]

/-- `W₅ = 5·32 − 1 = 159 = 3·53` is not prime. -/
theorem woodall_5_not_prime : ¬ (woodall 5).Prime := by norm_num [woodall]

/-! ## (3) Elementary structural relations -/

/-- **Difference-of-two law.** For `n ≥ 1`, the Cullen and Woodall numbers of the
same index differ by exactly `2`: `C_n = W_n + 2`. (For `n ≥ 1` the product
`n·2ⁿ ≥ 1`, so the truncated ℕ subtraction in `W_n` behaves as ordinary
subtraction.) -/
theorem cullen_sub_woodall (n : ℕ) (hn : 1 ≤ n) : cullen n = woodall n + 2 := by
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have h : 1 ≤ n * 2 ^ n :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  unfold cullen woodall
  omega

/-- For `n ≥ 1`, the Cullen number `C_n = n·2ⁿ + 1` is odd (`n·2ⁿ` is even since
`2ⁿ` is even for `n ≥ 1`, and even `+ 1` is odd). -/
theorem cullen_odd {n : ℕ} (hn : 1 ≤ n) : Odd (cullen n) := by
  have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨by decide, by omega⟩
  have hen : Even (n * 2 ^ n) := he.mul_left n
  unfold cullen
  exact hen.add_one

/-- For `n ≥ 1`, the Woodall number `W_n = n·2ⁿ − 1` is odd (`n·2ⁿ` is even and
`≥ 2`, so `n·2ⁿ − 1` is odd). -/
theorem woodall_odd {n : ℕ} (hn : 1 ≤ n) : Odd (woodall n) := by
  have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨by decide, by omega⟩
  have hen : Even (n * 2 ^ n) := he.mul_left n
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hx : 2 ≤ n * 2 ^ n := by
    calc 2 = 1 * 2 := by norm_num
      _ ≤ n * 2 ^ n := Nat.mul_le_mul hn h2n
  obtain ⟨m, hm⟩ := hen
  unfold woodall
  refine ⟨m - 1, ?_⟩
  omega

end Brockian.CullenWoodall
