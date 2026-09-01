/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- `noDivLe n k` is `true` when no `d` with `2 ≤ d ≤ k` and `d * d ≤ n` divides `n`. -/
def noDivLe (n : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (d + 2) => (decide (n < (d + 2) * (d + 2)) || n % (d + 2) != 0) && noDivLe n (d + 1)

/-- A kernel-friendly primality test; it is correct for `n ≤ 1520`. -/
def isPrimeB (n : Nat) : Bool := decide (2 ≤ n) && noDivLe n 38

theorem noDivLe_spec :
    ∀ (k n d : Nat), noDivLe n k = true → 2 ≤ d → d ≤ k → d * d ≤ n → ¬ d ∣ n := by
  intro k
  induction k with
  | zero => intro n d _ h2 hd _; omega
  | succ k ih =>
    match k with
    | 0 => intro n d _ h2 hd _; omega
    | (k' + 1) =>
      intro n d h h2 hd hdd
      rw [noDivLe, Bool.and_eq_true] at h
      obtain ⟨h1, h2'⟩ := h
      by_cases hd' : d ≤ k' + 1
      · exact ih n d h2' h2 hd' hdd
      · have hde : d = k' + 2 := by omega
        subst hde
        rcases Bool.or_eq_true _ _ |>.mp h1 with hlt | hmod
        · exact absurd (of_decide_eq_true hlt) (by omega)
        · have hmod' : n % (k' + 2) ≠ 0 := by simpa using hmod
          rintro ⟨c, rfl⟩
          exact hmod' (Nat.mul_mod_right (k' + 2) c)

theorem isPrimeB_two_le {n : Nat} (h : isPrimeB n = true) : 2 ≤ n := by
  rw [isPrimeB, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- Correctness of the fast primality test in the range where it is used. -/
theorem isPrimeB_isPrime {n : Nat} (hn : n ≤ 1520) (h : isPrimeB n = true) : IsPrime n := by
  rw [isPrimeB, Bool.and_eq_true] at h
  obtain ⟨h2, hnd⟩ := h
  have h2 : 2 ≤ n := of_decide_eq_true h2
  refine ⟨h2, fun d hd => ?_⟩
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  by_cases hdn : d = n
  · exact Or.inr hdn
  exfalso
  obtain ⟨e, he⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; simp at he; omega
  have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) ⟨e, he⟩
  have hcomm : n = e * d := by rw [he, Nat.mul_comm]
  have hele : e ≤ n := Nat.le_of_dvd (by omega) ⟨d, hcomm⟩
  -- the smaller of the two cofactors is at most 38, and divides `n`
  rcases Nat.le_total d e with hle | hle
  · have hdd : d * d ≤ n := by
      calc d * d ≤ d * e := Nat.mul_le_mul_left d hle
        _ = n := he.symm
    have hd38 : d ≤ 38 := by
      by_cases hc : d ≤ 38
      · exact hc
      · have : 39 * 39 ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
        omega
    exact noDivLe_spec 38 n d hnd (by omega) hd38 hdd ⟨e, he⟩
  · have hee : e * e ≤ n := by
      calc e * e ≤ d * e := Nat.mul_le_mul_right e hle
        _ = n := he.symm
    have he38 : e ≤ 38 := by
      by_cases hc : e ≤ 38
      · exact hc
      · have : 39 * 39 ≤ e * e := Nat.mul_le_mul (by omega) (by omega)
        omega
    have he1 : e ≠ 1 := by rintro rfl; omega
    exact noDivLe_spec 38 n e hnd (by omega) he38 hee ⟨d, hcomm⟩

/-- The wheel: a fixed 12-element list of primes. For every even `n` with `4 ≤ n ≤ 2 * 727`,
one of the two Goldbach summands of `n` can be taken from this list. -/
def goldbachWheelK2 : List Nat := [2, 3, 5, 7, 17, 19, 43, 101, 127, 149, 167, 181]

/-- `wheelOk m` tests that `2 * m = p + q` for some wheel prime `p` and some prime `q`. -/
def wheelOk (m : Nat) : Bool :=
  goldbachWheelK2.any (fun p => isPrimeB p && isPrimeB (2 * m - p))

/-- `checkAll k` tests `wheelOk m` for all `2 ≤ m ≤ k`. -/
def checkAll : Nat → Bool
  | 0 => true
  | 1 => true
  | (m + 2) => wheelOk (m + 2) && checkAll (m + 1)

theorem checkAll_spec :
    ∀ (k m : Nat), checkAll k = true → 2 ≤ m → m ≤ k → wheelOk m = true := by
  intro k
  induction k with
  | zero => intro m _ h2 hm; omega
  | succ k ih =>
    match k with
    | 0 => intro m _ h2 hm; omega
    | (k' + 1) =>
      intro m h h2 hm
      rw [checkAll, Bool.and_eq_true] at h
      by_cases hm' : m ≤ k' + 1
      · exact ih m h.2 h2 hm'
      · have hme : m = k' + 2 := by omega
        subst hme
        exact h.1

/-- The finite verification, checked by kernel reduction. -/
theorem checkAll_727 : checkAll 727 = true := by decide

theorem wheel_le_181 : ∀ p ∈ goldbachWheelK2, p ≤ 181 := by
  intro p hp
  have h : goldbachWheelK2.all (fun p => decide (p ≤ 181)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

/-- **Goldbach wheel, K = 2, modulus 727.**
Every even `n` with `4 ≤ n ≤ 2 * 727 = 1454` is a sum of two primes, one of which lies in the
fixed 12-element wheel `Brockian.goldbachWheelK2`. -/
theorem GoldbachWheelK2_727 :
    ∀ n : Nat, n % 2 = 0 → 4 ≤ n → n ≤ 2 * 727 →
      ∃ p q : Nat, p ∈ goldbachWheelK2 ∧ IsPrime p ∧ IsPrime q ∧ p + q = n := by
  intro n hn h4 hle
  have hm : wheelOk (n / 2) = true :=
    checkAll_spec 727 (n / 2) checkAll_727 (by omega) (by omega)
  obtain ⟨p, hp, hpb⟩ := List.any_eq_true.mp hm
  rw [Bool.and_eq_true] at hpb
  obtain ⟨hp1, hp2⟩ := hpb
  have hple : p ≤ 181 := wheel_le_181 p hp
  have hn2 : 2 * (n / 2) = n := by omega
  rw [hn2] at hp2
  have hq2 : 2 ≤ n - p := isPrimeB_two_le hp2
  exact ⟨p, n - p, hp, isPrimeB_isPrime (by omega) hp1, isPrimeB_isPrime (by omega) hp2, by omega⟩

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in
`RequestProject/GoldbachWheelK2_727.lean`, which is deliberately import-free (Lean requires
`import` lines to precede every other command, so the mandated header comment can only be the
first thing in a file that has no imports).

Here we connect the elementary primality predicate `Brockian.IsPrime` used there with Mathlib's
`Nat.Prime`, and restate the result in Mathlib's vocabulary.
-/

set_option maxHeartbeats 1000000

namespace Brockian

/-- `Brockian.IsPrime` agrees with Mathlib's `Nat.Prime`. -/
theorem isPrime_iff_nat_prime (p : ℕ) : IsPrime p ↔ Nat.Prime p :=
  Nat.prime_def.symm

/-- **Goldbach wheel, K = 2, modulus 727**, phrased with Mathlib's `Even` and `Nat.Prime`:
every even `n` with `4 ≤ n ≤ 2 * 727` is a sum of two primes, one of which lies in the fixed
12-element wheel `Brockian.goldbachWheelK2`. -/
theorem GoldbachWheelK2_727_mathlib :
    ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 727 →
      ∃ p q : ℕ, p ∈ goldbachWheelK2 ∧ Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n hn h4 hle
  obtain ⟨p, q, hp, hpp, hqp, hsum⟩ :=
    GoldbachWheelK2_727 n (Nat.even_iff.mp hn) h4 hle
  exact ⟨p, q, hp, (isPrime_iff_nat_prime p).mp hpp, (isPrime_iff_nat_prime q).mp hqp, hsum⟩

/-- Every entry of the wheel really is prime. -/
theorem goldbachWheelK2_prime : ∀ p ∈ goldbachWheelK2, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

end Brockian

