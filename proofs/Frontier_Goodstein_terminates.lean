import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Ordinal

/-! ## Hereditary base representations -/

lemma pow_log_pos (b x : ℕ) : 0 < b ^ Nat.log b x := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · exact Nat.pow_pos hb

lemma mod_pow_log_lt {x : ℕ} (b : ℕ) (hx : x ≠ 0) : x % b ^ Nat.log b x < x :=
  lt_of_lt_of_le (Nat.mod_lt _ (pow_log_pos b x)) (Nat.pow_log_le_self b hx)

lemma digit_lt {b n : ℕ} (hb : 2 ≤ b) : n / b ^ (Nat.log b n) < b := by
  rw [Nat.div_lt_iff_lt_mul (pow_log_pos b n)]
  calc n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self (b := b) hb n
    _ = b * b ^ Nat.log b n := by ring

lemma one_le_digit {b n : ℕ} (hn : n ≠ 0) : 1 ≤ n / b ^ (Nat.log b n) :=
  (Nat.one_le_div_iff (pow_log_pos b n)).2 (Nat.pow_log_le_self b hn)

/-- `bcNat b b' n` rewrites `n` in hereditary base `b` and replaces every occurrence of the
base `b` by `b'`. -/
def bcNat (b b' : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      b' ^ (bcNat b b' (Nat.log b (n + 1))) * ((n + 1) / b ^ (Nat.log b (n + 1)))
        + bcNat b b' ((n + 1) % b ^ (Nat.log b (n + 1)))
decreasing_by
  · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
  · exact mod_pow_log_lt b (Nat.succ_ne_zero n)

@[simp] lemma bcNat_zero (b b' : ℕ) : bcNat b b' 0 = 0 := by rw [bcNat]

lemma bcNat_eq (b b' : ℕ) {n : ℕ} (hn : n ≠ 0) :
    bcNat b b' n = b' ^ (bcNat b b' (Nat.log b n)) * (n / b ^ (Nat.log b n))
      + bcNat b b' (n % b ^ (Nat.log b n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [bcNat]

lemma bcNat_bnd {b b' : ℕ} (hb : 2 ≤ b) (hbb : b ≤ b') (E : ℕ)
    (hmono : ∀ p q, q ≤ E → p < q → bcNat b b' p < bcNat b b' q) :
    ∀ n, ∀ e ≤ E, n < b ^ e → bcNat b b' n < b' ^ (bcNat b b' e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro e heE hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simpa using Nat.pow_pos (show 0 < b' by omega)
    · obtain ⟨e', he'⟩ : ∃ e', Nat.log b n = e' := ⟨_, rfl⟩
      have he'e : e' < e := he' ▸ Nat.log_lt_of_lt_pow hn0 hn
      have hc : n / b ^ e' < b := he' ▸ digit_lt hb
      have hr : n % b ^ e' < n := he' ▸ mod_pow_log_lt b hn0
      have hrb : n % b ^ e' < b ^ e' := he' ▸ Nat.mod_lt _ (pow_log_pos b n)
      have key : bcNat b b' (n % b ^ e') < b' ^ (bcNat b b' e') :=
        IH _ hr e' (by omega) hrb
      have hneq := bcNat_eq b b' hn0
      rw [he'] at hneq
      rw [hneq]
      calc b' ^ (bcNat b b' e') * (n / b ^ e') + bcNat b b' (n % b ^ e')
          < b' ^ (bcNat b b' e') * (n / b ^ e') + b' ^ (bcNat b b' e') := by omega
        _ = b' ^ (bcNat b b' e') * (n / b ^ e' + 1) := by ring
        _ ≤ b' ^ (bcNat b b' e') * b' := Nat.mul_le_mul_left _ (by omega)
        _ = b' ^ (bcNat b b' e' + 1) := by ring
        _ ≤ b' ^ (bcNat b b' e) := Nat.pow_le_pow_right (by omega)
              (by have := hmono e' e heE he'e; omega)

lemma bcNat_strictMono {b b' : ℕ} (hb : 2 ≤ b) (hbb : b ≤ b') :
    ∀ m n, n < m → bcNat b b' n < bcNat b b' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro n hnm
    have hm0 : m ≠ 0 := by omega
    obtain ⟨E, hE⟩ : ∃ E, Nat.log b m = E := ⟨_, rfl⟩
    have hEm : E < m := hE ▸ Nat.log_lt_self b hm0
    have hmonoE : ∀ p q, q ≤ E → p < q → bcNat b b' p < bcNat b b' q :=
      fun p q hq hpq => IH q (by omega) p hpq
    have hbndE := bcNat_bnd hb hbb E hmonoE
    have hC : 1 ≤ m / b ^ E := hE ▸ one_le_digit hm0
    have hRb : m % b ^ E < b ^ E := hE ▸ Nat.mod_lt _ (pow_log_pos b m)
    have hRm : m % b ^ E < m := hE ▸ mod_pow_log_lt b hm0
    have hmeq := bcNat_eq b b' hm0
    rw [hE] at hmeq
    have hppos : 0 < b' ^ (bcNat b b' E) := Nat.pow_pos (by omega)
    have hmpos : 0 < b' ^ (bcNat b b' E) * (m / b ^ E) := Nat.mul_pos hppos (by omega)
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [hmeq, bcNat_zero]
      omega
    · obtain ⟨e, he⟩ : ∃ e, Nat.log b n = e := ⟨_, rfl⟩
      have hlog : e ≤ E := by rw [← he, ← hE]; exact Nat.log_mono_right (le_of_lt hnm)
      have hneq := bcNat_eq b b' hn0
      rw [he] at hneq
      have hrb : n % b ^ e < b ^ e := he ▸ Nat.mod_lt _ (pow_log_pos b n)
      have hrn : n % b ^ e < n := he ▸ mod_pow_log_lt b hn0
      have hcb : n / b ^ e < b := he ▸ digit_lt hb
      have hbndr : bcNat b b' (n % b ^ e) < b' ^ (bcNat b b' e) := hbndE _ e hlog hrb
      rcases lt_or_eq_of_le hlog with hlt | heq
      · have hnE : n < b ^ E := by
          refine lt_of_lt_of_le (Nat.lt_pow_succ_log_self hb n) ?_
          exact Nat.pow_le_pow_right (by omega) (by omega)
        have h1 : bcNat b b' n < b' ^ (bcNat b b' E) := hbndE _ E le_rfl hnE
        have h2 : b' ^ (bcNat b b' E) * 1 ≤ b' ^ (bcNat b b' E) * (m / b ^ E) :=
          Nat.mul_le_mul_left _ hC
        omega
      · subst heq
        have hbndR : bcNat b b' (m % b ^ e) < b' ^ (bcNat b b' e) := hbndE _ e le_rfl hRb
        have hnd : b ^ e * (n / b ^ e) + n % b ^ e = n := Nat.div_add_mod n (b ^ e)
        have hmd : b ^ e * (m / b ^ e) + m % b ^ e = m := Nat.div_add_mod m (b ^ e)
        rcases lt_trichotomy (n / b ^ e) (m / b ^ e) with hlt | heq2 | hgt
        · have h1 : b' ^ (bcNat b b' e) * (n / b ^ e + 1)
              ≤ b' ^ (bcNat b b' e) * (m / b ^ e) := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_add, Nat.mul_one] at h1
          rw [hneq, hmeq]
          omega
        · rw [hneq, hmeq, heq2]
          have hrr : n % b ^ e < m % b ^ e := by rw [heq2] at hnd; omega
          have hlast : bcNat b b' (n % b ^ e) < bcNat b b' (m % b ^ e) := IH _ hRm _ hrr
          omega
        · exfalso
          have hlt2 : m < n := by
            calc m = b ^ e * (m / b ^ e) + m % b ^ e := hmd.symm
              _ < b ^ e * (m / b ^ e) + b ^ e := by omega
              _ = b ^ e * (m / b ^ e + 1) := by ring
              _ ≤ b ^ e * (n / b ^ e) := Nat.mul_le_mul_left _ (by omega)
              _ ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self n (b ^ e)
          omega

end Frontier

