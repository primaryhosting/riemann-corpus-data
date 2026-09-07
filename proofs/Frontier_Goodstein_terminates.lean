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

/-! ### Arithmetic preliminaries -/

theorem nat_pow_log_pos (b n : ℕ) : 0 < b ^ Nat.log b n := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [Nat.log_of_left_le_one]
  · exact Nat.pow_pos hb

theorem nat_mod_pow_log_lt (b n : ℕ) (hn : n ≠ 0) : n % b ^ Nat.log b n < n :=
  lt_of_lt_of_le (Nat.mod_lt _ (nat_pow_log_pos b n)) (Nat.pow_log_le_self b hn)

/-- The leading digit of `n` in base `b` is positive. -/
theorem nat_div_pow_log_pos (b n : ℕ) (hn : n ≠ 0) : 0 < n / b ^ Nat.log b n :=
  Nat.div_pos (Nat.pow_log_le_self b hn) (nat_pow_log_pos b n)

/-- The leading digit of `n` in base `b` is less than `b`. -/
theorem nat_div_pow_log_lt (b n : ℕ) (hb : 2 ≤ b) : n / b ^ Nat.log b n < b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using lt_of_lt_of_le Nat.zero_lt_two hb
  · have h := Nat.lt_pow_succ_log_self (b := b) hb n
    rw [Nat.div_lt_iff_lt_mul (nat_pow_log_pos b n)]
    simpa [pow_succ, Nat.mul_comm] using h

/-- Uniqueness of the base-`c` decomposition, in the form we need. -/
theorem nat_decomp (c e q s : ℕ) (hc : 2 ≤ c) (hq0 : 0 < q) (hqc : q < c) (hs : s < c ^ e) :
    Nat.log c (c ^ e * q + s) = e ∧ (c ^ e * q + s) / c ^ e = q ∧ (c ^ e * q + s) % c ^ e = s := by
  have hce : 0 < c ^ e := Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_two hc)
  have hdiv : (c ^ e * q + s) / c ^ e = q := by
    rw [Nat.mul_add_div hce, Nat.div_eq_of_lt hs, Nat.add_zero]
  have hmod : (c ^ e * q + s) % c ^ e = s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  refine ⟨?_, hdiv, hmod⟩
  have hlow : c ^ e ≤ c ^ e * q + s := le_trans (Nat.le_mul_of_pos_right _ hq0) (Nat.le_add_right _ _)
  have hhigh : c ^ e * q + s < c ^ (e + 1) := by
    have : c ^ e * q + s < c ^ e * q + c ^ e := by omega
    calc c ^ e * q + s < c ^ e * q + c ^ e := this
      _ = c ^ e * (q + 1) := by ring
      _ ≤ c ^ e * c := Nat.mul_le_mul_left _ hqc
      _ = c ^ (e + 1) := by ring
  exact Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh

/-- Casting a natural power into the ordinals. -/
theorem natCast_pow_ord (m k : ℕ) : ((m ^ k : ℕ) : Ordinal) = (m : Ordinal) ^ (k : Ordinal) := by
  induction k with
  | zero => simp
  | succ j ih =>
      have h : ((j + 1 : ℕ) : Ordinal) = (j : Ordinal) + 1 := by push_cast; rfl
      rw [pow_succ, Ordinal.natCast_mul, ih, h, opow_add, opow_one]

/-! ### The ordinal (and natural) evaluation of hereditary base-`b` representations -/

/-- `Gv b w n` is the value of the hereditary base-`b` representation of `n`,
with the base `b` replaced by the ordinal `w`. -/
noncomputable def Gv (b : ℕ) (w : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | (n + 1) =>
      w ^ (Gv b w (Nat.log b (n + 1))) * ((n + 1) / b ^ Nat.log b (n + 1) : ℕ)
        + Gv b w ((n + 1) % b ^ Nat.log b (n + 1))
  decreasing_by
    · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
    · exact nat_mod_pow_log_lt b (n + 1) (Nat.succ_ne_zero n)

theorem Gv_def (b : ℕ) (w : Ordinal) (n : ℕ) (hn : n ≠ 0) :
    Gv b w n = w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
      + Gv b w (n % b ^ Nat.log b n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Gv]

@[simp] theorem Gv_zero (b : ℕ) (w : Ordinal) : Gv b w 0 = 0 := by rw [Gv]

theorem Gv_pos (b : ℕ) (w : Ordinal) (hw : 0 < w) (n : ℕ) (hn : n ≠ 0) : 0 < Gv b w n := by
  rw [Gv_def b w n hn]
  have h1 : (0 : Ordinal) < w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ)) := by
    apply mul_pos (opow_pos _ hw)
    exact_mod_cast nat_div_pow_log_pos b n hn
  exact lt_of_lt_of_le h1 le_self_add

/-- The main structural lemma: `Gv b w` is strictly monotone, and sends numbers below `b ^ k`
to ordinals below `w ^ (Gv b w k)`. -/
theorem Gv_key_and_mono (b : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hw : (b : Ordinal) ≤ w) (n : ℕ) :
    (∀ k : ℕ, n < b ^ k → Gv b w n < w ^ (Gv b w k)) ∧
      (∀ m : ℕ, n < m → Gv b w n < Gv b w m) := by
  have hb0 : 0 < b := by omega
  have hwpos : (0 : Ordinal) < w := lt_of_lt_of_le (by exact_mod_cast hb0) hw
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have key : ∀ k : ℕ, n < b ^ k → Gv b w n < w ^ (Gv b w k) := by
      intro k hk
      rcases eq_or_ne n 0 with rfl | hn
      · simpa using opow_pos (Gv b w k) hwpos
      · have hLn : Nat.log b n < n := Nat.log_lt_self b hn
        have hrn : n % b ^ Nat.log b n < n := nat_mod_pow_log_lt b n hn
        have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (nat_pow_log_pos b n)
        have hqb : n / b ^ Nat.log b n < b := nat_div_pow_log_lt b n hb
        have hLk : Nat.log b n < k := by
          have h1 : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
          exact (Nat.pow_lt_pow_iff_right hb).mp (lt_of_le_of_lt h1 hk)
        have hGLk : Gv b w (Nat.log b n) < Gv b w k := (IH _ hLn).2 k hLk
        have hGr : Gv b w (n % b ^ Nat.log b n) < w ^ (Gv b w (Nat.log b n)) :=
          (IH _ hrn).1 (Nat.log b n) hrb
        calc Gv b w n
            = w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
                + Gv b w (n % b ^ Nat.log b n) := Gv_def b w n hn
          _ < w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
                + w ^ (Gv b w (Nat.log b n)) := add_lt_add_right hGr _
          _ = w ^ (Gv b w (Nat.log b n)) * (((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1) := by
                rw [mul_add, mul_one]
          _ ≤ w ^ (Gv b w (Nat.log b n)) * w := by
                apply mul_le_mul_right
                have h2 : ((n / b ^ Nat.log b n : ℕ) + 1 : ℕ) ≤ b := hqb
                calc ((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1
                    = (((n / b ^ Nat.log b n : ℕ) + 1 : ℕ) : Ordinal) := by push_cast; rfl
                  _ ≤ (b : Ordinal) := by exact_mod_cast h2
                  _ ≤ w := hw
          _ = w ^ (Gv b w (Nat.log b n) + 1) := by rw [opow_add, opow_one]
          _ ≤ w ^ (Gv b w k) := opow_le_opow_right hwpos (Order.add_one_le_of_lt hGLk)
    refine ⟨key, ?_⟩
    intro m hnm
    have hm : m ≠ 0 := by omega
    have hGm : Gv b w m = w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ))
        + Gv b w (m % b ^ Nat.log b m) := Gv_def b w m hm
    have hqm0 : 0 < m / b ^ Nat.log b m := nat_div_pow_log_pos b m hm
    have hbase : w ^ (Gv b w (Nat.log b m)) ≤ Gv b w m := by
      rw [hGm]
      calc w ^ (Gv b w (Nat.log b m)) = w ^ (Gv b w (Nat.log b m)) * 1 := (mul_one _).symm
        _ ≤ w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ)) := by
              apply mul_le_mul_right
              exact_mod_cast hqm0
        _ ≤ _ := le_self_add
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using Gv_pos b w hwpos m hm
    · have hLM : Nat.log b n ≤ Nat.log b m := Nat.log_mono_right (le_of_lt hnm)
      rcases lt_or_eq_of_le hLM with hlt | heq
      · have hnlt : n < b ^ Nat.log b m :=
          lt_of_lt_of_le (Nat.lt_pow_succ_log_self hb n) (Nat.pow_le_pow_right hb0 hlt)
        exact lt_of_lt_of_le (key _ hnlt) hbase
      · have hrn : n % b ^ Nat.log b n < n := nat_mod_pow_log_lt b n hn
        have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (nat_pow_log_pos b n)
        have hGr : Gv b w (n % b ^ Nat.log b n) < w ^ (Gv b w (Nat.log b n)) :=
          (IH _ hrn).1 (Nat.log b n) hrb
        have hGn : Gv b w n = w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
            + Gv b w (n % b ^ Nat.log b n) := Gv_def b w n hn
        have hdn := Nat.div_add_mod n (b ^ Nat.log b n)
        rw [heq] at hrn hrb hGr hGn hdn
        have hdm := Nat.div_add_mod m (b ^ Nat.log b m)
        have hqle : n / b ^ Nat.log b m ≤ m / b ^ Nat.log b m :=
          Nat.div_le_div_right (le_of_lt hnm)
        rcases lt_or_eq_of_le hqle with hq | hq
        · calc Gv b w n
              = w ^ (Gv b w (Nat.log b m)) * ((n / b ^ Nat.log b m : ℕ))
                  + Gv b w (n % b ^ Nat.log b m) := hGn
            _ < w ^ (Gv b w (Nat.log b m)) * ((n / b ^ Nat.log b m : ℕ))
                  + w ^ (Gv b w (Nat.log b m)) := add_lt_add_right hGr _
            _ = w ^ (Gv b w (Nat.log b m)) * (((n / b ^ Nat.log b m : ℕ) : Ordinal) + 1) := by
                  rw [mul_add, mul_one]
            _ ≤ w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ)) := by
                  apply mul_le_mul_right
                  have h3 : ((n / b ^ Nat.log b m : ℕ) + 1 : ℕ) ≤ m / b ^ Nat.log b m := hq
                  calc ((n / b ^ Nat.log b m : ℕ) : Ordinal) + 1
                      = (((n / b ^ Nat.log b m : ℕ) + 1 : ℕ) : Ordinal) := by push_cast; rfl
                    _ ≤ _ := by exact_mod_cast h3
            _ ≤ Gv b w m := by rw [hGm]; exact le_self_add
        · have hrlt : n % b ^ Nat.log b m < m % b ^ Nat.log b m := by
            refine lt_of_add_lt_add_left (a := b ^ Nat.log b m * (m / b ^ Nat.log b m)) ?_
            rw [hdm, ← hq, hdn]
            exact hnm
          have hGrr : Gv b w (n % b ^ Nat.log b m) < Gv b w (m % b ^ Nat.log b m) :=
            (IH _ hrn).2 _ hrlt
          calc Gv b w n
              = w ^ (Gv b w (Nat.log b m)) * ((n / b ^ Nat.log b m : ℕ))
                  + Gv b w (n % b ^ Nat.log b m) := hGn
            _ < w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ))
                  + Gv b w (m % b ^ Nat.log b m) := by
                  rw [hq]; exact add_lt_add_right hGrr _
            _ = Gv b w m := hGm.symm

theorem Gv_lt_opow (b : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hw : (b : Ordinal) ≤ w) (n k : ℕ)
    (h : n < b ^ k) : Gv b w n < w ^ (Gv b w k) :=
  (Gv_key_and_mono b w hb hw n).1 k h

theorem Gv_strictMono (b : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hw : (b : Ordinal) ≤ w) {n m : ℕ}
    (h : n < m) : Gv b w n < Gv b w m :=
  (Gv_key_and_mono b w hb hw n).2 m h

/-! ### The base-bumping operation -/

/-- `bump b c n` rewrites `n` in hereditary base `b` and replaces every occurrence of `b`
by `c`. -/
def bump (b c : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      c ^ (bump b c (Nat.log b (n + 1))) * ((n + 1) / b ^ Nat.log b (n + 1))
        + bump b c ((n + 1) % b ^ Nat.log b (n + 1))
  decreasing_by
    · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
    · exact nat_mod_pow_log_lt b (n + 1) (Nat.succ_ne_zero n)

theorem bump_def (b c n : ℕ) (hn : n ≠ 0) :
    bump b c n = c ^ (bump b c (Nat.log b n)) * (n / b ^ Nat.log b n)
      + bump b c (n % b ^ Nat.log b n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [bump]

@[simp] theorem bump_zero (b c : ℕ) : bump b c 0 = 0 := by rw [bump]

/-- The natural number `bump b c n` is exactly the value of the hereditary base-`b`
representation of `n` with `b` replaced by `c`. -/
theorem natCast_bump (b c n : ℕ) : ((bump b c n : ℕ) : Ordinal) = Gv b (c : Ordinal) n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [bump_def b c n hn, Gv_def b (c : Ordinal) n hn, ← IH _ (Nat.log_lt_self b hn),
        ← IH _ (nat_mod_pow_log_lt b n hn), Nat.cast_add, Ordinal.natCast_mul,
        natCast_pow_ord]

theorem bump_ne_zero (b c n : ℕ) (hc : 0 < c) (hn : n ≠ 0) : bump b c n ≠ 0 := by
  have h : (0 : Ordinal) < Gv b (c : Ordinal) n := Gv_pos b _ (by exact_mod_cast hc) n hn
  rw [← natCast_bump] at h
  exact_mod_cast h.ne'

/-- Bumping the base does not change the ordinal value. -/
theorem Gv_bump (b c : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hbc : b ≤ c)
    (n : ℕ) : Gv c w (bump b c n) = Gv b w n := by
  have hc : 2 ≤ c := le_trans hb hbc
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hLn : Nat.log b n < n := Nat.log_lt_self b hn
      have hrn : n % b ^ Nat.log b n < n := nat_mod_pow_log_lt b n hn
      have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (nat_pow_log_pos b n)
      have hq0 : 0 < n / b ^ Nat.log b n := nat_div_pow_log_pos b n hn
      have hqc : n / b ^ Nat.log b n < c := lt_of_lt_of_le (nat_div_pow_log_lt b n hb) hbc
      have hkey : bump b c (n % b ^ Nat.log b n) < c ^ bump b c (Nat.log b n) := by
        have h1 : Gv b (c : Ordinal) (n % b ^ Nat.log b n)
            < (c : Ordinal) ^ (Gv b (c : Ordinal) (Nat.log b n)) :=
          Gv_lt_opow b (c : Ordinal) hb (by exact_mod_cast hbc) _ _ hrb
        rw [← natCast_bump, ← natCast_bump, ← natCast_pow_ord] at h1
        exact_mod_cast h1
      have hx : bump b c n
          = c ^ (bump b c (Nat.log b n)) * (n / b ^ Nat.log b n)
            + bump b c (n % b ^ Nat.log b n) := bump_def b c n hn
      obtain ⟨h1, h2, h3⟩ := nat_decomp c (bump b c (Nat.log b n)) (n / b ^ Nat.log b n)
        (bump b c (n % b ^ Nat.log b n)) hc hq0 hqc hkey
      have hxne : bump b c n ≠ 0 := bump_ne_zero b c n (by omega) hn
      rw [Gv_def c w _ hxne, hx, h1, h2, h3, IH _ hLn, IH _ hrn, Gv_def b w n hn]

/-! ### The Goodstein sequence -/

/-- `goodstein n k` is the `k`-th term of the Goodstein sequence started at `n`
(with initial base `2`): at each step, write the current value in hereditary base `k + 2`,
replace the base by `k + 3`, and subtract one. -/
def goodstein (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) => bump (k + 2) (k + 3) (goodstein n k) - 1

/-- **Goodstein's theorem**: every Goodstein sequence eventually reaches `0`. -/
theorem Goodstein_terminates (n : ℕ) : ∃ k : ℕ, goodstein n k = 0 := by
  by_contra hcon
  push_neg at hcon
  set f : ℕ → Ordinal := fun k => Gv (k + 2) Ordinal.omega0 (goodstein n k) with hf
  have step : ∀ k : ℕ, f (k + 1) < f k := by
    intro k
    have hgk : goodstein n k ≠ 0 := hcon k
    have hxne : bump (k + 2) (k + 3) (goodstein n k) ≠ 0 :=
      bump_ne_zero _ _ _ (by omega) hgk
    have hlt : bump (k + 2) (k + 3) (goodstein n k) - 1
        < bump (k + 2) (k + 3) (goodstein n k) := by omega
    have hwk : ((k + 3 : ℕ) : Ordinal) ≤ Ordinal.omega0 := le_of_lt (Ordinal.nat_lt_omega0 _)
    calc f (k + 1)
        = Gv (k + 3) Ordinal.omega0 (bump (k + 2) (k + 3) (goodstein n k) - 1) := rfl
      _ < Gv (k + 3) Ordinal.omega0 (bump (k + 2) (k + 3) (goodstein n k)) :=
          Gv_strictMono (k + 3) Ordinal.omega0 (by omega) hwk hlt
      _ = Gv (k + 2) Ordinal.omega0 (goodstein n k) :=
          Gv_bump (k + 2) (k + 3) Ordinal.omega0 (by omega) (by omega) _
      _ = f k := rfl
  obtain ⟨a, ha, hmin⟩ := Ordinal.lt_wf.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  obtain ⟨k, rfl⟩ := ha
  exact hmin (f (k + 1)) ⟨k + 1, rfl⟩ (step k)

/-! ### Sanity checks

These confirm that the definitions really implement the Goodstein process:
bumping the base of `4 = 2 ^ 2` from `2` to `3` gives `27 = 3 ^ 3`, the Goodstein
sequence starting at `3` is `3, 3, 3, 2, 1, 0`, and the one starting at `4` begins
`4, 26, 41, 60, ...`.
-/

example : bump 2 3 4 = 27 := by norm_num [bump_def]

example : goodstein 3 5 = 0 := by norm_num [goodstein, bump_def]

example : goodstein 4 3 = 60 := by norm_num [goodstein, bump_def]

end Frontier

