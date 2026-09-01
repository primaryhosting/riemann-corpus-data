import Mathlib

/-!
# Ramanujan's partition congruence `p(7n+5) ≡ 0 (mod 7)`

This file contains a self-contained proof of Ramanujan's congruence for the modulus `7`.

The strategy is the classical generating function argument:

* Let `E = ∏ (1 - X^i)` and `P = ∑ p(n) X^n = E⁻¹`.
* Jacobi's identity `E^3 = ∑_{j ≥ 0} (-1)^j (2j+1) X^{j(j+1)/2}` is proved from a finite form of
  the Jacobi triple product, obtained by induction on `n` from the `q`-Pascal recursion for
  Gaussian binomial coefficients, together with a dual-number ("derivative at `z = -1`")
  specialization and a limiting argument.
* In characteristic `7` one has `E^7 = ∏ (1 - X^{7i})`, so `P · E^7 = E^6 = (E^3)^2`, and the
  coefficients of `(E^3)^2` in degrees `≡ 5 (mod 7)` vanish mod `7` because `-1` is not a square
  mod `7`.
* A strong induction then gives `7 ∣ p(7n+5)`.
-/

namespace Brockian.Ramanujan7

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

/-! ## Gaussian binomial coefficients -/

section QB

variable {R : Type*} [CommRing R]

/-- The Gaussian binomial coefficient `[n choose k]_q`, defined by the `q`-Pascal recursion. -/
def qb (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qb q n k + q ^ (k + 1) * qb q n (k + 1)

@[simp] lemma qb_zero_right (q : R) (n : ℕ) : qb q n 0 = 1 := by cases n <;> rfl

@[simp] lemma qb_zero_succ (q : R) (k : ℕ) : qb q 0 (k + 1) = 0 := rfl

lemma qb_succ_succ (q : R) (n k : ℕ) :
    qb q (n + 1) (k + 1) = qb q n k + q ^ (k + 1) * qb q n (k + 1) := rfl

lemma qb_eq_zero_of_lt (q : R) {n k : ℕ} (h : n < k) : qb q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp [qb] at *
  | succ n ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      rw [qb_succ_succ]
      rw [ih (by omega), ih (by omega)]
      ring

/-- The second (`dual`) form of the `q`-Pascal recursion. -/
lemma qb_pascal2 (q : R) (n k : ℕ) :
    qb q (n + 1) (k + 1) = q ^ (n - k) * qb q n k + qb q n (k + 1) := by
  -- First prove the ratio property: qb q m (k + 1) * (1 - q ^ (k + 1)) = qb q m k * (1 - q ^ (m - k))
  have qb_ratio : ∀ m k, k ≤ m → qb q m (k + 1) * (1 - q ^ (k + 1)) = qb q m k * (1 - q ^ (m - k)) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      simp at hk
      simp [qb]
    | succ m ihm =>
      intro k hk
      cases k with
      | zero =>
        -- Need: qb q (m + 1) 1 * (1 - q) = qb q (m + 1) 0 * (1 - q ^ (m + 1))
        -- qb q (m + 1) 0 = 1
        -- qb q (m + 1) 1 = ∑ i ∈ range (m + 1), q ^ i
        simp only [qb_zero_right]
        -- First prove qb q (m + 1) 1 = ∑ i ∈ range (m + 1), q ^ i
        have qb1 : qb q (m + 1) 1 = ∑ i ∈ range (m + 1), q ^ i := by
          have : ∀ n, qb q n 1 = ∑ i ∈ range n, q ^ i := by
            intro n
            induction n with
            | zero => simp [qb]
            | succ n ih =>
              simp [qb_succ_succ, ih, Finset.range_add_one]
              linear_combination geom_sum_mul q n
          exact this (m + 1)
        rw [qb1]
        have h := geom_sum_mul q (m + 1)
        simp
        -- h: (∑ i ∈ range (m + 1), q ^ i) * (q - 1) = q ^ (m + 1) - 1
        -- Need: (∑ i ∈ range (m + 1), q ^ i) * (1 - q) = 1 - q ^ (m + 1)
        linear_combination -h
      | succ k =>
        -- Goal: qb q (m + 1) (k + 2) * (1 - q ^ (k + 2)) = qb q (m + 1) (k + 1) * (1 - q ^ (m - k))
        have hkm' : k ≤ m := by omega
        -- Handle two cases: k < m and k = m
        by_cases hkm : k < m
        · -- k < m, so k + 1 ≤ m, can use IH for both k and k + 1
          have ih1 := ihm k hkm'  -- qb q m (k + 1) * (1 - q^(k+1)) = qb q m k * (1 - q^(m-k))
          have ih2 := ihm (k + 1) (by omega)  -- qb q m (k + 2) * (1 - q^(k+2)) = qb q m (k + 1) * (1 - q^(m-k-1))
          have ih2' : qb q m (k + 2) * (1 - q ^ (k + 2)) = qb q m (k + 1) * (1 - q ^ (m - (k + 1))) := by omega;
          simp only [qb_succ_succ]
          have hmk'' : m + 1 - (k + 1) = m - k := by omega
          rw [hmk'']
          calc (qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2)) * (1 - q ^ (k + 2))
              = qb q m (k + 1) * (1 - q ^ (k + 2)) + q ^ (k + 2) * qb q m (k + 2) * (1 - q ^ (k + 2)) := by ring
            _ = qb q m (k + 1) * (1 - q ^ (k + 2)) + q ^ (k + 2) * (qb q m (k + 1) * (1 - q ^ (m - (k + 1)))) := by linear_combination q ^ (k + 2) * ih2'
            _ = qb q m (k + 1) * ((1 - q ^ (k + 2)) + q ^ (k + 2) * (1 - q ^ (m - (k + 1)))) := by ring
            _ = qb q m (k + 1) * (1 - q ^ (m + 1)) := by
                congr 1
                have hexp : 2 + k + (m - (1 + k)) = m + 1 := by omega
                have h1 : q ^ 2 * q ^ k * q ^ (m - (1 + k)) = q ^ (m + 1) := by
                  rw [← pow_add, ← pow_add, hexp]
                ring_nf
                rw [h1]
                ring
            _ = (qb q m k + q ^ (k + 1) * qb q m (k + 1)) * (1 - q ^ (m - k)) := by
                calc qb q m (k + 1) * (1 - q ^ (m + 1))
                    = qb q m (k + 1) * (1 - q ^ (k + 1)) + qb q m (k + 1) * (q ^ (k + 1) - q ^ (m + 1)) := by ring
                  _ = qb q m (k + 1) * (1 - q ^ (k + 1)) + qb q m (k + 1) * q ^ (k + 1) * (1 - q ^ (m - k)) := by
                    congr 1
                    have hexp : k + 1 + (m - k) = m + 1 := by omega
                    have heq : q ^ (k + 1) * q ^ (m - k) = q ^ (m + 1) := by rw [← pow_add, hexp]
                    linear_combination qb q m (k + 1) * heq
                  _ = qb q m k * (1 - q ^ (m - k)) + qb q m (k + 1) * q ^ (k + 1) * (1 - q ^ (m - k)) := by rw [ih1]
                  _ = (qb q m k + q ^ (k + 1) * qb q m (k + 1)) * (1 - q ^ (m - k)) := by ring
        · -- k = m
          have hk_eq_m : k = m := by omega
          subst hk_eq_m
          norm_num
          -- qb q (k + 1) (k + 2) = 0 since k + 2 > k + 1
          have hqb : qb q (k + 1) (k + 2) = 0 := qb_eq_zero_of_lt q (by omega)
          rw [hqb]
          ring
  have key : ∀ m k, qb q m k + q ^ (k + 1) * qb q m (k + 1) = q ^ (m - k) * qb q m k + qb q m (k + 1) := by
    intro m k
    by_cases h : k ≤ m
    · have := qb_ratio m k h
      calc qb q m k + q ^ (k + 1) * qb q m (k + 1)
          = qb q m k * 1 + q ^ (k + 1) * qb q m (k + 1) * 1 := by ring
        _ = qb q m k * (1 - q ^ (m - k)) + qb q m k * q ^ (m - k) + q ^ (k + 1) * qb q m (k + 1) := by ring
        _ = qb q m (k + 1) * (1 - q ^ (k + 1)) + qb q m k * q ^ (m - k) + q ^ (k + 1) * qb q m (k + 1) := by rw [this]
        _ = qb q m (k + 1) + qb q m k * q ^ (m - k) := by ring
        _ = q ^ (m - k) * qb q m k + qb q m (k + 1) := by ring
    · push_neg at h
      have h1 : qb q m k = 0 := qb_eq_zero_of_lt q h
      have h2 : qb q m (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
      simp [h1, h2]
  rw [qb_succ_succ, key]

/-- The ratio identity between consecutive Gaussian binomial coefficients. -/
lemma qb_ratio (q : R) (m k : ℕ) :
    qb q m (k + 1) * (1 - q ^ (k + 1)) = qb q m k * (1 - q ^ (m - k)) := by
  have h := qb_pascal2 q m k
  rw [qb_succ_succ] at h
  linear_combination -h

/-- A two-step Pascal recursion, the engine of the induction proving `finite_jtp`. -/
lemma qb_step (q : R) (m k : ℕ) :
    qb q (m + 2) (k + 2)
      = (1 + q ^ (m + 1)) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2)
        + q ^ (m - k) * qb q m k := by
  rw [qb_succ_succ, qb_pascal2, qb_pascal2]
  by_cases hkm : k + 1 ≤ m
  · have hexp : k + 2 + (m - (k + 1)) = m + 1 := by
      have h1 : m - (k + 1) = m - k - 1 := by omega
      rw [h1]
      omega
    have hpow : q ^ (k + 2) * q ^ (m - (k + 1)) = q ^ (m + 1) := by
      rw [← pow_add]
      congr 1
    calc q ^ (m - k) * qb q m k + qb q m (k + 1) +
        q ^ (k + 2) * (q ^ (m - (k + 1)) * qb q m (k + 1) + qb q m (k + 2))
      _ = q ^ (m - k) * qb q m k + qb q m (k + 1) +
          q ^ (k + 2) * q ^ (m - (k + 1)) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2) := by ring
      _ = q ^ (m - k) * qb q m k + qb q m (k + 1) + q ^ (m + 1) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2) := by rw [hpow]
      _ = (1 + q ^ (m + 1)) * qb q m (k + 1) + q ^ (k + 2) * qb q m (k + 2) + q ^ (m - k) * qb q m k := by ring
  · have hq : qb q m (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
    simp [hq]
    ring

/-- The `q`-Pochhammer symbol `(q; q)_n = ∏_{i=1}^{n} (1 - q^i)`. -/
def qpoch (q : R) (n : ℕ) : R := ∏ i ∈ range n, (1 - q ^ (i + 1))

@[simp] lemma qpoch_zero (q : R) : qpoch q 0 = 1 := rfl

lemma qpoch_succ (q : R) (n : ℕ) : qpoch q (n + 1) = qpoch q n * (1 - q ^ (n + 1)) :=
  prod_range_succ _ _

/-- The product formula for Gaussian binomial coefficients. -/
lemma qb_mul_qpoch (q : R) {m k : ℕ} (h : k ≤ m) :
    qb q m k * qpoch q k * qpoch q (m - k) = qpoch q m := by
  induction m generalizing k with
  | zero =>
    simp [Nat.le_zero.mp h]
  | succ m ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [qb_succ_succ]
      have hm : m + 1 - (k + 1) = m - k := by omega
      rw [hm, qpoch_succ]
      by_cases hk : k + 1 ≤ m
      · have ihm : k + 1 ≤ m := hk
        have ihm' : k ≤ m := by omega
        have hmk : m - k = m - (k + 1) + 1 := by omega
        have hexp : m - (k + 1) + 1 = m - k := hmk.symm
        -- Rewrite qpoch q (m - k) in terms of qpoch q (m - (k+1))
        have hqpoch_mk : qpoch q (m - k) = qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) := by
          conv_lhs => rw [hmk]
          rw [qpoch_succ, hexp]
        -- Rewrite qpoch q (k + 1) in terms of qpoch q k
        have hk1 : qpoch q (k + 1) = qpoch q k * (1 - q ^ (k + 1)) := qpoch_succ q k
        -- IH instances
        have eq1 : qb q m k * qpoch q k * qpoch q (m - k) = qpoch q m := ih ihm'
        have eq2 : qb q m (k + 1) * qpoch q (k + 1) * qpoch q (m - (k + 1)) = qpoch q m := ih ihm
        rw [hqpoch_mk] at eq1
        rw [hk1] at eq2
        -- Goal after qpoch_succ on RHS
        rw [qpoch_succ q m]
        rw [hqpoch_mk]
        -- Expand the LHS
        have lhs_expand : (qb q m k + q ^ (k + 1) * qb q m (k + 1)) *
            (qpoch q k * (1 - q ^ (k + 1))) * (qpoch q (m - (k + 1)) * (1 - q ^ (m - k))) =
          qb q m k * qpoch q k * (1 - q ^ (k + 1)) * qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) +
          q ^ (k + 1) * qb q m (k + 1) * qpoch q k * (1 - q ^ (k + 1)) *
            qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) := by ring
        rw [lhs_expand]
        -- Use eq1 and eq2 to simplify
        -- eq1: qb q m k * qpoch q k * qpoch q (m - (k+1)) * (1 - q^(m-k)) = qpoch q m
        -- So term1 = eq1 * (1 - q^(k+1)) = qpoch q m * (1 - q^(k+1))
        have term1 : qb q m k * qpoch q k * (1 - q ^ (k + 1)) * qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) =
            qpoch q m * (1 - q ^ (k + 1)) := by
          linear_combination eq1 * (1 - q ^ (k + 1))
        -- eq2: qb q m (k+1) * qpoch q (k+1) * qpoch q (m - (k+1)) = qpoch q m
        -- So term2 = eq2 * q^(k+1) * (1 - q^(m-k)) = qpoch q m * q^(k+1) * (1 - q^(m-k))
        have term2 : q ^ (k + 1) * qb q m (k + 1) * qpoch q k * (1 - q ^ (k + 1)) *
            qpoch q (m - (k + 1)) * (1 - q ^ (m - k)) =
            qpoch q m * q ^ (k + 1) * (1 - q ^ (m - k)) := by
          linear_combination eq2 * q ^ (k + 1) * (1 - q ^ (m - k))
        rw [term1, term2]
        -- LHS = qpoch q m * (1 - q^(k+1)) + qpoch q m * q^(k+1) * (1 - q^(m-k))
        --     = qpoch q m * [(1 - q^(k+1)) + q^(k+1) * (1 - q^(m-k))]
        --     = qpoch q m * [1 - q^(k+1) + q^(k+1) - q^(m+1)]
        --     = qpoch q m * (1 - q^(m+1)) = RHS
        have hexp2 : q ^ (k + 1) * q ^ (m - k) = q ^ (m + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hexp2' : q * q ^ k * q ^ (m - k) = q * q ^ m := by
          simp_rw [mul_assoc, ← pow_add, show k + (m - k) = m by omega]
        linear_combination -hexp2 * qpoch q m
      · have hz : qb q m (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
        have hmk : k = m := by omega
        have hqbm : qb q m m = 1 := by
          clear h hm hk hz hmk ih
          induction m with
          | zero => rfl
          | succ n ih => rw [qb_succ_succ]; simp [ih, qb_eq_zero_of_lt q (by omega : n < n + 1)]
        have hqbm1 : qb q m (m + 1) = 0 := qb_eq_zero_of_lt q (by omega)
        simp [hmk, hqbm, hqbm1, qpoch_succ]

end QB

/-! ## The finite Jacobi triple product -/

/-- The `m`-th triangular number. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := by
  have h : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
  simp only [tri, h]
  omega

lemma tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ fun n => by rw [tri_succ]; omega

lemma tri_injective : Function.Injective tri := tri_strictMono.injective

lemma self_le_tri (m : ℕ) : m ≤ tri m := by
  induction m with
  | zero => simp [tri]
  | succ n ih => rw [tri_succ]; omega

/-- The exponent `T_{k-n}` (a triangular number of the "integer" `k - n`). -/
def ee (n k : ℕ) : ℕ := if n ≤ k then tri (k - n) else tri (n - k - 1)

lemma ee_add (n j : ℕ) : ee n (n + j) = tri j := by
  simp [ee, tri]

lemma ee_sub (n j : ℕ) (h : j < n) : ee n (n - 1 - j) = tri j := by
  unfold ee
  have hn : ¬(n ≤ n - 1 - j) := by omega
  simp only [hn, if_false]
  congr 1
  omega

/-- `ee n k` only depends on the difference `k - n`. -/
lemma ee_shift (n k : ℕ) : ee (n + 1) (k + 1) = ee n k := by
  unfold ee
  by_cases h : n ≤ k
  · simp [h]
  · push_neg at h
    simp

lemma ee_up (n k : ℕ) : ee n k + n = ee (n + 1) k + k := by
  by_cases h : n ≤ k
  · by_cases h2 : n < k
    · -- n < k: ee n k = tri (k - n), ee (n+1) k = tri (k - n - 1)
      simp [ee, h, show n + 1 ≤ k from Nat.succ_le_of_lt h2]
      have : k - n = k - (n + 1) + 1 := by omega
      rw [this, tri_succ]
      omega
    · -- n = k
      push_neg at h2
      simp [ee, show n = k from le_antisymm h h2]
  · -- n > k
    push_neg at h
    simp [ee]
    split_ifs with h1 h2 <;> try omega
    -- Goal: tri (n - k - 1) + n = tri (n + 1 - k - 1) + k
    -- First simplify n + 1 - k - 1 = n - k
    have heq1 : n + 1 - k - 1 = n - k := by omega
    rw [heq1]
    -- Goal: tri (n - k - 1) + n = tri (n - k) + k
    -- Now use tri_succ: tri (n - k) = tri (n - k - 1) + (n - k)
    have heq2 : n - k = n - k - 1 + 1 := by omega
    rw [heq2, tri_succ]
    simp only [show n - k - 1 + 1 - 1 = n - k - 1 from by omega]
    omega

lemma ee_down (n k : ℕ) (h : k ≤ 2 * n) : ee n (k + 1) + (2 * n - k) = n + 1 + ee n k := by
  by_cases hn : n ≤ k
  · -- Case: n ≤ k, so ee n k = tri (k - n)
    have hn1 : n ≤ k + 1 := by omega
    simp [ee, hn, hn1]
    -- Let d = k - n
    set d := k - n with hd_def
    have hd2 : k + 1 - n = d + 1 := by omega
    have hd3 : 2 * n - k = n - d := by omega
    rw [hd2, hd3]
    -- Need: tri (d + 1) + (n - d) = n + 1 + tri d
    -- i.e., tri (d + 1) = tri d + (d + 1)
    have tri_succ : tri (d + 1) = tri d + (d + 1) := by
      simp only [tri]
      have h : (d + 1) * (d + 1 + 1) = d * (d + 1) + 2 * (d + 1) := by ring
      omega
    rw [tri_succ]
    omega
  · -- Case: k < n, so ee n k = tri (n - k - 1)
    push_neg at hn
    simp [ee, hn]
    by_cases hn1 : k + 1 ≥ n
    · -- Subcase: k + 1 ≥ n, which means k + 1 = n since k < n
      have hk1 : k + 1 = n := by omega
      have hk : ¬(n ≤ k) := by omega
      simp [hk]
      simp [tri]
      simp [hk1]
      have : n - k - 1 = 0 := by omega
      simp [this]
      omega
    · -- Subcase: k + 1 < n
      push_neg at hn1
      have hk : ¬(n ≤ k) := by omega
      have hk1 : ¬(n ≤ k + 1) := by omega
      simp [hk, hk1, tri]
      -- Let m = n - k - 1, then n - (k+1) - 1 = m - 1
      set m := n - k - 1 with hm_def
      have hm_pos : m ≥ 1 := by omega
      have h1 : n - (k + 1) - 1 = m - 1 := by omega
      have h2 : 2 * n - k = n + m + 1 := by omega
      rw [h1, h2]
      -- Need: tri (m-1) + (n + m + 1) = n + 1 + tri m
      -- i.e., tri (m-1) + m = tri m
      have tri_add : (m - 1) * m / 2 + m = m * (m + 1) / 2 := by
        have heq : (m - 1) * m + 2 * m = m * (m + 1) := by nlinarith [Nat.sub_add_cancel hm_pos]
        have : ((m - 1) * m + 2 * m) / 2 = ((m - 1) * m) / 2 + m := by
          rw [← Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
        omega
      simp [Nat.sub_add_cancel hm_pos]
      linarith [tri_add]

section FJTP

variable {R : Type*} [CommRing R]

/-- The coefficient of `z ^ k` in the finite Jacobi triple product of order `n`. -/
def cc (q : R) (n k : ℕ) : R := q ^ ee n k * qb q (2 * n) k

lemma cc_eq_zero_of_lt (q : R) {n k : ℕ} (h : 2 * n < k) : cc q n k = 0 := by
  simp [cc, qb_eq_zero_of_lt q h]

lemma cc_rec0 (q : R) (n : ℕ) : cc q (n + 1) 0 = q ^ n * cc q n 0 := by
  simp [cc, qb_zero_right]
  rw [← pow_add]
  congr 1
  cases n with
  | zero => simp [ee, tri]
  | succ n =>
    have h1 : ee (n + 1 + 1) 0 = tri (n + 1) := by simp [ee]
    have h2 : ee (n + 1) 0 = tri n := by simp [ee]
    rw [h1, h2, tri_succ, add_comm]

lemma cc_rec1 (q : R) (n : ℕ) :
    cc q (n + 1) 1 = (1 + q ^ (2 * n + 1)) * cc q n 0 + q ^ n * cc q n 1 := by
  unfold cc
  rw [ee_shift]
  simp [qb_zero_right]
  -- Goal: q ^ ee n 0 * qb q (2 * (n + 1)) 1 = (1 + q ^ (2 * n + 1)) * q ^ ee n 0 + q ^ n * (q ^ ee n 1 * qb q (2 * n) 1)
  -- Key identity: n + ee n 1 = ee n 0 + 1 (from ee_up and ee_shift)
  have ee_rel : n + ee n 1 = ee n 0 + 1 := by
    have := ee_up n 1
    simp [ee_shift] at this
    linarith
  -- Use qb_succ_succ recurrence: qb q (m+1) 1 = qb q m 0 + q * qb q m 1 = 1 + q * qb q m 1
  have qb1 : ∀ m : ℕ, qb q (m + 1) 1 = 1 + q * qb q m 1 := by
    intro m
    rw [qb_succ_succ]
    simp [qb_zero_right]
  rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  have h2 : qb q (2 * n + 2) 1 = 1 + q * qb q (2 * n + 1) 1 := qb1 (2 * n + 1)
  have h1 : qb q (2 * n + 1) 1 = 1 + q * qb q (2 * n) 1 := qb1 (2 * n)
  rw [h2, h1]
  -- Also need: qb q n 1 = ∑ i ∈ range n, q ^ i
  have qb_q1 : ∀ m : ℕ, qb q m 1 = ∑ i ∈ range m, q ^ i := by
    intro m
    induction m with
    | zero => simp [qb]
    | succ m ih =>
      rw [qb_succ_succ, ih, Finset.range_add_one]
      simp [qb_zero_right]
      linear_combination geom_sum_mul q m
  -- Use geometric series property: (q - 1) * qb q (2*n) 1 = q^(2*n) - 1
  have geo_sum : (q - 1) * qb q (2 * n) 1 = q ^ (2 * n) - 1 := by
    rw [qb_q1]
    rw [mul_comm]
    exact geom_sum_mul q (2 * n)
  -- Use: q ^ n * q ^ ee n 1 = q ^ (ee n 0 + 1) = q * q ^ ee n 0
  have q_prod : q ^ n * q ^ ee n 1 = q ^ ee n 0 * q := by
    have h : n + ee n 1 = ee n 0 + 1 := by linarith
    rw [← pow_add, h, pow_succ', mul_comm]
  have qb_term : q ^ n * (q ^ ee n 1 * qb q (2 * n) 1) = q ^ ee n 0 * q * qb q (2 * n) 1 := by
    rw [← mul_assoc (q ^ n) (q ^ ee n 1), q_prod]
  rw [qb_term]
  linear_combination geo_sum * q ^ (ee n 0 + 1)

lemma cc_rec2 (q : R) (n k : ℕ) :
    cc q (n + 1) (k + 2)
      = (1 + q ^ (2 * n + 1)) * cc q n (k + 1) + q ^ n * cc q n (k + 2)
        + q ^ (n + 1) * cc q n k := by
  unfold cc
  -- Key exponent relations from ee
  have h_ee_shift : ee (n + 1) (k + 2) = ee n (k + 1) := ee_shift n (k + 1)
  -- Use qb_succ_succ and qb_pascal2 to expand
  rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  rw [qb_succ_succ, qb_pascal2, qb_pascal2]
  rw [h_ee_shift]
  by_cases hk : k + 1 ≤ 2 * n
  · -- Case: k + 1 ≤ 2 * n
    have hk2 : k + 2 ≤ 2 * n + 1 := by omega
    -- Identity: q ^ (k + 2) * q ^ (2 * n - (k + 1)) = q ^ (2 * n + 1)
    have id1 : q ^ (k + 2) * q ^ (2 * n - (k + 1)) = q ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    -- ee_down relations
    have id2 : ee n (k + 2) + (2 * n - (k + 1)) = n + 1 + ee n (k + 1) := ee_down n (k + 1) (by omega)
    have id3 : ee n (k + 1) + (2 * n - k) = n + 1 + ee n k := ee_down n k (by omega)
    -- Rewrite exponent terms
    have id1' : q ^ (k + 1 + 1) * q ^ (2 * n - (k + 1)) = q ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    -- q ^ n * q ^ ee n (k + 2) = q ^ (ee n (k + 1) + k + 2)
    have id2' : q ^ n * q ^ ee n (k + 2) = q ^ (ee n (k + 1) + k + 2) := by
      rw [← pow_add]
      congr 1
      have : ee n (k + 2) = n + 1 + ee n (k + 1) - (2 * n - (k + 1)) := by rw [← id2]; omega
      omega
    -- q ^ (n + 1) * q ^ ee n k = q ^ (ee n (k + 1) + (2 * n - k))
    have id3' : q ^ (n + 1) * q ^ ee n k = q ^ (ee n (k + 1) + (2 * n - k)) := by
      rw [← pow_add, id3]
    -- Compute both sides explicitly
    have lhs_eq : q ^ ee n (k + 1) *
        (q ^ (2 * n - k) * qb q (2 * n) k + qb q (2 * n) (k + 1) +
          q ^ (k + 1 + 1) * (q ^ (2 * n - (k + 1)) * qb q (2 * n) (k + 1) + qb q (2 * n) (k + 1 + 1))) =
        q ^ (ee n (k + 1) + (2 * n - k)) * qb q (2 * n) k +
        q ^ ee n (k + 1) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + (2 * n + 1)) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + k + 2) * qb q (2 * n) (k + 2) := by
      rw [mul_add, mul_add]
      -- Expand the nested multiplication in the third term
      conv_lhs => right; right; rw [mul_add, ← mul_assoc, id1']
      ring
    have rhs_eq : (1 + q ^ (2 * n + 1)) * (q ^ ee n (k + 1) * qb q (2 * n) (k + 1)) +
        q ^ n * (q ^ ee n (k + 2) * qb q (2 * n) (k + 2)) +
        q ^ (n + 1) * (q ^ ee n k * qb q (2 * n) k) =
        q ^ (ee n (k + 1) + (2 * n - k)) * qb q (2 * n) k +
        q ^ ee n (k + 1) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + (2 * n + 1)) * qb q (2 * n) (k + 1) +
        q ^ (ee n (k + 1) + k + 2) * qb q (2 * n) (k + 2) := by
      rw [add_mul, one_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      rw [id2', id3']
      ring
    rw [lhs_eq, rhs_eq]
  · -- Case: k + 1 > 2 * n, so k ≥ 2 * n
    push_neg at hk
    have hk' : 2 * n < k + 1 := hk
    have hqb_k1 : qb q (2 * n) (k + 1) = 0 := qb_eq_zero_of_lt q (by omega)
    have hqb_k2 : qb q (2 * n) (k + 2) = 0 := qb_eq_zero_of_lt q (by omega)
    simp [hqb_k1, hqb_k2]
    -- Now k = 2 * n or k > 2 * n
    by_cases hk'' : k = 2 * n
    · subst hk''
      simp
      -- Need: q ^ ee n (2 * n + 1) = q ^ (n + 1) * q ^ ee n (2 * n)
      -- i.e., ee n (2 * n + 1) = n + 1 + ee n (2 * n)
      have h_ee_down : ee n (2 * n + 1) = n + 1 + ee n (2 * n) := by
        have := ee_down n (2 * n) (by omega : 2 * n ≤ 2 * n)
        simp at this ⊢
        linarith
      rw [h_ee_down]
      ring
    · -- k > 2 * n
      have hk''' : 2 * n < k := by omega
      have hqb_k : qb q (2 * n) k = 0 := qb_eq_zero_of_lt q hk'''
      simp [hqb_k]

/-- Enlarging the summation range does not change the finite Jacobi sum. -/
lemma sum_cc_ext (q z : R) (n N : ℕ) (h : 2 * n + 1 ≤ N) :
    ∑ k ∈ range N, cc q n k * z ^ k = ∑ k ∈ range (2 * n + 1), cc q n k * z ^ k := by
  rw [← Finset.sum_subset (Finset.range_mono h)]
  intro k hk hkn
  simp at hkn
  have : cc q n k = 0 := cc_eq_zero_of_lt q (by omega)
  simp [this]

/-- Shifting the index of the finite Jacobi sum by two. -/
lemma cc_shiftA (q z : R) (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), cc q n (k + 2) * z ^ (k + 2)
      = (∑ k ∈ range (2 * n + 1), cc q n k * z ^ k) - cc q n 0 - cc q n 1 * z := by
  have h3 : ∑ k ∈ range (2 * n + 3), cc q n k * z ^ k
      = ∑ k ∈ range (2 * n + 1), cc q n k * z ^ k := sum_cc_ext q z n (2 * n + 3) (by omega)
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from rfl, Finset.sum_range_succ',
    show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Finset.sum_range_succ'] at h3
  simp only [pow_zero, mul_one] at h3
  rw [← h3]
  ring

/-- Shifting the index of the finite Jacobi sum by one. -/
lemma cc_shiftB (q z : R) (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), cc q n (k + 1) * z ^ (k + 2)
      = ((∑ k ∈ range (2 * n + 1), cc q n k * z ^ k) - cc q n 0) * z := by
  have h2 : ∑ k ∈ range (2 * n + 2), cc q n k * z ^ k
      = ∑ k ∈ range (2 * n + 1), cc q n k * z ^ k := sum_cc_ext q z n (2 * n + 2) (by omega)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Finset.sum_range_succ'] at h2
  simp only [pow_zero, mul_one] at h2
  rw [← h2, add_sub_cancel_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Multiplying the finite Jacobi sum by `z ^ 2`. -/
lemma cc_shiftC (q z : R) (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), cc q n k * z ^ (k + 2)
      = (∑ k ∈ range (2 * n + 1), cc q n k * z ^ k) * z ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The generating-polynomial form of the recursions `cc_rec0`, `cc_rec1`, `cc_rec2`. -/
lemma cc_gen_step (q z : R) (n : ℕ) :
    ∑ k ∈ range (2 * (n + 1) + 1), cc q (n + 1) k * z ^ k
      = (∑ k ∈ range (2 * n + 1), cc q n k * z ^ k)
          * (q ^ n + (1 + q ^ (2 * n + 1)) * z + q ^ (n + 1) * z ^ 2) := by
  have hrange : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
  rw [hrange, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  have hterm : ∀ k ∈ range (2 * n + 1), cc q (n + 1) (k + 1 + 1) * z ^ (k + 1 + 1)
      = (1 + q ^ (2 * n + 1)) * (cc q n (k + 1) * z ^ (k + 2))
        + q ^ n * (cc q n (k + 2) * z ^ (k + 2)) + q ^ (n + 1) * (cc q n k * z ^ (k + 2)) := by
    intro k _
    rw [show k + 1 + 1 = k + 2 from rfl, cc_rec2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, cc_shiftA, cc_shiftB, cc_shiftC,
    cc_rec1, cc_rec0]
  ring

/-- The finite form of the Jacobi triple product. -/
theorem finite_jtp (q z : R) (n : ℕ) :
    (∏ i ∈ range n, (1 + z * q ^ (i + 1))) * (∏ i ∈ range n, (z + q ^ i))
      = ∑ k ∈ range (2 * n + 1), cc q n k * z ^ k := by
  induction n with
  | zero => simp [cc, ee, tri]
  | succ n ih =>
    rw [Finset.range_add_one, prod_insert (by simp), Finset.range_add_one,
      prod_insert (by simp)]
    have factored : ((1 + z * q ^ (n + 1)) * ∏ i ∈ range n, (1 + z * q ^ (i + 1))) *
        ((z + q ^ n) * ∏ i ∈ range n, (z + q ^ i)) =
        ((∏ i ∈ range n, (1 + z * q ^ (i + 1))) * ∏ i ∈ range n, (z + q ^ i)) *
        ((1 + z * q ^ (n + 1)) * (z + q ^ n)) := by ring
    rw [factored, ih]
    have quad_eq : (1 + z * q ^ (n + 1)) * (z + q ^ n) = q ^ n + (1 + q ^ (2 * n + 1)) * z + q ^ (n + 1) * z ^ 2 := by ring
    rw [quad_eq]
    rw [Finset.range_add_one]
    rw [show insert (2 * n) (range (2 * n)) = range (2 * n + 1) by rw [Finset.range_add_one]]
    rw [← cc_gen_step]
    rw [Finset.range_add_one]

/-! ### Dual numbers: extracting the derivative at `z = -1` -/

open TrivSqZeroExt DualNumber in
lemma qb_inl (q : R) (n k : ℕ) :
    qb (inl q : DualNumber R) n k = inl (qb q n k) := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [qb_succ_succ]
      rw [ih k, ih (k + 1)]
      simp [qb]

open TrivSqZeroExt DualNumber in
lemma cc_inl (q : R) (n k : ℕ) :
    cc (inl q : DualNumber R) n k = inl (cc q n k) := by
  unfold cc
  rw [qb_inl]
  simp [inl_pow]

open TrivSqZeroExt DualNumber in
lemma eps_mul_eq (x : DualNumber R) : (ε : DualNumber R) * x = inl x.fst * ε := by
  rcases x with ⟨a, b⟩
  let y : DualNumber R := ⟨a, b⟩
  show inr (1 : R) * y = inl a * inr (1 : R)
  ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  rfl

open TrivSqZeroExt DualNumber in
lemma neg_one_add_eps_pow (k : ℕ) :
    ((-1 : DualNumber R) + ε) ^ k
      = inl ((-1 : R) ^ k) + inl ((k : R) * (-1 : R) ^ (k + 1)) * ε := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    ring_nf
    simp [sq]
    ring

open TrivSqZeroExt DualNumber in
lemma snd_mul_eps (x : DualNumber R) : (x * ε).snd = x.fst := by
  rcases x with ⟨a, b⟩
  show ((⟨a * (0 : R), a * 1 + b * 0⟩ : TrivSqZeroExt R R)).snd = a
  simp

open TrivSqZeroExt DualNumber in
lemma fst_prod {ι : Type*} (s : Finset ι) (f : ι → DualNumber R) :
    (∏ i ∈ s, f i).fst = ∏ i ∈ s, (f i).fst := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, fst_mul, ih]

/-- Specializing `z = -1` in `finite_jtp`. -/
theorem fjtp_fst (q : R) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (2 * N + 1), (-1 : R) ^ k * cc q N k = 0 := by
  have := finite_jtp q (-1) N
  have hprod : ∏ i ∈ range N, (-(1 : R) + q ^ i) = 0 := by
    rw [Finset.prod_eq_zero (mem_range.mpr hN)]
    simp
  simp_all [mul_comm]

open TrivSqZeroExt DualNumber in
lemma mul_eps_eq (x : DualNumber R) : x * (ε : DualNumber R) = inl x.fst * ε := by
  rcases x with ⟨a, b⟩
  ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]

open TrivSqZeroExt DualNumber in
/-- The `ε`-component of the right-hand side of `finite_jtp` specialized at `z = -1 + ε`. -/
lemma dual_snd_sum (q : R) (N : ℕ) :
    (∑ k ∈ range (2 * N + 1),
        cc (inl q : DualNumber R) N k * ((-1 : DualNumber R) + ε) ^ k).snd
      = ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * (k : R)) * cc q N k := by
  rw [TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cc_inl, neg_one_add_eps_pow]
  simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul]
  ring

open TrivSqZeroExt DualNumber in
/-- The `fst`-component of the first product of `finite_jtp` specialized at `z = -1 + ε`. -/
lemma dual_prodA_fst (q : R) (N : ℕ) :
    (∏ i ∈ range N,
        (1 + ((-1 : DualNumber R) + ε) * (inl q : DualNumber R) ^ (i + 1))).fst = qpoch q N := by
  rw [fst_prod]
  apply Finset.prod_congr rfl
  intro i _
  show (1 + ((-1 : DualNumber R) + ε) * (inl q : DualNumber R) ^ (i + 1)).fst = 1 - q ^ (i + 1)
  simp [fst_add, fst_mul]
  ring

open TrivSqZeroExt DualNumber in
/-- The second product of `finite_jtp` specialized at `z = -1 + ε` is a pure `ε`-term. -/
lemma dual_prodB_eq (q : R) (M : ℕ) :
    ∏ i ∈ range (M + 1), (((-1 : DualNumber R) + ε) + (inl q : DualNumber R) ^ i)
      = inl ((-1 : R) ^ M * qpoch q M) * ε := by
  induction M with
  | zero => simp [qpoch_zero]
  | succ M ih =>
    rw [Finset.prod_range_succ, ih]
    simp [inl_pow, add_comm, add_assoc]
    rw [mul_assoc, eps_mul_eq, inl_mul_inl]
    simp [qpoch_succ, pow_succ]
    ring

open TrivSqZeroExt DualNumber in
/-- The `ε`-component (the derivative at `z = -1`) of `finite_jtp`. -/
theorem fjtp_eps (q : R) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * (k : R)) * cc q N k
      = (-1 : R) ^ (N + 1) * (qpoch q N * qpoch q (N - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := finite_jtp (inl q : DualNumber R) ((-1 : DualNumber R) + ε) (M + 1)
  rw [dual_prodB_eq] at h
  have hsnd := congrArg TrivSqZeroExt.snd h
  rw [dual_snd_sum] at hsnd
  rw [← hsnd, ← mul_assoc, mul_eps_eq, snd_mul_eps, fst_mul, dual_prodA_fst]
  simp
  ring

/-- The key finite identity: the finite form of Jacobi's identity. -/
theorem fjtp_key (q : R) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * ((k : R) - (N : R))) * cc q N k
      = (-1 : R) ^ (N + 1) * (qpoch q N * qpoch q (N - 1)) := by
  have h1 := fjtp_eps q N hN
  have h2 := fjtp_fst q N hN
  have hsplit : ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * ((k : R) - (N : R))) * cc q N k
      = (∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * (k : R)) * cc q N k)
        + (N : R) * ∑ k ∈ range (2 * N + 1), (-1 : R) ^ k * cc q N k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]
    ring
  rw [hsplit, h1, h2, mul_zero, add_zero]

/-- Splitting a sum over `range (2 * N + 1)` at the midpoint `k = N`. -/
lemma sum_range_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ range (2 * N + 1), f k
      = ∑ j ∈ range (N + 1), f (N + j) + ∑ j ∈ range N, f (N - 1 - j) := by
  have h2N1 : 2 * N + 1 = N + (N + 1) := by ring
  rw [h2N1]
  rw [← sum_range_add_sum_Ico _ (by omega : N ≤ N + (N + 1))]
  simp_rw [sum_Ico_eq_sum_range]
  have hsimp : N + (N + 1) - N = N + 1 := by omega
  rw [hsimp]
  rw [add_comm]
  congr 1
  exact (@Finset.sum_range_reflect _ _ f N).symm

/-- Splitting the key sum at `k = N` (for even `N`). -/
theorem key_split (q : R) (N : ℕ) (hN : Even N) :
    ∑ k ∈ range (2 * N + 1), ((-1 : R) ^ (k + 1) * ((k : R) - (N : R))) * cc q N k
      = ∑ j ∈ range (N + 1), ((-1 : R) ^ (j + 1) * (j : R)) * (q ^ tri j * qb q (2 * N) (N + j))
        + ∑ j ∈ range N, ((-1 : R) ^ (j + 1) * ((j : R) + 1))
            * (q ^ tri j * qb q (2 * N) (N - 1 - j)) := by
  rw [sum_range_split]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hN_even : (-1 : R) ^ N = 1 := by rw [hN.neg_one_pow]
    have hpow : (-1 : R) ^ (N + j + 1) = (-1 : R) ^ (j + 1) := by
      rw [pow_add, pow_add, hN_even]; ring
    rw [cc, ee_add, hpow]
    simp [Nat.cast_add]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < N := by simp at hj; exact hj
    have hN_even : (-1 : R) ^ N = 1 := by rw [hN.neg_one_pow]
    rw [cc, ee_sub _ _ hj']
    -- Need to show (-1)^(N - j) = (-1)^j when N is even
    have hN_ge_j : N ≥ j := le_of_lt hj'
    have hpow : (-1 : R) ^ (N - 1 - j + 1) = (-1 : R) ^ j := by
      have heq : N - 1 - j + 1 = N - j := by omega
      rw [heq]
      by_cases hj_even : Even j
      · have hNj_even : Even (N - j) := by rw [Nat.even_sub hN_ge_j]; simp [hN, hj_even]
        rw [hj_even.neg_one_pow, hNj_even.neg_one_pow]
      · have hj_odd : Odd j := by simpa using hj_even
        have hNj_odd : Odd (N - j) := by
          obtain ⟨m, hm⟩ := hj_odd
          obtain ⟨n, hn⟩ := hN
          subst hm hn
          use n - m - 1
          omega
        rw [hj_odd.neg_one_pow, hNj_odd.neg_one_pow]
    rw [hpow]
    have hsub : ((N - 1 - j : ℕ) : R) - N = -((j : R) + 1) := by
      have h1 : N ≥ 1 + j := by omega
      rw [Nat.sub_sub, Nat.cast_sub h1]
      simp
      ring
    simp [hsub]
    ring

end FJTP

/-! ## Power series over `ZMod 7` -/

/-- Power series over `ZMod 7`. -/
abbrev S7 : Type := PowerSeries (ZMod 7)

section PS

local instance : TopologicalSpace (ZMod 7) := ⊥
local instance : DiscreteTopology (ZMod 7) := ⟨rfl⟩

/-! ### Congruences modulo `X ^ (d+1)` -/

lemma dvd_iff_coeff (d : ℕ) (f g : S7) :
    (X : S7) ^ (d + 1) ∣ (f - g) ↔ ∀ m ≤ d, (coeff m) f = (coeff m) g := by
  rw [PowerSeries.X_pow_dvd_iff]
  simp [sub_eq_zero]

lemma dvd_sub_mul {N : ℕ} {a b c e : S7} (h1 : (X : S7) ^ N ∣ (a - b))
    (h2 : (X : S7) ^ N ∣ (c - e)) : (X : S7) ^ N ∣ (a * c - b * e) := by
  have h : a * c - b * e = a * (c - e) + (a - b) * e := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_right h2 a) (dvd_mul_of_dvd_left h1 e)

lemma dvd_sub_pow {N : ℕ} {a b : S7} (k : ℕ) (h : (X : S7) ^ N ∣ (a - b)) :
    (X : S7) ^ N ∣ (a ^ k - b ^ k) := by
  induction k with
  | zero => simp [pow_zero]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rw [show a ^ n * a - b ^ n * b = a ^ n * (a - b) + (a ^ n - b ^ n) * b by ring]
    exact dvd_add (dvd_mul_of_dvd_right h (a ^ n)) (dvd_mul_of_dvd_left ih b)

lemma dvd_mul_X_pow (d e : ℕ) (h : d < e) (a : S7) : (X : S7) ^ (d + 1) ∣ a * X ^ e := by
  refine Dvd.dvd.mul_left ?_ a
  exact pow_dvd_pow _ (by omega)

/-! ### The basic series -/

/-- The Euler product `E = ∏_{i ≥ 1} (1 - X^i)`. -/
noncomputable def EE : S7 := ∏' i : ℕ, (1 - (X : S7) ^ (i + 1))

/-- The generating function of the partition numbers. -/
noncomputable def PP : S7 := Nat.Partition.genFun (fun _ _ => (1 : ZMod 7))

/-- The coefficients of the Jacobi cube `∑ (-1)^j (2j+1) X^{T_j}`. -/
def jcoef (m : ℕ) : ZMod 7 :=
  ∑ j ∈ range (m + 1), if tri j = m then (-1 : ZMod 7) ^ j * (2 * j + 1) else 0

/-- The Jacobi cube series. -/
def JJ : S7 := PowerSeries.mk jcoef

/-- Partial sums of the Jacobi cube series. -/
noncomputable def Jpart (n : ℕ) : S7 := ∑ j ∈ range n, C ((-1 : ZMod 7) ^ j * (2 * j + 1)) * X ^ tri j

lemma coeff_PP (n : ℕ) :
    (coeff n) PP = (Fintype.card (Nat.Partition n) : ZMod 7) := by
  simp [PP, Nat.Partition.genFun]

lemma hasProd_EE : HasProd (fun i : ℕ => 1 - (X : S7) ^ (i + 1)) EE :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow (ZMod 7)).hasProd

lemma hasProd_PP :
    HasProd (fun i : ℕ => 1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1))) PP := by
  have h := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ZMod 7))
  exact h

lemma factor_mul_eq_one (i : ℕ) :
    (1 - (X : S7) ^ (i + 1)) * (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1)))
      = 1 := by
  have hc : PowerSeries.constantCoeff ((X : S7) ^ (i + 1)) = 0 := by simp
  have hsum : Summable (fun j : ℕ => ((X : S7) ^ (i + 1)) ^ j) :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hc
  have key : (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1)))
      = ∑' j : ℕ, ((X : S7) ^ (i + 1)) ^ j := by
    rw [hsum.tsum_eq_zero_add]
    simp [pow_succ, pow_mul, mul_comm]
  rw [key]
  exact PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hc

lemma PP_mul_EE : PP * EE = 1 := by
  have h2 : HasProd (fun i : ℕ =>
      (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1))) * (1 - (X : S7) ^ (i + 1)))
      (PP * EE) := hasProd_PP.mul hasProd_EE
  have h3 : (fun i : ℕ =>
      (1 + ∑' j : ℕ, (1 : ZMod 7) • (X : S7) ^ ((i + 1) * (j + 1))) * (1 - (X : S7) ^ (i + 1)))
      = fun _ : ℕ => (1 : S7) := by
    funext i
    rw [mul_comm]
    exact factor_mul_eq_one i
  rw [h3] at h2
  exact h2.unique hasProd_one

/-- A product of factors of high order is congruent to `1`. -/
lemma prod_factors_congr_one (d : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, d ≤ i) :
    (X : S7) ^ (d + 1) ∣ ((∏ i ∈ s, (1 - (X : S7) ^ (i + 1))) - 1) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_all
    -- We have: X^(d+1) | ∏ x ∈ s, (1 - X^(x+1)) - 1
    -- We need: X^(d+1) | (1 - X^(a+1)) * ∏ x ∈ s, (1 - X^(x+1)) - 1
    -- Rewrite: (1 - X^(a+1)) * ∏ ... - 1 = (1 - X^(a+1)) * (∏ ... - 1) + ((1 - X^(a+1)) - 1)
    obtain ⟨hda, _⟩ := hs
    have h1 : (1 - (X : S7) ^ (a + 1)) * ∏ x ∈ s, (1 - (X : S7) ^ (x + 1)) - 1 =
              (1 - (X : S7) ^ (a + 1)) * (∏ x ∈ s, (1 - (X : S7) ^ (x + 1)) - 1) + ((1 - (X : S7) ^ (a + 1)) - 1) := by ring
    rw [h1]
    apply dvd_add
    · exact dvd_mul_of_dvd_right ih _
    · have : (1 : S7) - X ^ (a + 1) - 1 = -(X ^ (a + 1)) := by ring
      rw [this]
      have h : d + 1 ≤ a + 1 := by omega
      exact (dvd_neg.mpr (pow_dvd_pow _ h))

/-- Two consecutive truncated products agree to high order. -/
lemma qpoch_stable (d M N : ℕ) (hM : d ≤ M) (hMN : M ≤ N) :
    (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) N - qpoch (X : S7) M) := by
  induction hMN with
  | refl => simp
  | @step m n ih =>
    rw [qpoch_succ]
    -- qpoch m * (1 - X^(m+1)) - qpoch M = (qpoch m - qpoch M) * (1 - X^(m+1)) + qpoch M * X^(m+1)
    have h1 : qpoch (X : S7) m * (1 - (X : S7) ^ (m + 1)) - qpoch (X : S7) M =
              (qpoch (X : S7) m - qpoch (X : S7) M) * (1 - (X : S7) ^ (m + 1)) - qpoch (X : S7) M * (X : S7) ^ (m + 1) := by ring
    rw [h1]
    apply dvd_sub
    · exact dvd_mul_of_dvd_left ih _
    · apply dvd_mul_of_dvd_right
      apply pow_dvd_pow _
      have : d ≤ m := Nat.le_trans hM n
      omega

/-- A finite subproduct containing all factors of low order agrees with `qpoch` to high order. -/
lemma prod_congr_qpoch (d : ℕ) (s : Finset ℕ) (hs : range d ⊆ s) :
    (X : S7) ^ (d + 1) ∣ ((∏ i ∈ s, (1 - (X : S7) ^ (i + 1))) - qpoch (X : S7) d) := by
  have heq : ∏ i ∈ s, (1 - (X : S7) ^ (i + 1)) = qpoch (X : S7) d * ∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1)) := by
    rw [← Finset.prod_sdiff hs]
    simp [qpoch, mul_comm]
  rw [heq]
  have h2 : qpoch (X : S7) d * ∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1)) - qpoch (X : S7) d =
            qpoch (X : S7) d * (∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1)) - 1) := by ring
  rw [h2]
  have h3 : X ^ (d + 1) ∣ (∏ i ∈ s \ range d, (1 - (X : S7) ^ (i + 1))) - 1 := by
    apply prod_factors_congr_one d _ (fun i hi => Nat.le_of_not_lt fun h => Finset.mem_sdiff.mp hi |>.2 (Finset.mem_range.mpr h))
  exact dvd_mul_of_dvd_right h3 _

lemma tendsto_coeff_EE (m : ℕ) :
    Filter.Tendsto (fun s : Finset ℕ => (coeff m) (∏ i ∈ s, (1 - (X : S7) ^ (i + 1))))
      Filter.atTop (nhds ((coeff m) EE)) :=
  ((PowerSeries.WithPiTopology.continuous_coeff (ZMod 7) m).tendsto EE).comp hasProd_EE

/-- Truncated products of `1 - X^i` approximate `EE`. -/
lemma coeff_EE_eq (m N : ℕ) (h : m ≤ N) : (coeff m) EE = (coeff m) (qpoch (X : S7) N) := by
  have key : ∀ s : Finset ℕ, range N ⊆ s →
      (coeff m) (∏ i ∈ s, (1 - (X : S7) ^ (i + 1))) = (coeff m) (qpoch (X : S7) N) :=
    fun s hs => ((dvd_iff_coeff N _ _).mp (prod_congr_qpoch N s hs)) m h
  have h2 : Filter.Tendsto (fun s : Finset ℕ => (coeff m) (∏ i ∈ s, (1 - (X : S7) ^ (i + 1))))
      Filter.atTop (nhds ((coeff m) (qpoch (X : S7) N))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (range N)] with s hs
    exact (key s hs).symm
  exact tendsto_nhds_unique (tendsto_coeff_EE m) h2

lemma EE_congr (d N : ℕ) (h : d ≤ N) : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) N - EE) := by
  rw [dvd_iff_coeff]
  intro m hm
  exact (coeff_EE_eq m N (le_trans hm h)).symm

/-- `EE` may be cancelled in congruences, since `PP * EE = 1`. -/
lemma dvd_of_dvd_mul_EE {N : ℕ} {f g : S7} (h : (X : S7) ^ N ∣ (f * EE - g * EE)) :
    (X : S7) ^ N ∣ (f - g) := by
  have h2 : (X : S7) ^ N ∣ ((f * EE - g * EE) * PP) := h.mul_right PP
  have : (f * EE - g * EE) * PP = f - g := by
    have hE : EE * PP = 1 := by rw [mul_comm]; exact PP_mul_EE
    calc (f * EE - g * EE) * PP = f * (EE * PP) - g * (EE * PP) := by ring
    _ = f - g := by rw [hE]; ring
  rwa [this] at h2

/-- Gaussian binomial coefficients approximate the partition series. -/
lemma qb_congr (d m k : ℕ) (hk : d ≤ k) (hkm : k ≤ m) (hmk : d ≤ m - k) :
    (X : S7) ^ (d + 1) ∣ (qb (X : S7) m k - PP) := by
  set B := qb (X : S7) m k with hB
  have hprod := qb_mul_qpoch (X : S7) hkm
  have h1 : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) k - EE) := EE_congr d k hk
  have h2 : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) (m - k) - EE) := EE_congr d (m - k) hmk
  have h3 : (X : S7) ^ (d + 1) ∣ (qpoch (X : S7) m - EE) := EE_congr d m (hk.trans hkm)
  have e0 : (X : S7) ^ (d + 1) ∣ (B - B) := by simp
  have h4 : (X : S7) ^ (d + 1) ∣ (B * qpoch (X : S7) k * qpoch (X : S7) (m - k) - B * EE * EE) :=
    dvd_sub_mul (dvd_sub_mul e0 h1) h2
  rw [hprod] at h4
  have h5 : (X : S7) ^ (d + 1) ∣ (B * EE * EE - EE) := by
    have hd := dvd_sub h3 h4
    have heq : (qpoch (X : S7) m - EE) - (qpoch (X : S7) m - B * EE * EE) = B * EE * EE - EE := by
      ring
    rwa [heq] at hd
  have hEE : PP * EE * EE = EE := by rw [PP_mul_EE, one_mul]
  have h6 : (X : S7) ^ (d + 1) ∣ (B * EE * EE - PP * EE * EE) := by rw [hEE]; exact h5
  exact dvd_of_dvd_mul_EE (dvd_of_dvd_mul_EE h6)

/-- Partial sums of the Jacobi series approximate `JJ`. -/
lemma Jpart_congr (d n : ℕ) (h : d < tri n) : (X : S7) ^ (d + 1) ∣ (Jpart n - JJ) := by
  rw [dvd_iff_coeff]
  intro m hm
  simp only [JJ, PowerSeries.coeff_mk]
  -- We need to show coeff m (Jpart n) = jcoef m
  -- jcoef m = ∑ j ∈ range (m+1), if tri j = m then (-1)^j * (2*j+1) else 0
  rw [jcoef, Jpart]
  simp
  -- coeff m (a * X ^ k) = coeff (m - k) a when m >= k, else 0
  -- Let's prove the coefficient simplification
  have coeff_term : ∀ x m : ℕ, (coeff m) (C ((-1 : ZMod 7) ^ x * (2 * x + 1)) * X ^ tri x) =
      if m = tri x then (-1 : ZMod 7) ^ x * (2 * x + 1) else 0 := by
    intro x m
    rw [PowerSeries.coeff_C_mul_X_pow]
  -- The sum over range (m+1) equals sum over range n because:
  -- 1. For x ≥ m+1: tri x ≥ x > m, so term is 0
  -- 2. For x ≥ n: tri x ≥ tri n > d ≥ m, so term is 0
  have h1 : ∀ x, x ≥ m + 1 → (if m = tri x then (-1 : ZMod 7) ^ x * (2 * x + 1) else 0) = 0 := by
    intro x hx
    simp only [ite_eq_right_iff]
    intro heq
    have : x ≤ tri x := self_le_tri x
    omega
  have h2 : ∀ x, x ≥ n → (if m = tri x then (-1 : ZMod 7) ^ x * (2 * x + 1) else 0) = 0 := by
    intro x hx
    simp only [ite_eq_right_iff]
    intro heq
    have htri : tri n ≤ tri x := tri_strictMono.monotone hx
    by_cases heq2 : x = n
    · rw [heq2] at heq; omega
    · have : n < x := lt_of_le_of_ne hx (Ne.symm heq2)
      have htri' : tri n < tri x := tri_strictMono this
      omega
  -- Both sums equal sum over range (max n (m+1))
  set N := max n (m + 1)
  have lhs_eq := Finset.sum_subset (Finset.range_mono (le_max_left n (m + 1)))
    (fun x _ hx => h2 x (Nat.not_lt.mp (Finset.mem_range.not.mp hx)))
  have rhs_eq := Finset.sum_subset (Finset.range_mono (le_max_right n (m + 1)))
    (fun x _ hx => h1 x (Nat.not_lt.mp (Finset.mem_range.not.mp hx)))
  have hconvert : ∀ x ∈ range n, ((-1 : S7) ^ x * (C (2 : ZMod 7) * (x : S7) + 1) * X ^ tri x) =
                       C ((-1 : ZMod 7) ^ x * (2 * (x : ZMod 7) + 1)) * X ^ tri x := by
    intro x _
    have : ((-1 : S7) ^ x * (C (2 : ZMod 7) * (x : S7) + 1)) = C ((-1 : ZMod 7) ^ x * (2 * (x : ZMod 7) + 1)) := by
      simp [mul_add, mul_comm]
    rw [this]
  rw [Finset.sum_congr rfl (fun x hx => by rw [hconvert x hx]),
      Finset.sum_congr rfl (fun x hx => coeff_term x m), lhs_eq, ← rhs_eq]
  simp_rw [eq_comm]

/-- A congruence between two terms of the key sums, from a congruence of the factors. -/
lemma term_dvd_of_dvd (d e : ℕ) (c A B : S7) (h : (X : S7) ^ (d + 1) ∣ (A - B)) :
    (X : S7) ^ (d + 1) ∣ (c * (X ^ e * A) - c * (X ^ e * B)) := by
  have hrw : c * ((X : S7) ^ e * A) - c * (X ^ e * B) = (c * X ^ e) * (A - B) := by ring
  rw [hrw]
  exact h.mul_left _

/-- A congruence between two terms of the key sums, from a high power of `X`. -/
lemma term_dvd_of_high (d e : ℕ) (he : d + 1 ≤ e) (c A B : S7) :
    (X : S7) ^ (d + 1) ∣ (c * (X ^ e * A) - c * (X ^ e * B)) := by
  have hrw : c * ((X : S7) ^ e * A) - c * (X ^ e * B) = X ^ e * (c * (A - B)) := by ring
  rw [hrw]
  exact (pow_dvd_pow (X : S7) he).mul_right _

/-- The first sum of `key_split`, with the Gaussian binomials replaced by `PP`. -/
lemma key_sumA_congr (d N : ℕ) (hN : 2 * d + 2 ≤ N) :
    (X : S7) ^ (d + 1) ∣
      (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7))
          * (X ^ tri j * qb (X : S7) (2 * N) (N + j))
        - ∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * PP)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  by_cases hcase : j ≤ N - d
  · exact term_dvd_of_dvd _ _ _ _ _
      (qb_congr d (2 * N) (N + j) (by omega) (by omega) (by omega))
  · refine term_dvd_of_high _ _ ?_ _ _ _
    have := self_le_tri j
    omega

/-- The second sum of `key_split`, with the Gaussian binomials replaced by `PP`. -/
lemma key_sumB_congr (d N : ℕ) (hN : 2 * d + 2 ≤ N) :
    (X : S7) ^ (d + 1) ∣
      (∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1))
          * (X ^ tri j * qb (X : S7) (2 * N) (N - 1 - j))
        - ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * PP)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  by_cases hcase : j ≤ N - 1 - d
  · exact term_dvd_of_dvd _ _ _ _ _
      (qb_congr d (2 * N) (N - 1 - j) (by omega) (by omega) (by omega))
  · refine term_dvd_of_high _ _ ?_ _ _ _
    have := self_le_tri j
    omega

/-- The two `PP`-sums combine into `- Jpart N * PP`, up to a term of high order. -/
lemma key_sums_eq (N : ℕ) :
    (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * PP)
      + ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * PP))
      = (- Jpart N + ((-1 : S7) ^ (N + 1) * (N : S7)) * X ^ tri N) * PP := by
  simp only [Jpart, Finset.sum_range_succ]
  -- Rearrange and combine sums
  rw [add_comm, ← add_assoc]
  rw [← Finset.sum_add_distrib]
  -- Simplify each term in the sum
  have hterm : ∀ x ∈ range N, ((-1 : S7) ^ (x + 1) * ((x : S7) + 1) * (X ^ tri x * PP) +
      (-1 : S7) ^ (x + 1) * (x : S7) * (X ^ tri x * PP)) =
      -(C ((-1 : ZMod 7) ^ x * (2 * (x : ZMod 7) + 1)) * X ^ tri x * PP) := by
    intro x _
    noncomm_ring
    simp [mul_assoc, mul_comm, mul_left_comm]
    abel_nf
    simp [mul_add]
    simp [show (2 : S7) = C (2 : ZMod 7) by rfl, mul_comm (C (2 : ZMod 7))]
    have h1 : (-1 : S7) ^ x = C ((-1 : ZMod 7) ^ x) := by simp [map_pow]
    rw [h1]
    simp [mul_comm, mul_left_comm]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_neg_distrib]
  conv_lhs => rw [← Finset.sum_mul]
  ring

/-- The heart of the limiting argument. -/
lemma key_congr (d : ℕ) : (X : S7) ^ (d + 1) ∣ (Jpart (2 * d + 2) * PP - EE ^ 2) := by
  -- Use N = 2*d + 2, which satisfies 2*d + 2 ≤ N trivially
  set N := 2 * d + 2 with hN_def
  -- N is even
  have heven : Even N := ⟨d + 1, by omega⟩
  -- We need high-order congruences; 2*d + 2 ≤ N is trivially true
  have hND : 2 * d + 2 ≤ N := le_refl _
  have hA := key_sumA_congr d N hND
  have hB := key_sumB_congr d N hND
  -- Combine hA and hB: the qb-sums are close to the PP-sums
  have hAB : (X : S7) ^ (d + 1) ∣
      (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * qb (X : S7) (2 * N) (N + j))
        + ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * qb (X : S7) (2 * N) (N - 1 - j)))
      - (∑ j ∈ range (N + 1), ((-1 : S7) ^ (j + 1) * (j : S7)) * (X ^ tri j * PP)
        + ∑ j ∈ range N, ((-1 : S7) ^ (j + 1) * ((j : S7) + 1)) * (X ^ tri j * PP)) := by
    convert dvd_add hA hB using 1; ring
  -- Use key_split to express qb-sums in terms of cc
  have hsplit := key_split (X : S7) N heven
  -- Use key_sums_eq to simplify PP-sums
  have hsums := key_sums_eq N
  -- Use fjtp_key to express the cc-sum
  have hNpos : 0 < N := by omega
  have hfjtp := fjtp_key (X : S7) N hNpos
  -- Rewrite hAB using hsplit and hfjtp
  rw [← hsplit, hfjtp] at hAB
  -- Rewrite hAB using hsums
  rw [hsums] at hAB
  -- hAB : X^(d+1) ∣ (-1)^(N+1) * qpoch * qpoch - (-Jpart N + term) * PP
  --      = (-1)^(N+1) * qpoch * qpoch + Jpart N * PP - term * PP
  have hAB' : (X : S7) ^ (d + 1) ∣
      Jpart N * PP + ((-1 : S7) ^ (N + 1)) * (qpoch (X : S7) N * qpoch (X : S7) (N - 1))
      - ((-1 : S7) ^ (N + 1)) * (N : S7) * X ^ tri N * PP := by
    convert hAB using 1; ring
  -- N = 2*d + 2 is even, so (-1)^(N+1) = -1
  have hN_even : Even N := heven
  have hNp1_odd : Odd (N + 1) := hN_even.add_odd (by decide : Odd 1)
  have hsign : ((-1 : S7) ^ (N + 1)) = -1 := by
    rw [neg_one_pow_eq_pow_mod_two]; simp [Nat.odd_iff.mp hNp1_odd]
  rw [hsign] at hAB'
  -- hAB' : X^(d+1) ∣ Jpart N * PP + (-1) * qpoch * qpoch - (-1) * N * X^tri N * PP
  --       = Jpart N * PP - qpoch * qpoch + N * X^tri N * PP
  have hAB'' : (X : S7) ^ (d + 1) ∣ Jpart N * PP - qpoch (X : S7) N * qpoch (X : S7) (N - 1)
      + (N : S7) * X ^ tri N * PP := by convert hAB' using 1; ring
  -- tri N = N*(N+1)/2 = (2*d+2)*(2*d+3)/2 = (d+1)*(2*d+3) ≥ d+1
  have htri : tri N ≥ d + 1 := by
    simp only [tri]
    rw [hN_def]
    have h1 : (2 * d + 2) * (2 * d + 2 + 1) = 2 * (d + 1) * (2 * d + 3) := by ring
    have h2 : 2 * (d + 1) * (2 * d + 3) / 2 = (d + 1) * (2 * d + 3) := by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [h1, h2]
    have : (d + 1) * (2 * d + 3) ≥ d + 1 := Nat.le_mul_of_pos_right _ (by omega)
    exact this
  -- N * X^tri N * PP is divisible by X^(d+1)
  have hterm : (X : S7) ^ (d + 1) ∣ (N : S7) * X ^ tri N * PP := by
    have : (X : S7) ^ (d + 1) ∣ X ^ tri N := pow_dvd_pow _ htri
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this (N : S7)) PP
  -- qpoch N * qpoch (N-1) ≈ EE^2 (mod X^(d+1))
  have hN_ge_d : d ≤ N := by omega
  have hN1_ge_d : d ≤ N - 1 := by omega
  have hEE_N := EE_congr d N hN_ge_d
  have hEE_N1 := EE_congr d (N - 1) hN1_ge_d
  -- qpoch N * qpoch (N-1) - EE^2 = qpoch N * (qpoch (N-1) - EE) + EE * (qpoch N - EE)
  have hEE_sq : (X : S7) ^ (d + 1) ∣ qpoch (X : S7) N * qpoch (X : S7) (N - 1) - EE ^ 2 := by
    have h1 : qpoch (X : S7) N * qpoch (X : S7) (N - 1) - EE ^ 2 =
        qpoch (X : S7) N * (qpoch (X : S7) (N - 1) - EE) + EE * (qpoch (X : S7) N - EE) := by ring
    rw [h1]
    exact dvd_add (dvd_mul_of_dvd_right hEE_N1 _) (dvd_mul_of_dvd_right hEE_N _)
  -- Combine: (Jpart N * PP - qpoch N * qpoch (N-1)) = (divisible) - term
  have h1 : (X : S7) ^ (d + 1) ∣ Jpart N * PP - qpoch (X : S7) N * qpoch (X : S7) (N - 1) := by
    have := dvd_sub hAB'' hterm
    convert this using 1; ring
  -- Now: Jpart N * PP - EE^2 = (Jpart N * PP - qpoch N * qpoch (N-1)) + (qpoch N * qpoch (N-1) - EE^2)
  have h2 : (X : S7) ^ (d + 1) ∣ Jpart N * PP - EE ^ 2 := by
    have := dvd_add h1 hEE_sq
    convert this using 1; ring
  exact h2

lemma JJ_mul_PP_congr (d : ℕ) : (X : S7) ^ (d + 1) ∣ (JJ * PP - EE ^ 2) := by
  have hJ : (X : S7) ^ (d + 1) ∣ (Jpart (2 * d + 2) - JJ) :=
    Jpart_congr d (2 * d + 2) (by have := self_le_tri (2 * d + 2); omega)
  have h1 : (X : S7) ^ (d + 1) ∣ (JJ * PP - Jpart (2 * d + 2) * PP) := by
    have h2 := hJ.mul_right PP
    have h3 : (Jpart (2 * d + 2) - JJ) * PP = -(JJ * PP - Jpart (2 * d + 2) * PP) := by ring
    rw [h3, dvd_neg] at h2
    exact h2
  have h4 := dvd_add h1 (key_congr d)
  have h5 : (JJ * PP - Jpart (2 * d + 2) * PP) + (Jpart (2 * d + 2) * PP - EE ^ 2)
      = JJ * PP - EE ^ 2 := by ring
  rwa [h5] at h4

lemma JJ_mul_PP : JJ * PP = EE ^ 2 := by
  ext d
  have := (dvd_iff_coeff d (JJ * PP) (EE ^ 2)).mp (JJ_mul_PP_congr d)
  exact this d le_rfl

/-- Jacobi's identity `E^3 = ∑ (-1)^j (2j+1) X^{T_j}`. -/
theorem jacobi_cube : JJ = EE ^ 3 := by
  have h := JJ_mul_PP
  have h2 : JJ * (PP * EE) = EE ^ 2 * EE := by rw [← mul_assoc, h]
  rw [PP_mul_EE, mul_one] at h2
  rw [h2]
  ring

/-! ### Characteristic 7 -/

/-- A power series supported in degrees divisible by `7`. -/
def Supp7 (f : S7) : Prop := ∀ m : ℕ, ¬ (7 ∣ m) → (coeff m) f = 0

lemma Supp7.mul {f g : S7} (hf : Supp7 f) (hg : Supp7 g) : Supp7 (f * g) := by
  intro m hm
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  have hp' : p.1 + p.2 = m := hp
  have : ¬(7 ∣ p.1) ∨ ¬(7 ∣ p.2) := by
    by_contra h
    push_neg at h
    apply hm
    exact ⟨h.1.choose + h.2.choose, by linarith [h.1.choose_spec, h.2.choose_spec]⟩
  cases this with
  | inl hi => simp [hf p.1 hi]
  | inr hj => simp [hg p.2 hj]

lemma Supp7_one : Supp7 (1 : S7) := by
  intro m hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm ⟨0, rfl⟩
  simp [PowerSeries.coeff_one, hm0]

lemma Supp7_one_sub (k : ℕ) : Supp7 (1 - (X : S7) ^ (7 * (k + 1))) := by
  intro m hm
  have h0 : m ≠ 0 := by rintro rfl; exact hm ⟨0, rfl⟩
  have h7 : m ≠ 7 * (k + 1) := by rintro rfl; exact hm ⟨k + 1, rfl⟩
  simp [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, h0, h7]

lemma Supp7_prod (N : ℕ) : Supp7 (∏ i ∈ range N, (1 - (X : S7) ^ (7 * (i + 1)))) := by
  induction N with
  | zero => simpa using Supp7_one
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact ih.mul (Supp7_one_sub n)

noncomputable local instance charP_S7 : CharP S7 7 :=
  charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod 7)) 7

local instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

local instance expChar_S7 : ExpChar S7 7 := ExpChar.prime (by norm_num)

lemma sub_pow_seven (a b : S7) : (a - b) ^ 7 = a ^ 7 - b ^ 7 := sub_pow_char a b

lemma qpoch_pow_seven (N : ℕ) :
    (qpoch (X : S7) N) ^ 7 = ∏ i ∈ range N, (1 - (X : S7) ^ (7 * (i + 1))) := by
  rw [qpoch, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sub_pow_char, one_pow, ← pow_mul, mul_comm (i + 1) 7]

/-- In characteristic `7`, `E^7` is supported in degrees divisible by `7`. -/
lemma coeff_EE_pow_seven (b : ℕ) (hb : ¬ (7 ∣ b)) : (coeff b) (EE ^ 7) = 0 := by
  have h1 : (X : S7) ^ (b + 1) ∣ (qpoch (X : S7) b - EE) := EE_congr b b le_rfl
  have h2 := dvd_sub_pow (N := b + 1) 7 h1
  have h3 : (coeff b) ((qpoch (X : S7) b) ^ 7) = (coeff b) (EE ^ 7) :=
    ((dvd_iff_coeff b _ _).mp h2) b le_rfl
  rw [← h3, qpoch_pow_seven]
  exact Supp7_prod b b hb

lemma constantCoeff_EE_pow_seven : (coeff 0) (EE ^ 7) = 1 := by
  have h0 : (coeff 0) EE = 1 := by
    have h := coeff_EE_eq 0 0 le_rfl
    simpa [qpoch] using h
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at h0 ⊢
  rw [map_pow, h0, one_pow]

/-! ### The arithmetic of the coefficients of `J²` -/

lemma two_mul_tri (m : ℕ) : 2 * tri m = m * (m + 1) := by
  induction m with
  | zero => simp [tri]
  | succ n ih =>
    rw [tri_succ, Nat.mul_add, ih]
    ring

lemma sq_add_sq_eq_zero_mod7 (x y : ZMod 7) (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  revert x y
  decide

lemma jcoef_eq_zero_of (m : ℕ) (h : ∀ j, tri j ≠ m) : jcoef m = 0 := by
  unfold jcoef
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [h j]

lemma jcoef_eq (m j : ℕ) (h : tri j = m) : jcoef m = (-1 : ZMod 7) ^ j * (2 * j + 1) := by
  have hjm : j ≤ m := h ▸ self_le_tri j
  unfold jcoef
  rw [Finset.sum_eq_single j]
  · simp [h]
  · intro b _ hbj
    have : tri b ≠ m := fun hb => hbj (tri_injective (hb.trans h.symm))
    simp [this]
  · intro hj
    exact absurd (Finset.mem_range.mpr (by omega)) hj

/-- `8 T_i + 1 = (2i+1)^2`. -/
lemma eight_tri_add_one (i : ℕ) : 8 * tri i + 1 = (2 * i + 1) ^ 2 := by
  have h := two_mul_tri i
  nlinarith [h]

/-- If `2i+1` vanishes mod `7` then the `T_i`-th Jacobi coefficient vanishes. -/
lemma jcoef_eq_zero_of_cast (i : ℕ) (h : ((2 * i + 1 : ℕ) : ZMod 7) = 0) : jcoef (tri i) = 0 := by
  rw [jcoef_eq (tri i) i rfl]
  push_cast at h
  rw [h, mul_zero]

lemma coeff_JJ_sq_term (a b : ℕ) (hab : (a + b) % 7 = 5) : jcoef a * jcoef b = 0 := by
  by_cases ha : ∀ i, tri i ≠ a
  · rw [jcoef_eq_zero_of a ha]
    ring
  · push_neg at ha
    obtain ⟨i, hi⟩ := ha
    by_cases hb : ∀ j, tri j ≠ b
    · rw [jcoef_eq_zero_of b hb]
      ring
    · push_neg at hb
      obtain ⟨j, hj⟩ := hb
      rw [jcoef_eq a i hi, jcoef_eq b j hj]
      -- Need to show (-1)^i * (2*i+1) * ((-1)^j * (2*j+1)) = 0
      -- Key: (2*i+1)^2 + (2*j+1)^2 ≡ 0 (mod 7)
      have hmod : (8 * (a + b) + 2) % 7 = 0 := by omega
      have h1 : (8 : ℕ) * tri i + 1 = (2 * i + 1) ^ 2 := eight_tri_add_one i
      have h2 : (8 : ℕ) * tri j + 1 = (2 * j + 1) ^ 2 := eight_tri_add_one j
      have key : ((2 * i + 1 : ℕ) : ZMod 7) ^ 2 + ((2 * j + 1 : ℕ) : ZMod 7) ^ 2 = 0 := by
        have hsum : ((8 * tri i + 1) + (8 * tri j + 1) : ℕ) = 8 * (a + b) + 2 := by rw [hi, hj]; ring
        rw [h1, h2] at hsum
        norm_cast
        have hdiv : (7 : ℕ) ∣ (2 * i + 1) ^ 2 + (2 * j + 1) ^ 2 := by omega
        exact (ZMod.natCast_eq_zero_iff ((2 * i + 1) ^ 2 + (2 * j + 1) ^ 2) 7).mpr hdiv
      -- In ZMod 7, x^2 + y^2 = 0 implies x = 0 or y = 0
      have forbid : ∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∨ y = 0 := by decide
      rcases forbid _ _ key with hx | hy
      · simp_all
      · simp_all

/-- The coefficients of `J^2` in degrees `≡ 5 (mod 7)` vanish. -/
lemma coeff_JJ_sq (m : ℕ) (hm : m % 7 = 5) : (coeff m) (JJ ^ 2) = 0 := by
  rw [sq, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  simp only [JJ, PowerSeries.coeff_mk]
  exact coeff_JJ_sq_term p.1 p.2 (by rw [hp]; exact hm)

/-! ### Conclusion -/

lemma PP_mul_EE_pow_seven : PP * EE ^ 7 = JJ ^ 2 := by
  have h : PP * EE ^ 7 = (PP * EE) * EE ^ 6 := by ring
  rw [h, PP_mul_EE, one_mul, jacobi_cube]
  ring

lemma coeff_PP_step (n : ℕ) (ih : ∀ t < n, (coeff (7 * t + 5)) PP = 0) :
    (coeff (7 * n + 5)) PP = 0 := by
  -- From PP * EE^7 = JJ^2, coeff (7*n+5) PP * EE^7 = coeff (7*n+5) JJ^2 = 0
  have heq : coeff (7 * n + 5) (PP * EE ^ 7) = coeff (7 * n + 5) (JJ ^ 2) := by
    rw [PP_mul_EE_pow_seven]
  have hzero : coeff (7 * n + 5) (JJ ^ 2) = 0 := coeff_JJ_sq _ (by omega : (7 * n + 5) % 7 = 5)
  rw [hzero] at heq
  -- Expand coeff (PP * EE^7) as a sum
  rw [PowerSeries.coeff_mul] at heq
  -- The sum only has terms where the second component is divisible by 7
  -- Since p.1 + p.2 = 7*n + 5, if 7 ∣ p.2 then p.1 ≡ 5 (mod 7)
  -- By IH, coeff p.1 PP = 0 unless p.1 = 7*n + 5 (i.e., p.2 = 0)
  rw [Finset.sum_eq_single (7 * n + 5, 0)] at heq
  · change coeff (7 * n + 5) PP * coeff 0 (EE ^ 7) = 0 at heq
    rw [constantCoeff_EE_pow_seven, mul_one] at heq
    exact heq
  · intro p hp hne
    -- p.1 + p.2 = 7*n + 5
    have hsum : p.1 + p.2 = 7 * n + 5 := Finset.mem_antidiagonal.mp hp
    by_cases hdiv : 7 ∣ p.2
    · -- If 7 ∣ p.2, then p.1 = 7*n + 5 - p.2 = 7*(n - k) + 5 for some k > 0
      obtain ⟨k, hk⟩ := hdiv
      have hkpos : 0 < k := by
        by_contra hkneg
        push_neg at hkneg
        have : p = (7 * n + 5, 0) := by
          ext <;> omega
        exact hne this
      have h1 : p.1 = 7 * (n - k) + 5 := by omega
      have hklt : n - k < n := by omega
      rw [h1, ih _ hklt, zero_mul]
    · -- If ¬ 7 ∣ p.2, then coeff p.2 (EE^7) = 0
      rw [mul_eq_zero]
      right
      exact coeff_EE_pow_seven _ hdiv
  · intro h
    exact absurd (h (by simp [Finset.mem_antidiagonal])) (by simp)

lemma coeff_PP_eq_zero (n : ℕ) : (coeff (7 * n + 5)) PP = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih => exact coeff_PP_step n fun t ht => ih t ht

end PS

/-- Ramanujan's congruence: p(7n+5) ≡ 0 (mod 7). -/
theorem ramanujan_seven (n : ℕ) : 7 ∣ Fintype.card (Nat.Partition (7 * n + 5)) := by
  have h := coeff_PP_eq_zero n
  rw [coeff_PP] at h
  exact (ZMod.natCast_eq_zero_iff _ 7).mp h

end Brockian.Ramanujan7

