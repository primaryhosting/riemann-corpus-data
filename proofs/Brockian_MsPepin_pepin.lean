import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/
private lemma fermat_mod_four (n : ℕ) (hn : 1 ≤ n) : (2 ^ (2 ^ n) + 1) % 4 = 1 := by
  have h : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
  have h2 : 4 ∣ 2 ^ (2 ^ n) := pow_dvd_pow 2 h
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd h2]

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `2` mod `3`. -/
private lemma fermat_mod_three (n : ℕ) (hn : 1 ≤ n) : (2 ^ (2 ^ n) + 1) % 3 = 2 := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  have h3 : 2 ^ (2 ^ n) = (2 ^ 2) ^ (2 ^ (n - 1)) := by rw [h2, pow_mul]
  rw [h3]
  norm_num at *
  have h4 : 4 ^ 2 ^ (n - 1) % 3 = 1 := by
    have := Nat.pow_mod 4 (2 ^ (n - 1)) 3
    simp [this]
  rw [Nat.add_mod, h4]

/-- `2` is not a square modulo `3`. -/
private lemma legendreSym_three_two : legendreSym 3 (2 : ℤ) = -1 := by decide

/-- `3` is a quadratic nonresidue modulo a prime Fermat number `F n`, `n ≥ 1`. -/
private lemma legendre_three (n : ℕ) (hn : 1 ≤ n)
    [Fact (Nat.Prime (2 ^ (2 ^ n) + 1))] :
    legendreSym (2 ^ (2 ^ n) + 1) 3 = -1 := by
  have hF4 : (2 ^ (2 ^ n) + 1) % 4 = 1 := fermat_mod_four n hn
  have hF3 : (2 ^ (2 ^ n) + 1) % 3 = 2 := fermat_mod_three n hn
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Quadratic reciprocity: `F n ≡ 1 [MOD 4]`, so `(3 / F n) = (F n / 3)`.
  have hqr : legendreSym 3 ((2 ^ (2 ^ n) + 1 : ℕ) : ℤ)
      = legendreSym (2 ^ (2 ^ n) + 1) ((3 : ℕ) : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four hF4 (by norm_num)
  -- `F n ≡ 2 [MOD 3]`, and `2` is not a square mod `3`.
  have hmod : ((2 ^ (2 ^ n) + 1 : ℕ) : ℤ) % 3 = (2 : ℤ) := by
    have : ((2 ^ (2 ^ n) + 1) % 3 : ℕ) = 2 := hF3
    omega
  have h2 : legendreSym 3 ((2 ^ (2 ^ n) + 1 : ℕ) : ℤ) = -1 := by
    rw [legendreSym.mod, show ((3 : ℕ) : ℤ) = (3 : ℤ) from by norm_num, hmod,
      legendreSym_three_two]
  rw [← show ((3 : ℕ) : ℤ) = (3 : ℤ) from by norm_num, ← hqr, h2]

/-- Forward direction of Pépin's test. -/
private lemma pepin_mp (n : ℕ) (hn : 1 ≤ n) (hp : (2 ^ (2 ^ n) + 1).Prime) :
    (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1 := by
  haveI : Fact (Nat.Prime (2 ^ (2 ^ n) + 1)) := ⟨hp⟩
  have h := legendre_three n hn
  have euler := legendreSym.eq_pow (p := 2 ^ (2 ^ n) + 1) (a := 3)
  rw [h] at euler
  have key : (2 ^ (2 ^ n) + 1) / 2 = 2 ^ (2 ^ n) / 2 := by
    have h2 : 2 ∣ 2 ^ (2 ^ n) := dvd_pow_self 2 (by positivity)
    omega
  rw [key] at euler
  simp at euler
  exact euler.symm

/-- `-1 ≠ 1` in `ZMod (F n)` for `n ≥ 1`, since `F n > 2`. -/
private lemma neg_one_ne_one_fermat (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ZMod (2 ^ (2 ^ n) + 1)) ≠ 1 := by
  have hmod : (2 : ℕ) < 2 ^ (2 ^ n) + 1 := by
    have h1 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 2 ^ 2 ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (by simpa using h1)
    omega
  haveI : Fact (2 < 2 ^ (2 ^ n) + 1) := ⟨hmod⟩
  exact ZMod.neg_one_ne_one

/-- If `3 ^ (F n / 2) = -1` then `3 ^ (F n - 1) = 1`. -/
private lemma pow_fermat_sub_one (n : ℕ)
    (h : (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1) :
    (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) + 1 - 1) = 1 := by
  have hsplit : 2 ^ (2 ^ n) + 1 - 1 = 2 ^ (2 ^ n) / 2 + 2 ^ (2 ^ n) / 2 := by
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ (2 ^ n) := dvd_pow_self 2 (by positivity)
    omega
  rw [hsplit, pow_add, h]
  ring

/-- The only prime dividing `F n - 1 = 2 ^ (2 ^ n)` is `2`, and
`3 ^ ((F n - 1) / 2) = -1 ≠ 1`. -/
private lemma pow_prime_div_ne_one (n : ℕ) (hn : 1 ≤ n)
    (h : (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1) :
    ∀ q : ℕ, q.Prime → q ∣ (2 ^ (2 ^ n) + 1 - 1) →
      (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ ((2 ^ (2 ^ n) + 1 - 1) / q) ≠ 1 := by
  intro q hq hdiv
  -- q divides 2^(2^n), so q = 2
  have hq2 : q = 2 := by
    have hdvd2pow : q ∣ 2 ^ (2 ^ n) := by simpa using hdiv
    have hdvd2 : q ∣ 2 := hq.dvd_of_dvd_pow hdvd2pow
    have := Nat.le_of_dvd (by norm_num) hdvd2
    interval_cases q <;> trivial
  rw [hq2]
  -- Now the exponent is 2^(2^n) / 2
  simp_all
  exact neg_one_ne_one_fermat n hn

/-- Backward direction of Pépin's test (Lucas primality with witness `3`). -/
private lemma pepin_mpr (n : ℕ) (hn : 1 ≤ n)
    (h : (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1) :
    (2 ^ (2 ^ n) + 1).Prime :=
  lucas_primality (2 ^ (2 ^ n) + 1) 3 (pow_fermat_sub_one n h)
    (pow_prime_div_ne_one n hn h)

/-- Pépin's test: the Fermat number F_n = 2^(2^n)+1 (n ≥ 1) is prime iff
    3^((F_n−1)/2) ≡ −1 (mod F_n). -/
theorem pepin (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ (2 ^ n) + 1).Prime ↔
      (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1 :=
  ⟨pepin_mp n hn, pepin_mpr n hn⟩

end Brockian.MsPepin

