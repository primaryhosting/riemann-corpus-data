import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/
private def A (p : ℕ) : ℕ := 2 ^ p - 1

/-- `B p = (2 ^ p + 1) / 3`. -/
private def B (p : ℕ) : ℕ := (2 ^ p + 1) / 3

/-- `N p = (4 ^ p - 1) / 3`, written as a product. -/
private def N (p : ℕ) : ℕ := A p * B p

private lemma three_mul_B (p : ℕ) (hp : Odd p) : 3 * B p = 2 ^ p + 1 := by
  have h : 3 ∣ 2 ^ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    obtain ⟨k, rfl⟩ := hp
    norm_num [Nat.add_mod, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  rw [B, Nat.mul_div_cancel' h]

private lemma three_mul_N (p : ℕ) (hp : Odd p) : 3 * N p + 1 = 4 ^ p := by
  rw [N, mul_comm (A p) (B p), ← mul_assoc, three_mul_B p hp, A]
  have key : (2 ^ p + 1) * (2 ^ p - 1) = 4 ^ p - 1 := by
    have h4 : (4 : ℕ) ^ p = 2 ^ p * 2 ^ p := by
      rw [← Nat.pow_add, ← two_mul, pow_mul]; norm_num
    obtain ⟨y, hy⟩ : ∃ y, 2 ^ p = y + 1 :=
      ⟨2 ^ p - 1, by have := Nat.one_le_pow p 2 (by norm_num); omega⟩
    have hkey : (y + 1) * (y + 1) = (y + 1 + 1) * y + 1 := by ring
    rw [h4, hy, Nat.add_sub_cancel]
    omega
  rw [key]
  exact Nat.sub_add_cancel (Nat.one_le_pow p 4 (by norm_num))

private lemma one_lt_A {p : ℕ} (hp : 5 ≤ p) : 1 < A p := by
  show 1 < 2 ^ p - 1
  have : 2 ^ p ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hp
  omega

private lemma one_lt_B {p : ℕ} (hp : 5 ≤ p) : 1 < B p := by
  show 1 < (2 ^ p + 1) / 3
  have : 2 ^ p ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hp
  omega

private lemma one_lt_N {p : ℕ} (hp : 5 ≤ p) : 1 < N p := by
  have ha := one_lt_A hp
  have hb := one_lt_B hp
  rw [N]
  nlinarith

private lemma N_not_prime {p : ℕ} (hp : 5 ≤ p) : ¬ (N p).Prime := by
  unfold N
  show ¬ (A p * B p).Prime
  by_contra h
  have hAp : 1 < A p := one_lt_A hp
  have hBp : 1 < B p := one_lt_B hp
  exact Nat.not_prime_mul (by omega : A p ≠ 1) (by omega : B p ≠ 1) h

private lemma lt_N {p : ℕ} (hp : 5 ≤ p) : p < N p := by
  have hb := one_lt_B hp
  have h2p : p + 2 ≤ 2 ^ p :=
    Nat.le_induction (by norm_num) (fun k _ ih => by rw [pow_succ]; omega) p hp
  have h1 : p < A p := by rw [A]; omega
  rw [N]
  nlinarith

private lemma N_odd (p : ℕ) (hp : Odd p) : Odd (N p) := by
  rw [N, A, B]
  have hp1 : 1 ≤ p := hp.pos
  have h2p_even : Even (2 ^ p) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hAp_odd : Odd (2 ^ p - 1) := by
    rw [← Nat.not_even_iff_odd, Nat.even_sub (Nat.one_le_pow p 2 (by norm_num))]
    simp [h2p_even]
  have hBp_odd : Odd ((2 ^ p + 1) / 3) := by
    have h := three_mul_B p hp
    rw [B] at h
    have hodd2 : Odd (2 ^ p + 1) := by
      obtain ⟨k, hk⟩ := h2p_even
      exact ⟨k, by omega⟩
    obtain ⟨m, hm⟩ := hodd2
    rw [← h] at hm
    exact ⟨m / 3, by omega⟩
  exact hAp_odd.mul hBp_odd

/-- `p ∣ N p - 1`, coming from Fermat's little theorem `4 ^ p ≡ 4 [MOD p]`. -/
private lemma p_dvd_N_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p ∣ N p - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h3N : 3 * N p + 1 = 4 ^ p := three_mul_N p hodd
  have h1 : 1 ≤ N p := le_of_lt (one_lt_N h5)
  have h2 : 3 * (N p - 1) = 4 ^ p - 4 := by omega
  have h4 : p ∣ 4 ^ p - 4 := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have h4p : 4 ≤ 4 ^ p := Nat.le_self_pow hp.ne_zero 4
    have hmod : (4 : ℕ) ≡ 4 ^ p [MOD p] := by
      refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
      push_cast
      exact (ZMod.pow_card (4 : ZMod p)).symm
    exact (Nat.modEq_iff_dvd' h4p).mp hmod
  have hdiv3 : p ∣ 3 * (N p - 1) := h2 ▸ h4
  have hgcd : Nat.Coprime p 3 :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  exact hgcd.dvd_of_dvd_mul_left hdiv3

private lemma two_p_dvd_N_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : 2 * p ∣ N p - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 : 2 ∣ N p - 1 := by
    have hNodd : Odd (N p) := N_odd p hodd
    obtain ⟨k, hk⟩ := hNodd
    use k
    rw [hk]
    simp
  have hcoprime : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two (by omega))
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcoprime h2 (p_dvd_N_sub_one hp h5)

private lemma N_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ∃ k, N p = 2 * p * k + 1 := by
  obtain ⟨k, hk⟩ := two_p_dvd_N_sub_one hp h5
  have hN : 1 < N p := one_lt_N h5
  exact ⟨k, by omega⟩

/-- `4 ^ p ≡ 1 [MOD N p]`, since `4 ^ p = 3 * N p + 1`. -/
private lemma four_pow_modEq {p : ℕ} (hp : Odd p) : 4 ^ p ≡ 1 [MOD N p] := by
  have h := three_mul_N p hp
  exact Nat.ModEq.symm (Nat.modEq_of_dvd ⟨3, by omega⟩)

/-- The order of `2` divides `2 * p` modulo `N p`. -/
private lemma two_pow_two_mul_modEq {p : ℕ} (hp : Odd p) : 2 ^ (2 * p) ≡ 1 [MOD N p] := by
  have h : 2 ^ (2 * p) = 4 ^ p := by rw [pow_mul]; norm_num
  rw [h]
  exact four_pow_modEq hp

/-- The key congruence: `2 ^ (N p) ≡ 2 [MOD N p]`. -/
private lemma pow_N_modEq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    2 ^ (N p) ≡ 2 [MOD N p] := by
  obtain ⟨k, hk⟩ := N_eq hp h5
  have h2p : 2 ^ (2 * p) ≡ 1 [MOD N p] := two_pow_two_mul_modEq (hp.odd_of_ne_two (by omega))
  calc 2 ^ (N p) = 2 ^ (2 * p * k + 1) := by rw [hk]
    _ = (2 ^ (2 * p)) ^ k * 2 := by ring
    _ ≡ 1 ^ k * 2 [MOD N p] := by gcongr
    _ = 2 := by ring

/-- Cipolla: there are infinitely many Fermat pseudoprimes to base 2
    (composite n > 1 with 2^n ≡ 2 mod n). -/
theorem infinite_pseudoprimes_base_two :
    {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ 2 ^ n ≡ 2 [MOD n]}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (max (a + 1) 5)
  have h5 : 5 ≤ p := le_trans (le_max_right _ _) hpa
  have hap : a < p := lt_of_lt_of_le (Nat.lt_succ_self a) (le_trans (le_max_left _ _) hpa)
  exact ⟨N p, ⟨N_not_prime h5, one_lt_N h5, pow_N_modEq hp h5⟩,
    lt_trans hap (lt_N h5)⟩

end Brockian.PseudoprimesBaseTwo

