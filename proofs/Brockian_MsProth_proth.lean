import Mathlib
namespace Brockian.MsProth

open Nat in
/-- If `d ∣ k * 2 ^ n` and `2 ^ n ∤ d`, then already `d ∣ k * 2 ^ (n - 1)`. -/
private lemma dvd_half_of_not_two_pow_dvd {k n d : ℕ} (hn : 1 ≤ n)
    (hd : d ∣ k * 2 ^ n) (h2 : ¬ (2 ^ n ∣ d)) : d ∣ k * 2 ^ (n - 1) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact h2 (dvd_zero _)
  have hsn : d.factorization 2 < n := by
    by_contra h
    push_neg at h
    exact h2 (dvd_trans (pow_dvd_pow 2 h) (Nat.ordProj_dvd d 2))
  have hodd : Odd (ordCompl[2] d) :=
    Nat.odd_iff.mpr (Nat.not_even_iff.mp
      (fun he => Nat.not_dvd_ordCompl Nat.prime_two hd0 he.two_dvd))
  have hcop : Nat.Coprime (ordCompl[2] d) (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hm : ordCompl[2] d ∣ k := hcop.dvd_of_dvd_mul_right ((Nat.ordCompl_dvd d 2).trans hd)
  have hkey : d ∣ 2 ^ (n - 1) * k := by
    calc d = ordProj[2] d * ordCompl[2] d := (Nat.ordProj_mul_ordCompl_eq_self d 2).symm
      _ ∣ 2 ^ (n - 1) * k := mul_dvd_mul (pow_dvd_pow 2 (by omega)) hm
  simpa [mul_comm] using hkey

/-- Every prime factor `p` of a Proth number `N = k * 2 ^ n + 1` admitting a witness `a` with
`a ^ ((N-1)/2) = -1` satisfies `2 ^ n ∣ p - 1`. -/
private lemma two_pow_dvd_prime_sub_one {k n N : ℕ} (hk : Odd k) (hn : 1 ≤ n)
    (hN : N = k * 2 ^ n + 1) (a : ZMod N) (ha : a ^ ((N - 1) / 2) = -1)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) : 2 ^ n ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := by rcases hk with ⟨m, hm⟩; omega
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hhalf : (N - 1) / 2 = k * 2 ^ (n - 1) := by
    have h1 : N - 1 = k * 2 ^ (n - 1) * 2 := by rw [hN, Nat.add_sub_cancel, hpow, mul_assoc]
    omega
  have hNodd : ¬ (2 ∣ N) := by
    have : 2 ∣ k * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) k
    omega
  have hp2 : p ≠ 2 := by rintro rfl; exact hNodd hpN
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  set b : ZMod p := (ZMod.castHom hpN (ZMod p)) a with hb_def
  have hb : b ^ (k * 2 ^ (n - 1)) = -1 := by
    have := congrArg (ZMod.castHom hpN (ZMod p)) ha
    rwa [map_pow, map_neg, map_one, hhalf] at this
  have hb2 : b ^ (k * 2 ^ n) = 1 := by
    have hkn : k * 2 ^ n = k * 2 ^ (n - 1) * 2 := by rw [hpow, mul_assoc]
    rw [hkn, pow_mul, hb]
    ring
  have hord : orderOf b ∣ k * 2 ^ n := orderOf_dvd_of_pow_eq_one hb2
  have hnord : ¬ (orderOf b ∣ k * 2 ^ (n - 1)) := by
    intro h
    have h1 : b ^ (k * 2 ^ (n - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [hb] at h1
    exact ZMod.neg_one_ne_one h1
  have h2ord : 2 ^ n ∣ orderOf b := by
    by_contra h
    exact hnord (dvd_half_of_not_two_pow_dvd hn hord h)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hb
    exact one_ne_zero (neg_eq_zero.mp hb.symm)
  exact h2ord.trans (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hb0))

/-- Proth's theorem: for N = k·2ⁿ + 1 with k odd and k < 2ⁿ, N is prime iff there is a with
    a^((N−1)/2) ≡ −1 (mod N). -/
theorem proth (k n N : ℕ) (hk : Odd k) (hkn : k < 2 ^ n) (hN : N = k * 2 ^ n + 1) :
    N.Prime ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hkn
      rcases hk with ⟨m, hm⟩
      omega
    · exact h
  have hk1 : 1 ≤ k := by
    rcases hk with ⟨m, hm⟩; omega
  have hN3 : 3 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 2 ≤ 2 ^ n := by simpa using this
    nlinarith [hN]
  have hNodd : Odd N := by
    subst hN
    rcases hk with ⟨m, hm⟩
    refine ⟨(k * 2 ^ n) / 2, ?_⟩
    have : 2 ∣ k * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) k
    omega
  constructor
  · intro hprime
    haveI : Fact N.Prime := ⟨hprime⟩
    have hchar : ringChar (ZMod N) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      rintro rfl
      omega
    obtain ⟨a, hanonsq⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hanonsq (IsSquare.zero)
    refine ⟨a, ?_⟩
    have hNdiv : N / 2 = (N - 1) / 2 := by
      rcases hNodd with ⟨m, hm⟩; omega
    have h1 : a ^ (N / 2) ≠ 1 := fun h => hanonsq ((ZMod.euler_criterion N ha0).2 h)
    have h2 := ZMod.pow_div_two_eq_neg_one_or_one N ha0
    rw [hNdiv] at h1 h2
    tauto
  · rintro ⟨a, ha⟩
    by_contra hnp
    set p := N.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpN : p ∣ N := Nat.minFac_dvd N
    have hdvd : 2 ^ n ∣ p - 1 := two_pow_dvd_prime_sub_one hk hn hN a ha hp hpN
    have hp2 : 2 ^ n + 1 ≤ p := by
      have h1 : 0 < p - 1 := by
        have := hp.two_le
        rcases Nat.eq_or_lt_of_le this with h | h
        · exfalso
          have : (2 : ℕ) ∣ N := h ▸ hpN
          rcases hNodd with ⟨m, hm⟩
          omega
        · omega
      have := Nat.le_of_dvd h1 hdvd
      omega
    have hsq : p ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
    have : (2 ^ n + 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hp2 2) hsq
    have hkle : k ≤ 2 ^ n - 1 := by omega
    subst hN
    nlinarith [this, hkn, Nat.one_le_two_pow (n := n)]

end Brockian.MsProth

