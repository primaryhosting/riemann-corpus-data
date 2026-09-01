import Mathlib
namespace Brockian.MsPocklington

/-- If `p` is a prime divisor of `N` and `gcd (a ^ m - 1) N = 1`, then `a ^ m ≢ 1 (mod p)`. -/
private lemma pow_ne_one_mod_prime {N a m p : ℕ} (h2 : Nat.gcd (a ^ m - 1) N = 1)
    (hp : p.Prime) (hpN : p ∣ N) : ¬ (a ^ m ≡ 1 [MOD p]) := by
  intro h
  have hdiv : p ∣ a ^ m - 1 := by
    by_cases ham : a ^ m ≥ 1
    · rw [Nat.modEq_iff_dvd] at h
      have hpz : (p : ℤ) ∣ ↑(a ^ m) - 1 := by
        have := h.neg_right
        simpa using this
      exact_mod_cast hpz
    · -- `a ^ m < 1` means `a ^ m = 0`
      have ham0 : a ^ m = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp ham)
      rw [ham0] at h
      rcases p with _ | _ | p <;> simp_all
  have hgcd := Nat.dvd_gcd hdiv hpN
  rw [h2] at hgcd
  exact Nat.Prime.not_dvd_one hp hgcd

/-- If `d ∣ q * m` with `q` prime and `d ∤ m`, then `q ∣ d`. -/
private lemma prime_dvd_of_dvd_mul_not_dvd {q m d : ℕ} (hq : q.Prime) (hdvd : d ∣ q * m)
    (hnd : ¬ d ∣ m) : q ∣ d := by
  by_contra hqnd
  have hcoprime : Nat.Coprime d q := (hq.coprime_iff_not_dvd.mpr hqnd).symm
  exact hnd (hcoprime.dvd_of_dvd_mul_left hdvd)

/-- Key step: every prime divisor `p` of `N` satisfies `q ∣ p - 1`. -/
private lemma q_dvd_prime_sub_one {N q m a p : ℕ} (hfac : N - 1 = q * m)
    (hq : q.Prime) (h1 : a ^ (N - 1) ≡ 1 [MOD N]) (h2 : Nat.gcd (a ^ m - 1) N = 1)
    (hp : p.Prime) (hpN : p ∣ N) : q ∣ p - 1 := by
  -- Since p ∣ N and a^(N-1) ≡ 1 (mod N), we have a^(N-1) ≡ 1 (mod p)
  have hmod_p : a ^ (N - 1) ≡ 1 [MOD p] := h1.of_dvd hpN
  rw [hfac] at hmod_p
  -- The order of a mod p divides q * m
  -- But a^m ≢ 1 (mod p) by pow_ne_one_mod_prime
  have hnamod : ¬(a ^ m ≡ 1 [MOD p]) := pow_ne_one_mod_prime h2 hp hpN
  -- Consider the order of a in ZMod p
  have horder : orderOf (a : ZMod p) ∣ q * m := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hconv : (a : ZMod p) ^ (q * m) = 1 := by
      simpa using congr_arg (fun x : ℕ => (x : ZMod p)) hmod_p
    exact hconv
  -- The order does not divide m
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hnot_dvd : ¬(orderOf (a : ZMod p) ∣ m) := by
    intro hdvd
    have hpow := orderOf_dvd_iff_pow_eq_one.mp hdvd
    apply hnamod
    have hcast : ((a ^ m : ℕ) : ZMod p) = 1 := by rw [Nat.cast_pow]; exact hpow
    rw [show (1 : ZMod p) = ((1 % p : ℕ) : ZMod p) from by
      simp [Nat.mod_eq_of_lt hp.one_lt]] at hcast
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    rwa [Nat.mod_eq_of_lt hp.one_lt] at hcast
  -- Apply prime_dvd_of_dvd_mul_not_dvd to get q ∣ order
  have hq_dvd_order : q ∣ orderOf (a : ZMod p) := prime_dvd_of_dvd_mul_not_dvd hq horder hnot_dvd
  -- The order divides p - 1 since ZMod p has p - 1 nonzero elements
  have ha_ne_zero : (a : ZMod p) ≠ 0 := by
    intro ha0
    have hp_div_a : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp ha0
    have hm_pos : m ≠ 0 := by
      by_contra hm0
      simp [hm0] at hnot_dvd
    have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq.pos.ne' hm_pos
    have hpow : a ^ (q * m) ≡ 0 [MOD p] :=
      (Nat.modEq_zero_iff_dvd).mpr (dvd_pow hp_div_a hqm)
    have hcontra : 1 ≡ 0 [MOD p] := (hmod_p.symm).trans hpow
    simp [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] at hcontra
  have horder_p_minus_1 : orderOf (a : ZMod p) ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one ha_ne_zero)
  exact Nat.dvd_trans hq_dvd_order horder_p_minus_1

/-- Every prime divisor of `N` is bigger than `q`. -/
private lemma q_lt_prime_divisor {N q m a p : ℕ} (hfac : N - 1 = q * m)
    (hq : q.Prime) (h1 : a ^ (N - 1) ≡ 1 [MOD N]) (h2 : Nat.gcd (a ^ m - 1) N = 1)
    (hp : p.Prime) (hpN : p ∣ N) : q < p := by
  have hd : q ∣ p - 1 := q_dvd_prime_sub_one hfac hq h1 h2 hp hpN
  have hp2 : 2 ≤ p := hp.two_le
  have hpos : 0 < p - 1 := by omega
  have := Nat.le_of_dvd hpos hd
  omega

/-- Pocklington's primality criterion: if N−1 = q·m with q prime, q > √N, and there is a with
    a^(N−1) ≡ 1 (mod N) and gcd(a^((N−1)/q) − 1, N) = 1, then N is prime. -/
theorem pocklington (N q m : ℕ) (hN : 1 < N) (hfac : N - 1 = q * m) (hq : q.Prime)
    (hqbig : N < q * q) (a : ℕ)
    (h1 : a ^ (N - 1) ≡ 1 [MOD N])
    (h2 : Nat.gcd (a ^ ((N - 1) / q) - 1) N = 1) :
    N.Prime := by
  have hq0 : 0 < q := hq.pos
  have hm : (N - 1) / q = m := by
    rw [hfac, Nat.mul_div_cancel_left _ hq0]
  rw [hm] at h2
  by_contra hnp
  have hNpos : 0 < N := by omega
  have hmin : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self hNpos hnp
  have hpp : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hlt : q < N.minFac := q_lt_prime_divisor hfac hq h1 h2 hpp (Nat.minFac_dvd N)
  nlinarith [hmin, hlt, sq_nonneg (N.minFac)]

end Brockian.MsPocklington

