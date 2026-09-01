import Mathlib
namespace Brockian.Zsygmondy

open Polynomial

/-! ## Auxiliary results

The proof follows the classical cyclotomic-polynomial argument (Bang's theorem).
Write `Φ n a = eval (a : ℤ) (cyclotomic n ℤ)`.

* Any prime `q ∣ Φ n a` with `q ∤ n` is a primitive prime divisor of `aⁿ - 1`.
* If a prime `p ∣ Φ n a` divides `n`, writing `n = p ^ k * m` with `p ∤ m`, then the
  multiplicative order of `a` mod `p` is exactly `m`, hence `m ∣ p - 1`; in particular `p` is
  the largest prime factor of `n`, and `p ^ 2 ∤ Φ n a`.
* Consequently, if `Φ n a` has no prime factor coprime to `n`, then `Φ n a = p`.
* Finally `Φ n a > p`, a contradiction (except for `(a, n) = (2, 6)`).
-/

/-- The value of the `n`-th cyclotomic polynomial at a natural number `a`, as an integer. -/
noncomputable def Phi (n a : ℕ) : ℤ := (cyclotomic n ℤ).eval (a : ℤ)

/-! ### Basic facts about `Phi` -/

lemma Phi_pos {n : ℕ} (hn : 2 < n) (a : ℕ) : 0 < Phi n a := by
  simpa [Phi] using cyclotomic_pos hn (a : ℤ)

lemma one_lt_Phi {n a : ℕ} (hn : 2 < n) (ha : 2 ≤ a) : 1 < Phi n a := by
  unfold Phi
  have h := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (n := n) (q := a) (by omega) (by omega)
  have h1 : 1 ≤ (a - 1) ^ Nat.totient n := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < (cyclotomic n ℤ).eval (a : ℤ) := cyclotomic_pos hn _
  have h2 : 2 ≤ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs := by omega
  omega

lemma Phi_dvd (n a : ℕ) : Phi n a ∣ (a : ℤ) ^ n - 1 := by
  unfold Phi
  have h : cyclotomic n ℤ ∣ X ^ n - 1 := Polynomial.cyclotomic.dvd_X_pow_sub_one (R := ℤ) n
  obtain ⟨c, hc⟩ := h
  have : (a : ℤ) ^ n - 1 = Polynomial.eval (a : ℤ) (X ^ n - 1) := by simp
  rw [this, hc]
  simp [Polynomial.eval_mul]

/-- Reduction of `p ∣ Φ n a` to a root statement over `ZMod p`. -/
lemma isRoot_zmod_of_dvd_Phi {n a p : ℕ} (hdvd : (p : ℤ) ∣ Phi n a) :
    (cyclotomic n (ZMod p)).IsRoot (a : ZMod p) := by
  unfold Phi at hdvd
  rw [Polynomial.IsRoot]
  have h1 : (cyclotomic n (ZMod p)).eval (a : ZMod p) =
      Int.cast ((cyclotomic n ℤ).eval (a : ℤ)) := by
    have hmap : cyclotomic n (ZMod p) = (cyclotomic n ℤ).map (Int.castRingHom (ZMod p)) :=
      (map_cyclotomic_int n (ZMod p)).symm
    rw [hmap, Polynomial.eval_map]
    induction (cyclotomic n ℤ) using Polynomial.induction_on' with
    | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
    | monomial n c => simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial]
  rw [h1]
  obtain ⟨k, hk⟩ := hdvd
  simp [hk]

/-! ### Primes not dividing `n` -/

lemma orderOf_eq_of_not_dvd {n a p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : orderOf (a : ZMod p) = n := by
  have hroot := isRoot_zmod_of_dvd_Phi hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (n : ZMod p) := by
    refine ⟨?_⟩
    intro h
    apply hpn
    exact (ZMod.natCast_eq_zero_iff n p).mp h
  have hprim : IsPrimitiveRoot (a : ZMod p) n := (Polynomial.isRoot_cyclotomic_iff).mp hroot
  exact hprim.eq_orderOf.symm

/-- Primitivity: if `a` has order `n` modulo `p`, then `p` divides no `aᵐ - 1` with `0 < m < n`. -/
lemma not_dvd_of_orderOf_eq {n a p : ℕ} (ha : 1 ≤ a)
    (hord : orderOf (a : ZMod p) = n) : ∀ m, 0 < m → m < n → ¬ p ∣ a ^ m - 1 := by
  intro m hm₁ hm₂ h
  have : (a : ZMod p) ^ m = 1 := by
    have h' : (p : ℤ) ∣ (a : ℤ) ^ m - 1 := by
      rw [← Int.natCast_pow]
      rw [← Int.natCast_one, ← Int.natCast_sub (Nat.one_le_pow m a ha)]
      exact Int.natCast_dvd_natCast.mpr h
    have h'' : (a : ZMod p) ^ m - 1 = 0 := by
      rw [sub_eq_zero]
      have h1 : ((a : ℤ) ^ m - (1 : ℤ) : ZMod p) = 0 := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) ^ m - 1) p).mpr h'
        convert this using 2
        norm_cast
      simp only [Int.cast_natCast, Int.cast_one] at h1
      exact eq_of_sub_eq_zero h1
    simp [sub_eq_zero] at h''
    exact h''
  have hdiv : orderOf (a : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one this
  rw [hord] at hdiv
  exact Nat.not_dvd_of_pos_of_lt hm₁ hm₂ hdiv

/-! ### Primes dividing `n` -/

lemma orderOf_eq_of_dvd {a p k m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hdvd : (p : ℤ) ∣ Phi (p ^ k * m) a) : orderOf (a : ZMod p) = m := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero ((m : ZMod p)) := NeZero.of_not_dvd (ZMod p) hpm
  have hroot := isRoot_zmod_of_dvd_Phi hdvd
  have h := (isRoot_cyclotomic_prime_pow_mul_iff_of_charP (R := ZMod p) (p := p) (m := m)
    (k := k)).1 hroot
  exact h.eq_orderOf.symm

/-- If `p ∣ n` and `p ∣ Φ n a`, then the prime-to-`p` part of `n` divides `p - 1`. -/
lemma ordCompl_dvd_pred {n a p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : n / p ^ (n.factorization p) ∣ p - 1 := by
  set k := n.factorization p
  set m := n / p ^ k
  have hnk : n = p ^ k * m := by
    rw [Nat.mul_div_cancel' (Nat.ordProj_dvd n p)]
  have hdiv : p ^ k ∣ n := Nat.ordProj_dvd n p
  have hle : p ^ k ≤ n := Nat.le_of_dvd hn hdiv
  have hm_pos : 0 < m := Nat.div_pos hle (pow_pos hp.pos k)
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
  have hpm : ¬ p ∣ m := by
    rw [Nat.dvd_div_iff_mul_dvd hdiv]
    intro h
    have h2 : p ^ (k + 1) ∣ n := by simpa [pow_succ] using h
    have hfac := Nat.factorization_le_iff_dvd (pow_ne_zero (k + 1) hp.ne_zero) hn.ne' |>.mpr h2
    have hpk := hfac p
    simp only [Nat.factorization_pow, Finsupp.smul_apply] at hpk
    rw [Nat.Prime.factorization_self hp] at hpk
    convert hpk using 1
    simp [k]
  have hdvd' : (p : ℤ) ∣ Phi (p ^ k * m) a := by rw [← hnk]; exact hdvd
  have hord := orderOf_eq_of_dvd hp hpm hdvd'
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hm1 : m = 1
  · simp [hm1]
  · -- Otherwise, we can prove a ≢ 0 (mod p)
    have ha_ne : (a : ZMod p) ≠ 0 := by
      intro ha
      have hroot := isRoot_zmod_of_dvd_Phi hdvd
      rw [Polynomial.IsRoot] at hroot
      have heq : (cyclotomic n (ZMod p)).eval ((a : ZMod p)) = (cyclotomic n (ZMod p)).eval 0 := by
        rw [ha]
      rw [heq] at hroot
      have hn1 : 1 < n := by
        by_contra hle1
        push_neg at hle1
        interval_cases n
        simp [Phi] at hdvd
        · -- n = 1: p ∣ a - 1 and p ∣ a implies p ∣ 1
          have hpa : (p : ℤ) ∣ a := by
            have := ZMod.intCast_zmod_eq_zero_iff_dvd a p
            simp [ha] at this
            exact this
          have : (p : ℤ) ∣ 1 := by simpa using Int.dvd_sub hpa hdvd
          exact Nat.Prime.not_dvd_one hp (Int.natCast_dvd_natCast.mp this)
      have hcoeff := Polynomial.cyclotomic_coeff_zero (ZMod p) hn1
      have hroot' : (cyclotomic n (ZMod p)).coeff 0 = 0 := by
        simp [Polynomial.eval_eq_sum_range, Finset.sum_range_succ'] at hroot
        exact hroot
      rw [hcoeff] at hroot'
      norm_num at hroot'
    have key : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha_ne
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr key

/-- If `p ∣ n` and `p ∣ Φ n a`, then every prime factor of `n` is at most `p`. -/
lemma prime_le_of_dvd_Phi {n a p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : ∀ q, q.Prime → q ∣ n → q ≤ p := by
  intro q hq hqn
  by_cases hq_eq_p : q = p
  · exact hq_eq_p ▸ le_refl p
  · have hq_ne_p : q ≠ p := hq_eq_p
    have hq_coprime_p : Nat.Coprime q (p ^ (n.factorization p)) := by
      apply Nat.Coprime.pow_right
      exact hq.coprime_iff_not_dvd.mpr fun h => hq_ne_p (Nat.prime_dvd_prime_iff_eq hq hp |>.mp h)
    have hq_dvd_ordCompl : q ∣ n / p ^ (n.factorization p) := by
      have hpow_dvd_n : p ^ (n.factorization p) ∣ n := Nat.ordProj_dvd n p
      have hmul : n = p ^ (n.factorization p) * (n / p ^ (n.factorization p)) := (Nat.mul_div_cancel' hpow_dvd_n).symm
      rw [hmul] at hqn
      exact hq_coprime_p.dvd_of_dvd_mul_left hqn
    have hordCompl_dvd_pred := ordCompl_dvd_pred hn hp hpn hdvd
    have hq_dvd_pred : q ∣ p - 1 := Nat.dvd_trans hq_dvd_ordCompl hordCompl_dvd_pred
    have hq_le_pred : q ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hq_dvd_pred
    exact Nat.le_trans hq_le_pred (Nat.sub_le p 1)

/-- If `p ∣ n` and `p ∣ Φ n a`, then `p` divides `a ^ (n / p) - 1`. -/
lemma dvd_pow_div_sub_one {n a p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : (p : ℤ) ∣ (a : ℤ) ^ (n / p) - 1 := by
  set k := n.factorization p with hk_def
  set m := n / p ^ k with hm_def
  have hmk : n = p ^ k * m := by rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (by
    intro heq
    rw [heq, Nat.mul_zero] at hmk
    exact hn.ne' hmk)
  have hpndiv : ¬ p ∣ m := by
    rw [hm_def]
    rw [Nat.Prime.dvd_iff_one_le_factorization hp]
    · rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
      simp [hp.factorization_self]
    · omega
  rw [hmk] at hdvd
  have hord : orderOf (a : ZMod p) = m := orderOf_eq_of_dvd hp hpndiv hdvd
  have hk_pos : k > 0 := hp.factorization_pos_of_dvd hn.ne' hpn
  have hdiv : m ∣ n / p := by
    rw [hmk]
    have hpdiv : p ∣ p ^ k := dvd_pow_self p hk_pos.ne'
    have heq : p ^ k * m / p = p ^ (k - 1) * m := by
      have : p ^ k * m = p * (p ^ (k - 1) * m) := by
        rw [← mul_assoc]
        rw [show p ^ k = p * p ^ (k - 1) by rw [← pow_succ', Nat.sub_add_cancel hk_pos]]
      rw [this, Nat.mul_div_cancel_left _ hp.pos]
    rw [heq]
    exact dvd_mul_left m _
  have hpow_eq_one : (a : ZMod p) ^ (n / p) = 1 := by
    have hdiv' : orderOf (a : ZMod p) ∣ n / p := hord ▸ hdiv
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv'
  have hsub : ((a : ℕ) ^ (n / p) : ZMod p) - 1 = 0 := by simp [hpow_eq_one]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [hsub]

/-! ### The square of `p` does not divide `Φ n a` -/

/-- Lifting the exponent: for an odd prime `p ∣ n` we have `p ^ 2 ∤ Φ n a`. -/
lemma not_sq_dvd_Phi_of_odd {n a p : ℕ} (ha : 2 ≤ a) (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hdvd : (p : ℤ) ∣ (a : ℤ) ^ (n / p) - 1) : ¬ ((p : ℤ) ^ 2 ∣ Phi n a) := by
  intro hsq
  unfold Phi at hsq
  set q := n / p with hq
  have hpq : p * q = n := Nat.mul_div_cancel' hpn
  have hp2' := hp.two_le
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hpq; omega
    · exact h
  have hqn : q ∈ n.properDivisors := by
    refine Nat.mem_properDivisors.2 ⟨⟨p, by rw [← hpq]; ring⟩, ?_⟩
    nlinarith [hpq, hq0]
  have hdvd2 : ((a : ℤ) ^ q - 1) * (cyclotomic n ℤ).eval (a : ℤ) ∣ (a : ℤ) ^ n - 1 := by
    obtain ⟨c, hc⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hqn
    refine ⟨c.eval (a : ℤ), ?_⟩
    have := congrArg (Polynomial.eval (a : ℤ)) hc
    simpa using this
  set x : ℤ := (a : ℤ) ^ q with hx
  have hx2 : 2 ≤ x := by
    calc (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
      _ = (a : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (a : ℤ) ^ q := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ a)) (by omega)
  have hxp : (a : ℤ) ^ n = x ^ p := by rw [hx, ← pow_mul, mul_comm q p, hpq]
  have hpx : ¬ (p : ℤ) ∣ x := by
    intro h
    have h1 : (p : ℤ) ∣ 1 := (dvd_sub_right h).mp (by simpa using hdvd)
    have := Int.le_of_dvd one_pos h1
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2'
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd hdvd hpx p
  rw [one_pow, hp.emultiplicity_self] at hlte
  have hdvd3 : (x - 1) * (p : ℤ) ^ 2 ∣ x ^ p - 1 := by
    obtain ⟨c, hc⟩ := hsq
    obtain ⟨d, hd⟩ := hdvd2
    exact ⟨c * d, by rw [← hxp, hd, hc]; ring⟩
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : emultiplicity (p : ℤ) ((x - 1) * (p : ℤ) ^ 2)
      = emultiplicity (p : ℤ) (x - 1) + 2 := by
    rw [emultiplicity_mul hprime, emultiplicity_pow_self hprime.ne_zero hprime.not_unit]
    norm_num
  have h1 : emultiplicity (p : ℤ) ((x - 1) * (p : ℤ) ^ 2) ≤ emultiplicity (p : ℤ) (x ^ p - 1) :=
    emultiplicity_le_emultiplicity_of_dvd_right hdvd3
  rw [h2, hlte] at h1
  have hfin : FiniteMultiplicity (p : ℤ) (x - 1) :=
    FiniteMultiplicity.of_prime_left hprime (by intro h; omega)
  rw [hfin.emultiplicity_eq_multiplicity] at h1
  set M := multiplicity (p : ℤ) (x - 1) with hM
  have h3 : ((M + 2 : ℕ) : ℕ∞) ≤ ((M + 1 : ℕ) : ℕ∞) := by push_cast; exact h1
  have h4 := Nat.cast_le (α := ℕ∞).mp h3
  omega

lemma cyclotomic_two_pow_eval (k : ℕ) (x : ℤ) :
    (cyclotomic (2 ^ (k + 1)) ℤ).eval x = x ^ (2 ^ k) + 1 := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum (by decide : Nat.Prime 2)]
  simp

lemma not_four_dvd_sq_add_one (x : ℤ) : ¬ ((4 : ℤ) ∣ x ^ 2 + 1) := by
  rw [Int.dvd_iff_emod_eq_zero]
  have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [h, sq, Int.add_emod, Int.mul_emod]

/-- For any prime `p ∣ n` dividing `Φ n a` we have `p ^ 2 ∤ Φ n a`. -/
lemma not_sq_dvd_Phi {n a p : ℕ} (ha : 2 ≤ a) (hn : 2 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : ¬ ((p : ℤ) ^ 2 ∣ Phi n a) := by
  have hn0 : 0 < n := by omega
  by_cases hp2 : p = 2
  · subst hp2
    -- here `n` is a power of two, and `Φ n a = a ^ (2 ^ (k - 1)) + 1 ≡ 2 [MOD 4]`
    have hmp : n / 2 ^ (n.factorization 2) ∣ 1 := ordCompl_dvd_pred hn0 hp hpn hdvd
    have hm1 : n / 2 ^ (n.factorization 2) = 1 := Nat.dvd_one.1 hmp
    have hnk : 2 ^ (n.factorization 2) = n := by
      have := Nat.ordProj_mul_ordCompl_eq_self n 2
      rw [hm1, mul_one] at this
      exact this
    have hk2 : 2 ≤ n.factorization 2 := by
      by_contra hlt
      interval_cases h : n.factorization 2 <;> omega
    obtain ⟨j, hj⟩ : ∃ j, n.factorization 2 = j + 1 + 1 := ⟨n.factorization 2 - 2, by omega⟩
    rw [hj] at hnk
    have hPhi : Phi n a = ((a : ℤ) ^ (2 ^ j)) ^ 2 + 1 := by
      unfold Phi
      rw [← hnk, cyclotomic_two_pow_eval (j + 1) (a : ℤ), ← pow_mul, pow_succ, mul_comm (2 ^ j) 2]
    rw [hPhi]
    have : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
    rw [this]
    exact not_four_dvd_sq_add_one _
  · exact not_sq_dvd_Phi_of_odd ha hn0 hp hp2 hpn (dvd_pow_div_sub_one hn0 hp hpn hdvd)

/-! ### The size bound `Φ n a > p` -/

/-- `Φ_{p^(k+1) m}(x) = Φ_{m p}(x ^ (p ^ k))`. -/
lemma Phi_pow_reduction {p m : ℕ} (hp : p.Prime) (k : ℕ) (x : ℤ) :
    (cyclotomic (p ^ (k + 1) * m) ℤ).eval x = (cyclotomic (m * p) ℤ).eval (x ^ (p ^ k)) := by
  induction k generalizing x with
  | zero => simp [mul_comm]
  | succ k ih =>
    have hdvd : p ∣ p ^ (k + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero k)) m
    have h2 := congrArg (Polynomial.eval x) (cyclotomic_expand_eq_cyclotomic hp hdvd ℤ)
    rw [expand_eval] at h2
    have hxx : p ^ (k + 1) * m * p = p ^ (k + 1 + 1) * m := by ring
    rw [hxx] at h2
    rw [← h2, ih (x ^ p), ← pow_mul, ← pow_succ']

/-- Lower bound for `Φ_{m p}` in terms of `((y ^ p - 1) / (y + 1)) ^ φ m`, over the reals. -/
lemma real_lower_bound {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m) {y : ℝ}
    (hy : 2 ≤ y) : ((y ^ p - 1) / (y + 1)) ^ (Nat.totient m) < (cyclotomic (m * p) ℝ).eval y := by
  have hy1 : (1:ℝ) < y := by linarith
  have hyp : (1:ℝ) < y ^ p := one_lt_pow₀ hy1 hp.ne_zero
  have key : (cyclotomic m ℝ).eval (y ^ p)
      = (cyclotomic (m * p) ℝ).eval y * (cyclotomic m ℝ).eval y := by
    have h2 := congrArg (Polynomial.eval y) (cyclotomic_expand_eq_cyclotomic_mul hp hpm ℝ)
    rw [expand_eval] at h2
    simpa using h2
  have hlow : (y ^ p - 1) ^ (Nat.totient m) < (cyclotomic m ℝ).eval (y ^ p) :=
    sub_one_pow_totient_lt_cyclotomic_eval hm hyp
  have hup : (cyclotomic m ℝ).eval y ≤ (y + 1) ^ (Nat.totient m) :=
    cyclotomic_eval_le_add_one_pow_totient hy1 m
  have hpos : 0 < (cyclotomic m ℝ).eval y := cyclotomic_pos' m hy1
  have hy1' : (0:ℝ) < y + 1 := by linarith
  rw [div_pow, div_lt_iff₀ (by positivity)]
  calc (y ^ p - 1) ^ (Nat.totient m) < (cyclotomic m ℝ).eval (y ^ p) := hlow
    _ = (cyclotomic (m * p) ℝ).eval y * (cyclotomic m ℝ).eval y := key
    _ ≤ (cyclotomic (m * p) ℝ).eval y * (y + 1) ^ (Nat.totient m) := by
        have hmp : 0 < (cyclotomic (m * p) ℝ).eval y := by
          rcases lt_trichotomy ((cyclotomic (m * p) ℝ).eval y) 0 with h | h | h
          · nlinarith [hlow, key, pow_pos (show (0:ℝ) < y ^ p - 1 by linarith) (Nat.totient m)]
          · nlinarith [hlow, key, pow_pos (show (0:ℝ) < y ^ p - 1 by linarith) (Nat.totient m)]
          · exact h
        nlinarith

lemma real_base_bound {p : ℕ} (hp : 5 ≤ p) {y : ℝ} (hy : 2 ≤ y) :
    (p : ℝ) ≤ (y ^ p - 1) / (y + 1) := by
  have hy1 : y + 1 > 0 := by linarith
  rw [le_div_iff₀ hy1]
  have hy2 : y ^ p ≥ 2 ^ p := by gcongr
  have hgeom : y ^ p - 1 = (y - 1) * ∑ i ∈ Finset.range p, y ^ i := by
    rw [mul_comm, geom_sum_mul]
  have hsum_bound : ∑ i ∈ Finset.range p, y ^ i ≥ ∑ i ∈ Finset.range 5, y ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
    intro x _ _
    exact pow_nonneg (by linarith : 0 ≤ y) x
  have hsum5 : ∑ i ∈ Finset.range 5, y ^ i = 1 + y + y^2 + y^3 + y^4 := by
    simp [Finset.sum_range_succ]
  have hprod : (y - 1) * (1 + y + y^2 + y^3 + y^4) = y^5 - 1 := by ring
  have hy5_bound : y ^ p - 1 ≥ y ^ 5 - 1 := by
    apply sub_le_sub_right
    exact pow_le_pow_right₀ (by linarith) hp
  have hy5_bound2 : y ^ 5 ≥ 5 * (y + 1) + 1 := by nlinarith [sq_nonneg y, sq_nonneg (y^2 - 2)]
  have aux : ∀ q : ℕ, 5 ≤ q → (y : ℝ) ^ q ≥ q * (y + 1) + 1 := by
    intro q hq
    have key : ∀ k : ℕ, (y : ℝ) ^ (5 + k) ≥ (5 + k) * (y + 1) + 1 := by
      intro k
      induction k with
      | zero => simp; exact hy5_bound2
      | succ k ih =>
        have h1 : y ^ (5 + (k + 1)) = y ^ (5 + k) * y := by ring
        have h2 : y ^ (5 + k) * y ≥ ((5 + k) * (y + 1) + 1) * y := by nlinarith
        have h3 : ((5 + k) * (y + 1) + 1) * y = (5 + k) * y * (y + 1) + y := by ring
        have hy2 : y ^ 2 ≥ 4 := by nlinarith
        have h4 : (5 + (k : ℝ)) * y ^ 2 ≥ 7 + k := by nlinarith
        have h5 : (5 + k) * y * (y + 1) + y ≥ (6 + k) * (y + 1) + 1 := by nlinarith
        have h8 : (5 : ℝ) + ↑(k + 1) = 6 + k := by push_cast; ring
        rw [h8]
        linarith
    have heq : q = 5 + (q - 5) := by omega
    rw [heq]
    simpa using key (q - 5)
  have := aux p hp
  linarith

/-- The case `m = 1`: `Φ_p(y) = 1 + y + ⋯ + y ^ (p - 1) ≥ 2 ^ p - 1 > p`. -/
lemma lt_cyclotomic_prime_eval {p y : ℕ} (hp : p.Prime) (hy : 2 ≤ y) :
    (p : ℤ) < (cyclotomic p ℤ).eval (y : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hyz : (2 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy
  rw [cyclotomic_prime ℤ p]
  simp only [eval_finset_sum, eval_pow, eval_X]
  have hlt : ∑ _i ∈ Finset.range p, (1 : ℤ) < ∑ i ∈ Finset.range p, (y : ℤ) ^ i := by
    refine Finset.sum_lt_sum (fun i _ => one_le_pow₀ (by linarith)) ⟨1, ?_, ?_⟩
    · exact Finset.mem_range.2 hp.one_lt
    · simpa using by linarith
  simpa using hlt

/-- The case `m ≥ 2` and `p ≥ 5`, via the real-analytic bounds. -/
lemma lt_cyclotomic_mul_prime_eval_of_five {p m y : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 2 ≤ m)
    (hpm : ¬ p ∣ m) (hy : 2 ≤ y) : (p : ℤ) < (cyclotomic (m * p) ℤ).eval (y : ℤ) := by
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have h1 : (p : ℝ) ≤ ((y : ℝ) ^ p - 1) / ((y : ℝ) + 1) := real_base_bound hp5 hyR
  have hbase1 : (1 : ℝ) ≤ ((y : ℝ) ^ p - 1) / ((y : ℝ) + 1) := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    linarith
  have hphi : Nat.totient m ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
  have h2 : ((y : ℝ) ^ p - 1) / ((y : ℝ) + 1)
      ≤ (((y : ℝ) ^ p - 1) / ((y : ℝ) + 1)) ^ (Nat.totient m) := le_self_pow₀ hbase1 hphi
  have h3 := real_lower_bound hm hp hpm hyR
  have h4 : (p : ℝ) < (cyclotomic (m * p) ℝ).eval (y : ℝ) := by linarith
  have h5 : (cyclotomic (m * p) ℝ).eval ((y : ℤ) : ℝ)
      = (((cyclotomic (m * p) ℤ).eval (y : ℤ) : ℤ) : ℝ) := by
    simpa using cyclotomic.eval_apply ((y : ℤ)) (m * p) (Int.castRingHom ℝ)
  rw [show ((y : ℕ) : ℝ) = (((y : ℤ)) : ℝ) by push_cast; ring, h5] at h4
  exact_mod_cast h4

/-- The key size bound: `Φ_{m p}(y) > p`, where `m ∣ p - 1` and `y ≥ 2`, except in the
single case `y = 2, m = 2, p = 3` (which is `Φ₆(2) = 3`). -/
lemma lt_cyclotomic_mul_prime_eval {p m y : ℕ} (hp : p.Prime) (hmp : m ∣ p - 1) (hy : 2 ≤ y)
    (hexc : ¬ (y = 2 ∧ m = 2 ∧ p = 3)) : (p : ℤ) < (cyclotomic (m * p) ℤ).eval (y : ℤ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hmp (by omega)
  have hmle : m ≤ p - 1 := Nat.le_of_dvd (by omega) hmp
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have : m = 1 := by omega
    rw [this, one_mul]
    exact lt_cyclotomic_prime_eval hp hy
  · -- `2 ≤ m`, so `p ≥ 3`
    have hp3 : 3 ≤ p := by omega
    have hpm : ¬ p ∣ m := Nat.not_dvd_of_pos_of_lt hm0 (by omega)
    rcases eq_or_lt_of_le hp3 with hp3' | hp4
    · -- `p = 3`, hence `m = 2` and `y ≥ 3`
      have hm2' : m = 2 := by omega
      have hy3 : 3 ≤ y := by
        rcases eq_or_lt_of_le hy with h | h
        · exact absurd ⟨h.symm, hm2', hp3'.symm⟩ hexc
        · omega
      have hmp6 : m * p = 6 := by rw [hm2', ← hp3']
      rw [hmp6, cyclotomic_six]
      have : (3 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy3
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
      rw [← hp3']
      push_cast
      nlinarith
    · -- `p ≥ 5`
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p
          · exact absurd hp (by decide)
        · exact h
      exact lt_cyclotomic_mul_prime_eval_of_five hp hp5 hm2 hpm hy

/-- The size bound at the level of `n = p ^ k * m`. -/
lemma lt_Phi {n a p k m : ℕ} (ha : 2 ≤ a) (hp : p.Prime) (hk : 0 < k) (hmp : m ∣ p - 1)
    (hn : n = p ^ k * m) (hexc : ¬ (a = 2 ∧ n = 6)) : (p : ℤ) < Phi n a := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hy2 : 2 ≤ a ^ (p ^ k') := by
    calc 2 ≤ a := ha
      _ = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ (p ^ k') := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
  have hrw : Phi n a = (cyclotomic (m * p) ℤ).eval ((a ^ (p ^ k') : ℕ) : ℤ) := by
    unfold Phi
    rw [hn, Phi_pow_reduction hp k' (a : ℤ)]
    push_cast
    ring_nf
  rw [hrw]
  refine lt_cyclotomic_mul_prime_eval hp hmp hy2 ?_
  rintro ⟨hy, hm2, hp3⟩
  have hk'0 : k' = 0 := by
    by_contra hne
    have h1 : 1 ≤ k' := by omega
    have : 2 ≤ p ^ k' := by
      calc 2 ≤ p := hp2
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k' := Nat.pow_le_pow_right (by omega) h1
    have : 2 ^ 2 ≤ a ^ (p ^ k') := by
      calc (2:ℕ) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha 2
        _ ≤ a ^ (p ^ k') := Nat.pow_le_pow_right (by omega) this
    omega
  subst hk'0
  have ha2 : a = 2 := by
    simpa using hy
  refine hexc ⟨ha2, ?_⟩
  rw [hn, hm2, hp3]
  norm_num

/-! ## Main theorem -/

/-- Zsygmondy's theorem (Bang's case b=1, n ≥ 3): aⁿ − 1 has a primitive prime divisor —
    a prime dividing aⁿ − 1 but no aᵐ − 1 for 0 < m < n — except for (a,n) = (2,6). -/
theorem zsygmondy_primitive_prime (a n : ℕ) (ha : 2 ≤ a) (hn : 3 ≤ n)
    (hexc : ¬ (a = 2 ∧ n = 6)) :
    ∃ p, p.Prime ∧ p ∣ (a ^ n - 1) ∧ ∀ m, 0 < m → m < n → ¬ p ∣ (a ^ m - 1) := by
  have hn0 : 0 < n := by omega
  have hn2 : 2 < n := by omega
  have hPpos : 0 < Phi n a := Phi_pos hn2 a
  have hP1 : 1 < Phi n a := one_lt_Phi hn2 ha
  set N : ℕ := (Phi n a).toNat with hNdef
  have hNcast : (N : ℤ) = Phi n a := Int.toNat_of_nonneg hPpos.le
  have hN1 : 1 < N := by omega
  have hdvdN : ∀ q : ℕ, ((q : ℤ) ∣ Phi n a ↔ q ∣ N) := by
    intro q
    rw [← hNcast]
    exact Int.natCast_dvd_natCast
  by_cases hcase : ∃ q, q.Prime ∧ q ∣ N ∧ ¬ q ∣ n
  · obtain ⟨q, hq, hqN, hqn⟩ := hcase
    have hqP : (q : ℤ) ∣ Phi n a := (hdvdN q).2 hqN
    have hord : orderOf ((a : ZMod q)) = n := orderOf_eq_of_not_dvd hq hqn hqP
    refine ⟨q, hq, ?_, not_dvd_of_orderOf_eq (by omega) hord⟩
    have h1 : (q : ℤ) ∣ (a : ℤ) ^ n - 1 := hqP.trans (Phi_dvd n a)
    have hle : 1 ≤ a ^ n := Nat.one_le_pow _ _ (by omega)
    have hcast : ((a ^ n - 1 : ℕ) : ℤ) = (a : ℤ) ^ n - 1 := by
      push_cast [hle]
      ring
    exact_mod_cast hcast ▸ h1
  · exfalso
    push_neg at hcase
    obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (n := N) (by omega)
    have hpP : (p : ℤ) ∣ Phi n a := (hdvdN p).2 hpN
    have hpn : p ∣ n := hcase p hp hpN
    have hk0 : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0.ne' hpn
    have hnk : p ^ (n.factorization p) * (n / p ^ (n.factorization p)) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hmp : n / p ^ (n.factorization p) ∣ p - 1 := ordCompl_dvd_pred hn0 hp hpn hpP
    have huniq : ∀ q, q.Prime → q ∣ N → q = p := by
      intro q hq hqN
      have hqn : q ∣ n := hcase q hq hqN
      have h1 : q ≤ p := prime_le_of_dvd_Phi hn0 hp hpn hpP q hq hqn
      have h2 : p ≤ q := prime_le_of_dvd_Phi hn0 hq hqn ((hdvdN q).2 hqN) p hp hpn
      omega
    have hsq : ¬ ((p : ℤ) ^ 2 ∣ Phi n a) := not_sq_dvd_Phi ha hn2 hp hpn hpP
    have hNp : N = p := by
      obtain ⟨t, ht⟩ := hpN
      have ht1 : t = 1 := by
        by_contra hne
        have ht0 : t ≠ 0 := by
          rintro rfl
          simp at ht
          omega
        obtain ⟨r, hr, hrt⟩ := Nat.exists_prime_and_dvd hne
        have hrN : r ∣ N := ht ▸ hrt.mul_left p
        have hrp : r = p := huniq r hr hrN
        subst hrp
        obtain ⟨s, hs⟩ := hrt
        refine hsq ⟨(s : ℤ), ?_⟩
        rw [← hNcast, ht, hs]
        push_cast
        ring
      rw [ht, ht1, mul_one]
    have hlt := lt_Phi ha hp hk0 hmp hnk.symm hexc
    rw [← hNcast, hNp] at hlt
    omega

end Brockian.Zsygmondy

