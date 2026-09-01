import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/
noncomputable def sol (G : Type*) [Group G] (n : ℕ) : ℕ := Nat.card {x : G // x ^ n = 1}

/-- The number of solutions of `x ^ n = y` in `G`. -/
noncomputable def solEq {G : Type*} [Group G] (n : ℕ) (y : G) : ℕ := Nat.card {x : G // x ^ n = y}

lemma sol_eq_solEq_one (n : ℕ) : sol G n = solEq n (1 : G) := rfl

lemma sol_eq_card_filter [Fintype G] (n : ℕ) :
    sol G n = (univ.filter (fun x : G => x ^ n = 1)).card := by
  simp [sol, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

lemma solEq_eq_card_filter [Fintype G] (n : ℕ) (y : G) :
    solEq n y = (univ.filter (fun x : G => x ^ n = y)).card := by
  simp [solEq, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

/-- Solutions of `x ^ n = 1` only depend on `gcd n |G|`. -/
lemma sol_eq_gcd [Finite G] (n : ℕ) : sol G n = sol G (Nat.gcd n (Nat.card G)) := by
  haveI : Fintype G := Fintype.ofFinite G
  have h : {x : G | x ^ n = 1} = {x : G | x ^ (Nat.gcd n (Nat.card G)) = 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [pow_gcd_eq_one]
    simp [Nat.card_eq_fintype_card, pow_card_eq_one]
  simp only [sol, Set.ext_iff, Set.mem_setOf_eq] at h ⊢
  exact Nat.card_congr (Equiv.subtypeEquivRight h)

/-- Counting solutions in the top subgroup is the same as counting in the group. -/
lemma sol_top [Finite G] (n : ℕ) : sol (↥(⊤ : Subgroup G)) n = sol G n := by
  apply Nat.card_congr
  exact Subgroup.topEquiv.subtypeEquiv fun x => by
    rw [← Subtype.coe_inj]
    simp

/-- Isomorphic groups have the same number of solutions of `x ^ n = 1`. -/
lemma sol_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) (n : ℕ) :
    sol H n = sol K n := by
  unfold sol
  apply Nat.card_congr
  exact {
    toFun := fun ⟨x, hx⟩ => ⟨e x, by rw [← map_pow, hx, map_one]⟩
    invFun := fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_pow, hy, map_one]⟩
    left_inv := fun ⟨x, hx⟩ => by simp
    right_inv := fun ⟨y, hy⟩ => by simp
  }

/-- Conjugate centralizers have the same number of solutions of `x ^ n = 1`. -/
lemma sol_centralizer_conj [Finite G] (g w : G) (n : ℕ) :
    sol ↥(Subgroup.centralizer ({g * w * g⁻¹} : Set G)) n
      = sol ↥(Subgroup.centralizer ({w} : Set G)) n := by
  -- Conjugation by `g` gives an isomorphism between the centralizers.
  let ι : Subgroup.centralizer {w} ≃* Subgroup.centralizer {g * w * g⁻¹} := by
    refine {
      toFun := fun ⟨h, hh⟩ => ⟨g * h * g⁻¹, ?_⟩
      invFun := fun ⟨h, hh⟩ => ⟨g⁻¹ * h * g, ?_⟩
      left_inv := fun ⟨h, _⟩ => ?_
      right_inv := fun ⟨h, _⟩ => ?_
      map_mul' := fun _ _ => ?_ }
    · show g * h * g⁻¹ ∈ Subgroup.centralizer {g * w * g⁻¹}
      simp [Subgroup.mem_centralizer_iff] at hh ⊢
      exact hh
    · simp [Subgroup.mem_centralizer_iff] at hh ⊢
      calc w * (g⁻¹ * h * g) = g⁻¹ * (g * w * g⁻¹) * (h * g) := by simp [mul_assoc]
        _ = g⁻¹ * ((g * w * g⁻¹) * h) * g := by simp [mul_assoc]
        _ = g⁻¹ * (h * (g * w * g⁻¹)) * g := by rw [hh]
        _ = (g⁻¹ * h * g) * w := by simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
  exact sol_congr ι.symm n

/-- In a commutative group, if `p` does not divide `m` then `p` does not divide the number of
solutions of `x ^ m = 1`. -/
lemma not_dvd_sol_of_comm {A : Type*} [Group A] [Finite A] (hcomm : ∀ x y : A, Commute x y)
    {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) : ¬ p ∣ sol A m := by
  by_contra h
  -- The `m`-torsion is a subgroup, and Cauchy's theorem would give an element of order `p` in it.
  let powHom : A →* A :=
    { toFun := fun g => g ^ m, map_one' := by simp,
      map_mul' := fun a b => (hcomm a b).mul_pow m }
  let S := powHom.ker
  have hpS : p ∣ Nat.card S := h
  haveI : Fintype S := Fintype.ofFinite S
  have hpS' : p ∣ Fintype.card S := by rwa [Nat.card_eq_fintype_card] at hpS
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card p hpS'
  have hx_pow_m : (x : A) ^ m = 1 := x.2
  exact hm (by
    have h1 : orderOf (x : A) ∣ m := orderOf_dvd_of_pow_eq_one hx_pow_m
    rwa [Subgroup.orderOf_coe x, hx_order] at h1)

/-- `gcd (p ^ a) N` is `p ^ min a (v_p N)`. -/
lemma gcd_prime_pow {p : ℕ} (hp : p.Prime) (a N : ℕ) (hN : N ≠ 0) :
    Nat.gcd (p ^ a) N = p ^ (min a (N.factorization p)) := by
  have h1 : Nat.factorization (Nat.gcd (p ^ a) N) p = min (Nat.factorization (p ^ a) p) (Nat.factorization N p) := by
    have := Nat.factorization_gcd (pow_ne_zero a hp.ne_zero) hN
    simp [this]
  rw [Nat.factorization_pow_self hp] at h1
  have hdvd : Nat.gcd (p ^ a) N ∣ p ^ a := Nat.gcd_dvd_left _ _
  have ha : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have hne : Nat.gcd (p ^ a) N ≠ 0 := by
    simp [Nat.gcd_eq_zero_iff, hN]
  -- Any divisor of p^a is a power of p
  have pow_form : ∀ d, d ∣ p ^ a → d ≠ 0 → ∃ k, d = p ^ k := by
    intro d hd hd0
    use d.factorization p
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
    have hsupp : d.factorization.support ⊆ {p} := by
      intro q hq
      rw [Finsupp.mem_support_iff] at hq
      rw [Finset.mem_singleton]
      -- q ∈ d.factorization.support means d.factorization q ≠ 0
      -- This implies q ∣ d (since q^(d.factorization q) ∣ d and d.factorization q ≥ 1)
      have hq_dvd : q ∣ d := Nat.dvd_trans (dvd_pow_self q (Nat.pos_of_ne_zero hq).ne') (Nat.ordProj_dvd d q)
      -- Since d ∣ p^a, we have q ∣ p^a
      have hq_dvd_pa : q ∣ p ^ a := Nat.dvd_trans hq_dvd hd
      -- Since q ∣ p^a and q is a natural number, if q is prime then q = p
      -- We need to show q is prime: this follows from q ∈ support of factorization
      have hq_prime : q.Prime := by
        by_contra hnp
        apply hq
        exact Nat.factorization_eq_zero_of_not_prime d hnp
      have hq_dvd_p : q ∣ p := Nat.Prime.dvd_of_dvd_pow hq_prime hq_dvd_pa
      exact Nat.prime_dvd_prime_iff_eq hq_prime hp |>.mp hq_dvd_p
    rw [Finsupp.prod_eq_single p (fun b hb hbp => by
      have hb_in_sup := Finsupp.mem_support_iff.mpr hb
      exact False.elim (hbp (Finset.mem_singleton.mp (hsupp hb_in_sup)))
    ) (fun _ => by simp)]
  obtain ⟨k, hk⟩ := pow_form _ hdvd hne
  rw [hk]
  congr 1
  have : (p ^ k).factorization p = min a (N.factorization p) := by rwa [← hk]
  rw [Nat.factorization_pow_self hp] at this
  exact this

/-- If `x ^ (p ^ a) = y` and `y` has order `p ^ k` then `x` has order `p ^ (a + k)`. -/
lemma orderOf_of_pow_eq [Finite G] {p a k : ℕ} (hp : p.Prime) (hk : 0 < k) {x y : G}
    (hy : orderOf y = p ^ k) (hxy : x ^ (p ^ a) = y) : orderOf x = p ^ (a + k) := by
  -- First show x ^ (p ^ (a + k)) = 1
  have hx_pow : x ^ (p ^ (a + k)) = 1 := by
    calc x ^ (p ^ (a + k)) = x ^ (p ^ a * p ^ k) := by rw [pow_add]
      _ = (x ^ (p ^ a)) ^ (p ^ k) := by rw [← pow_mul]
      _ = y ^ (p ^ k) := by rw [hxy]
      _ = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  -- So orderOf x divides p ^ (a + k)
  have hdiv : orderOf x ∣ p ^ (a + k) := orderOf_dvd_of_pow_eq_one hx_pow
  -- orderOf x is a power of p
  rw [Nat.dvd_prime_pow hp] at hdiv
  obtain ⟨m, hm_le, hm_eq⟩ := hdiv
  -- Use that orderOf (x ^ (p ^ a)) = orderOf x / gcd(orderOf x, p ^ a)
  have hy' : orderOf (x ^ (p ^ a)) = p ^ k := by rw [hxy, hy]
  -- Use orderOf_pow to relate orderOf (x ^ n) to orderOf x
  have hpow := orderOf_pow (x := x) (n := p ^ a)
  rw [hm_eq] at hpow
  rw [hpow] at hy'
  -- gcd(p^m, p^a) = p^(min m a)
  rw [Nat.gcd_comm] at hy'
  have hgcd : Nat.gcd (p ^ a) (p ^ m) = p ^ min a m := by
    rcases le_total a m with ham | ham
    · rw [min_eq_left ham]
      simp [Nat.gcd_eq_left (pow_dvd_pow p ham)]
    · rw [min_eq_right ham]
      simp [Nat.gcd_eq_right (pow_dvd_pow p ham)]
  rw [hgcd] at hy'
  -- So p^(m - min a m) = p^k, hence m - min a m = k
  have hminm : min a m ≤ m := min_le_right a m
  have hdiv_eq : p ^ k * p ^ min a m = p ^ m := by
    have h1 : p ^ min a m ∣ p ^ m := pow_dvd_pow p hminm
    rw [← Nat.mul_div_cancel' h1]
    simp [hy', Nat.mul_comm]
  rw [← pow_add] at hdiv_eq
  have hexp : k + min a m = m := Nat.pow_right_injective hp.one_lt hdiv_eq
  have hexp' : m - min a m = k := by omega
  -- Since k > 0, we have m > min a m, so m > a
  by_cases hm : m ≤ a
  · -- If m ≤ a, then min a m = m, so m - m = k = 0, contradicting k > 0
    rw [min_eq_right hm] at hexp
    simp at hexp
    linarith
  · -- If m > a, then min a m = a, so m - a = k, hence m = a + k
    push Not at hm
    rw [min_eq_left (le_of_lt hm)] at hexp
    rw [hm_eq]
    rw [← hexp]
    rw [add_comm]

/-- The solutions of `x ^ (p ^ a) = y` generating a fixed cyclic subgroup: there are exactly
`p ^ a` of them. -/
lemma card_fiber_zpowers [Fintype G] {p a k : ℕ} (hp : p.Prime) {y : G} (hk : 0 < k)
    (hy : orderOf y = p ^ k) {x₀ : G} (hx₀ : x₀ ^ (p ^ a) = y) :
    (univ.filter (fun x : G => x ^ (p ^ a) = y ∧ Subgroup.zpowers x = Subgroup.zpowers x₀)).card
      = p ^ a := by
  -- First establish that orderOf x₀ = p^(a+k)
  have hord : orderOf x₀ = p ^ (a + k) := orderOf_of_pow_eq hp hk hy hx₀
  let S := (univ.filter (fun x : G => x ^ (p ^ a) = y ∧ Subgroup.zpowers x = Subgroup.zpowers x₀))
  -- Define the map from Fin (p^a) to our set
  let f : Fin (p ^ a) → G := fun t => x₀ ^ (1 + t.val * p ^ k)
  -- Show that f maps into S
  have hf_in_S : ∀ t : Fin (p ^ a), f t ∈ S := by
    intro t
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · -- Show (f t) ^ (p ^ a) = y
      simp only [f]
      rw [← pow_mul, add_mul, one_mul]
      rw [pow_add, hx₀]
      rw [mul_assoc]
      have h1 : p ^ k * p ^ a = p ^ (a + k) := by ring
      rw [h1]
      have h2 : x₀ ^ (p ^ (a + k)) = 1 := by rw [← hord, pow_orderOf_eq_one]
      rw [mul_comm, pow_mul, h2, one_pow, mul_one]
    · -- Show zpowers (f t) = zpowers x₀
      -- This follows because gcd(1 + t*p^k, p^(a+k)) = 1
      apply le_antisymm
      · -- zpowers (f t) ≤ zpowers x₀
        apply Subgroup.zpowers_le.mpr
        simp only [f]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x₀) _
      · -- zpowers x₀ ≤ zpowers (f t)
        apply Subgroup.zpowers_le.mpr
        -- Need to show x₀ ∈ zpowers (x₀^(1 + t*p^k))
        -- This is true because gcd(1 + t*p^k, p^(a+k)) = 1
        simp only [f]
        -- x₀ = (x₀^(1 + t*p^k))^m for some m with m*(1 + t*p^k) ≡ 1 (mod p^(a+k))
        have hcop : Nat.Coprime (1 + t.val * p ^ k) (p ^ (a + k)) := by
          apply Nat.Coprime.pow_right
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          have hdvd : p ∣ t.val * p ^ k := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
          rw [Nat.dvd_add_left hdvd]
          exact Nat.Prime.not_dvd_one hp
        -- Use Euler's theorem: a^(φ(n)) ≡ 1 (mod n) when gcd(a, n) = 1
        let n := orderOf x₀
        have hn : n = p ^ (a + k) := hord
        have hnpos : 0 < n := Nat.pos_of_ne_zero (hn.symm ▸ pow_ne_zero _ hp.ne_zero)
        have hcop' : Nat.Coprime (1 + t.val * p ^ k) n := by rw [hn]; exact hcop
        -- The inverse of (1 + t*p^k) mod n is (1 + t*p^k)^(φ(n) - 1)
        have h_tot : (1 + t.val * p ^ k) ^ Nat.totient n ≡ 1 [MOD n] :=
          Nat.ModEq.pow_totient hcop'
        -- We claim x₀ = (x₀^(1 + t*p^k))^((1 + t*p^k)^(φ(n)-1))
        -- Let m = (1 + t*p^k)^(φ(n)-1)
        set m := (1 + t.val * p ^ k) ^ (Nat.totient n - 1) with hm_def
        use m
        -- Goal involves zpow (integer exponent) since zpowers uses zpow
        -- Convert zpow to pow
        simp only [zpow_natCast]
        -- Goal: (x₀ ^ (1 + ↑t * p ^ k)) ^ m = x₀
        -- Using pow_mul: (x₀ ^ A) ^ m = x₀ ^ (A * m)
        -- Note: after substituting hm_def, m = A^(φ-1), so we need pow_mul for (x₀^A)^(A^(φ-1))
        rw [hm_def]
        -- Goal is now: (x₀ ^ A) ^ (A ^ (φ-1)) = x₀ where A = 1 + ↑t * p ^ k
        have hφpos : 0 < Nat.totient n := Nat.totient_pos.mpr hnpos
        have heq : (1 + t.val * p ^ k) * (1 + t.val * p ^ k) ^ (Nat.totient n - 1) = (1 + t.val * p ^ k) ^ Nat.totient n := by
          rw [← pow_succ', Nat.sub_add_cancel hφpos]
        have pow_mul_applied : (x₀ ^ (1 + t.val * p ^ k)) ^ ((1 + t.val * p ^ k) ^ (Nat.totient n - 1))
                             = x₀ ^ ((1 + t.val * p ^ k) * (1 + t.val * p ^ k) ^ (Nat.totient n - 1)) := by
          exact (pow_mul x₀ (1 + t.val * p ^ k) ((1 + t.val * p ^ k) ^ (Nat.totient n - 1))).symm
        rw [pow_mul_applied, heq]
        -- Goal: x₀ ^ (1 + ↑t * p ^ k) ^ n.totient = x₀
        -- Since (1 + ↑t * p ^ k) ^ n.totient ≡ 1 (mod n) and x₀ ^ n = 1
        -- We have x₀ ^ ((1 + ↑t * p ^ k) ^ n.totient) = x₀ ^ 1 = x₀
        -- x₀^m = x₀^(m % n) when orderOf x₀ = n
        have key : x₀ ^ ((1 + t.val * p ^ k) ^ Nat.totient n) = x₀ ^ (((1 + t.val * p ^ k) ^ Nat.totient n) % n) := by
          rw [pow_mod_orderOf]
        rw [key]
        rw [h_tot]
        have h1lt : 1 < n := hn.symm ▸ Nat.one_lt_pow (by omega : a + k ≠ 0) hp.one_lt
        simp [Nat.mod_eq_of_lt h1lt]
  -- Now show f is a bijection between Fin (p^a) and S
  -- First, f is injective
  have hf_inj : Function.Injective f := by
    intro t t' h_eq
    simp only [f] at h_eq
    -- Use pow_right_inj: x^m = x^n ↔ m ≡ n (mod orderOf x) when x has finite order
    have hmod : (1 + t.val * p ^ k) ≡ (1 + t'.val * p ^ k) [MOD orderOf x₀] := by
      -- If x^m = x^n, then m ≡ n (mod orderOf x)
      -- This follows from x^(m-n) = 1 when m ≥ n, so orderOf x | (m-n)
      wlog h : 1 + t.val * p ^ k ≥ 1 + t'.val * p ^ k generalizing t t'
      · push Not at h
        exact (this h_eq.symm (le_of_lt h)).symm
      have hdiff : x₀ ^ (1 + t.val * p ^ k - (1 + t'.val * p ^ k)) = 1 := by
        have heq' : x₀ ^ (1 + t.val * p ^ k) = x₀ ^ (1 + t.val * p ^ k - (1 + t'.val * p ^ k)) * x₀ ^ (1 + t'.val * p ^ k) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h_eq] at heq'
        have := congr_arg (· * (x₀ ^ (1 + t'.val * p ^ k))⁻¹) heq'
        simp at this
        exact this.symm
      have hdvd : orderOf x₀ ∣ (1 + t.val * p ^ k) - (1 + t'.val * p ^ k) := orderOf_dvd_of_pow_eq_one hdiff
      simp only [add_tsub_add_eq_tsub_left] at hdvd
      rw [Nat.modEq_iff_dvd]
      simp_all
      have : (p ^ (a + k) : ℤ) ∣ (t'.val : ℤ) * p ^ k - (t.val : ℤ) * p ^ k := by
        have hdvd' : (p ^ (a + k) : ℤ) ∣ (t.val : ℤ) * p ^ k - (t'.val : ℤ) * p ^ k := by
          exact_mod_cast hdvd
        exact dvd_sub_comm.mp hdvd'
      exact this
    -- Simplify: t * p^k ≡ t' * p^k (mod p^(a+k))
    -- So p^a | (t - t')
    have ht_eq : t.val = t'.val := by
      -- From hmod: (1 + t*p^k) ≡ (1 + t'*p^k) [MOD p^(a+k)]
      -- So t*p^k ≡ t'*p^k [MOD p^(a+k)], hence p^(a+k) | (t - t')*p^k in ℤ
      rw [hord] at hmod
      -- We need to show t.val = t'.val given that t, t' < p^a and the modular condition
      -- The condition implies p^a | (t - t') in ℤ
      have key : (p ^ (a + k) : ℤ) ∣ ((t.val : ℤ) - (t'.val : ℤ)) * p ^ k := by
        have hmod' : ((1 + t.val * p ^ k : ℕ) : ℤ) ≡ ((1 + t'.val * p ^ k : ℕ) : ℤ) [ZMOD (p ^ (a + k) : ℤ)] := by
          rw [Int.ModEq]
          norm_cast
        have hsimp : ((t.val : ℤ) * p ^ k) ≡ ((t'.val : ℤ) * p ^ k) [ZMOD (p ^ (a + k) : ℤ)] := by
          rw [Int.ModEq] at hmod' ⊢
          have h1 : ((1 + t.val * p ^ k : ℕ) : ℤ) = 1 + (t.val : ℤ) * p ^ k := by push_cast; ring
          have h2 : ((1 + t'.val * p ^ k : ℕ) : ℤ) = 1 + (t'.val : ℤ) * p ^ k := by push_cast; ring
          rw [h1, h2] at hmod'
          have hpow_gt : 1 < (p : ℤ) ^ (a + k) := by
            norm_cast; exact one_lt_pow₀ hp.one_lt (by omega : a + k ≠ 0)
          -- hmod' says (1 + t.val * p^k) % n = (1 + t'.val * p^k) % n in ℤ
          -- We need t.val * p^k % n = t'.val * p^k % n in ℤ
          -- (1 + a) % n = (1 + b) % n → a % n = b % n
          -- Because (1 + a) ≡ (1 + b) (mod n) → a ≡ b (mod n)
          have hmod2 : ((1 : ℤ) + (t.val : ℤ) * p ^ k) ≡ ((1 : ℤ) + (t'.val : ℤ) * p ^ k) [ZMOD (p : ℤ) ^ (a + k)] := by
            rw [Int.ModEq, hmod']
          have hmod3 := hmod2.sub_right 1
          simp at hmod3
          exact hmod3
        rw [Int.modEq_iff_dvd] at hsimp
        have h' := dvd_sub_comm.mp hsimp
        rw [sub_mul]
        exact h'
      have hdvd' : (p ^ a : ℤ) ∣ (t.val : ℤ) - (t'.val : ℤ) := by
        have : (p ^ (a + k) : ℤ) = (p ^ a : ℤ) * (p ^ k : ℤ) := by ring
        rw [this] at key
        exact Int.mul_dvd_mul_iff_right (pow_ne_zero k (Nat.cast_ne_zero.mpr hp.ne_zero)) |>.mp key
      -- Since t, t' < p^a and p^a | (t - t'), we have t = t'
      have ht_bound : t.val < p ^ a := t.is_lt
      have ht'_bound : t'.val < p ^ a := t'.is_lt
      have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
      -- From hdvd' and the bounds, conclude t.val = t'.val
      have habs : Int.natAbs ((t.val : ℤ) - (t'.val : ℤ)) < p ^ a := by
        omega
      have hdvd_nat : p ^ a ∣ Int.natAbs ((t.val : ℤ) - (t'.val : ℤ)) := by
        exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd')
      have hzero : Int.natAbs ((t.val : ℤ) - (t'.val : ℤ)) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_nat habs
      omega
    exact Fin.val_injective ht_eq
  -- Show S = image of f, then use card_image_of_injective
  have hf_image_eq_S : S = Finset.image f Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · -- S ⊆ image f univ: need surjectivity
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      obtain ⟨hx_pow, hx_zpow⟩ := hx
      -- x ∈ zpowers x₀, so x = x₀^m for some m
      have hx_mem : x ∈ Subgroup.zpowers x₀ := hx_zpow ▸ Subgroup.mem_zpowers x
      obtain ⟨m, hm⟩ := hx_mem
      -- hm : x₀ ^ m = x
      -- Reduce m to [0, orderOf x₀)
      let m' := Int.toNat (m % orderOf x₀)
      have hord_pos : (0 : ℤ) < orderOf x₀ := by exact_mod_cast orderOf_pos x₀
      have hm'_lt : m' < orderOf x₀ := by
        simp only [m']
        have h1 : 0 ≤ m % orderOf x₀ := Int.emod_nonneg m hord_pos.ne'
        have h2 : m % orderOf x₀ < orderOf x₀ := Int.emod_lt_of_pos m hord_pos
        omega
      have hx_eq : x = x₀ ^ m' := by
        rw [← hm]
        have heq : m = (m % orderOf x₀ : ℤ) + orderOf x₀ * (m / orderOf x₀) := by
          linarith [Int.emod_add_mul_ediv m (orderOf x₀)]
        have h_nonneg : 0 ≤ m % orderOf x₀ := Int.emod_nonneg m hord_pos.ne'
        show x₀ ^ m = x₀ ^ m'
        rw [heq, zpow_add, zpow_mul]
        have h1 : x₀ ^ (orderOf x₀ : ℤ) = 1 := by
          rw [zpow_natCast, pow_orderOf_eq_one]
        have h2 : (x₀ ^ (orderOf x₀ : ℤ)) ^ (m / (orderOf x₀ : ℤ)) = 1 := by
          rw [h1, one_zpow]
        rw [h2, mul_one]
        -- Now need: x₀ ^ (m % orderOf x₀) = x₀ ^ m'
        -- Since m' = (m % orderOf x₀).toNat and m % orderOf x₀ ≥ 0
        rw [← zpow_natCast, Int.toNat_of_nonneg h_nonneg]
      -- Since x^(p^a) = y = x₀^(p^a), we have x₀^(m'*p^a) = x₀^(p^a)
      -- So m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
      -- Hence p^k | (m' - 1), so m' = 1 + t*p^k for some t
      have hpow_eq : x₀ ^ (m' * p ^ a) = x₀ ^ (p ^ a) := by
        calc x₀ ^ (m' * p ^ a) = (x₀ ^ m') ^ (p ^ a) := by rw [← pow_mul]
          _ = x ^ (p ^ a) := by rw [← hx_eq]
          _ = y := hx_pow
          _ = x₀ ^ (p ^ a) := hx₀.symm
      -- From hpow_eq: m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
      -- So p^(a+k) | (m' - 1)*p^a, hence p^k | (m' - 1)
      -- Thus m' = 1 + t*p^k for some t with 0 ≤ t < p^a
      -- x₀^(m'*p^a) = x₀^(p^a) with orderOf x₀ = p^(a+k)
      -- For finite order elements, x^A = x^B implies A ≡ B (mod orderOf x)
      -- From hpow_eq: m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
      -- So p^(a+k) | (m' - 1)*p^a, hence p^k | (m' - 1)
      -- Thus m' = 1 + t*p^k for some t with 0 ≤ t < p^a
      -- x₀^(m'*p^a) = x₀^(p^a) with orderOf x₀ = p^(a+k)
      -- For finite order elements, x^A = x^B implies A ≡ B (mod orderOf x)
      have hm'_eq : m' * p ^ a ≡ p ^ a [MOD p ^ (a + k)] := by
        -- x₀^(m'*p^a) = x₀^(p^a) implies m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
        rcases le_total (m' * p ^ a) (p ^ a) with hle | hge
        · -- m' * p^a ≤ p^a case
          have hdiff : x₀ ^ (p ^ a - m' * p ^ a) = 1 := by
            have heq' : x₀ ^ (p ^ a) = x₀ ^ (p ^ a - m' * p ^ a) * x₀ ^ (m' * p ^ a) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hpow_eq] at heq'
            have := congr_arg (· * (x₀ ^ (m' * p ^ a))⁻¹) heq'
            simp at this
            exact this
          have hdvd : orderOf x₀ ∣ p ^ a - m' * p ^ a := orderOf_dvd_of_pow_eq_one hdiff
          rw [hord] at hdvd
          rw [Nat.modEq_iff_dvd]
          exact_mod_cast hdvd
        · -- p^a ≤ m' * p^a case
          have hdiff : x₀ ^ (m' * p ^ a - p ^ a) = 1 := by
            have heq' : x₀ ^ (m' * p ^ a) = x₀ ^ (m' * p ^ a - p ^ a) * x₀ ^ (p ^ a) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hpow_eq] at heq'
            have := congr_arg (· * (x₀ ^ (p ^ a))⁻¹) heq'
            simp at this
            exact this.symm
          have hdvd : orderOf x₀ ∣ m' * p ^ a - p ^ a := orderOf_dvd_of_pow_eq_one hdiff
          rw [hord] at hdvd
          rw [Nat.modEq_iff_dvd]
          have hdvd' : (p ^ (a + k) : ℤ) ∣ (m' : ℤ) * p ^ a - p ^ a := by norm_cast
          push_cast
          exact dvd_sub_comm.mp hdvd'
      -- First show m' ≥ 1 (otherwise x₀^0 = 1 = y contradicts orderOf y = p^k with k ≥ 1)
      have hm'_pos : m' ≥ 1 := by
        by_contra hm'0
        push Not at hm'0
        have hm'_eq0 : m' = 0 := by omega
        rw [hm'_eq0, zero_mul] at hpow_eq
        have h1 : x₀ ^ p ^ a = 1 := by rw [hpow_eq.symm]; exact pow_zero x₀
        have : orderOf (x₀ ^ p ^ a) = 1 := by rw [h1]; exact orderOf_one
        rw [hx₀] at this
        rw [hy] at this
        have hk0 : k = 0 := (Nat.pow_right_injective hp.one_lt).eq_iff.mp this
        omega
      -- From hm'_eq: p^(a+k) | (m' - 1) * p^a
      have hdvd : p ^ (a + k) ∣ (m' - 1) * p ^ a := by
        have h1 : (m' - 1) * p ^ a = m' * p ^ a - p ^ a := by
          rw [tsub_mul, one_mul]
        rw [h1]
        have hge : m' * p ^ a ≥ p ^ a := by
          have : 1 ≤ m' := hm'_pos
          nlinarith [pow_pos hp.pos a]
        -- m' * p^a ≡ p^a [MOD p^(a+k)] means p^(a+k) | (m' * p^a - p^a) = (m' - 1) * p^a
        have hm'_eq' : (m' * p ^ a : ℤ) ≡ (p ^ a : ℤ) [ZMOD (p ^ (a + k) : ℤ)] := by
          simp only [Int.ModEq]
          norm_cast
        have hdvd_int : (p ^ (a + k) : ℤ) ∣ ((m' : ℤ) * p ^ a - p ^ a) := Int.ModEq.dvd hm'_eq'.symm
        have hdvd_nat : (p ^ (a + k) : ℤ) ∣ ((m' * p ^ a - p ^ a : ℕ) : ℤ) := by
          rw [Int.ofNat_sub hge]
          exact hdvd_int
        norm_cast at hdvd_nat
      -- From p^(a+k) ∣ (m' - 1) * p^a, we get p^k ∣ (m' - 1)
      have hdvd' : p ^ k ∣ (m' - 1) := by
        have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
        have heq : p ^ (a + k) = p ^ a * p ^ k := by ring
        rw [heq] at hdvd
        rw [mul_comm (m' - 1)] at hdvd
        exact Nat.mul_dvd_mul_iff_left hpa_pos |>.mp hdvd
      -- So m' = 1 + t * p^k for some t
      obtain ⟨t, ht⟩ := hdvd'
      -- Since m' < p^(a+k), we have t < p^a
      have hm'_lt' : m' < p ^ (a + k) := hord ▸ hm'_lt
      have ht_lt : t < p ^ a := by
        have hm'_eq' : m' = 1 + t * p ^ k := by
          have := ht
          rw [mul_comm] at this
          omega
        rw [hm'_eq'] at hm'_lt'
        have hpow_eq : p ^ (a + k) = p ^ a * p ^ k := by ring
        rw [hpow_eq] at hm'_lt'
        have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
        nlinarith
      -- x = x₀^m' = x₀^(1 + t*p^k) = f ⟨t, ht_lt⟩
      use ⟨t, ht_lt⟩
      simp only [f]
      rw [hx_eq]
      congr 1
      have := ht
      rw [mul_comm] at this
      omega
    · -- card (image f univ) ≤ card S
      have h1 : #(Finset.image f Finset.univ) = p ^ a := by
        rw [Finset.card_image_of_injective _ hf_inj]
        simp
      have h2 : #(Finset.image f Finset.univ) ≤ #S :=
        Finset.card_le_card (Finset.image_subset_iff.mpr fun t _ => hf_in_S t)
      linarith
  show #S = p ^ a
  rw [hf_image_eq_S, Finset.card_image_of_injective _ hf_inj]
  simp

/-- **Key counting lemma.**  If `y` has order `p ^ k` with `k ≥ 1`, then the number of solutions
of `x ^ (p ^ a) = y` is divisible by `p ^ a`.  Indeed every solution `x` has order `p ^ (a + k)`,
and for each cyclic subgroup `C` of order `p ^ (a+k)` containing `y` the solutions lying in `C`
form a coset of `{z ∈ C | z ^ (p ^ a) = 1}`, which has exactly `p ^ a` elements. -/
lemma solEq_prime_pow_dvd [Finite G] {p a k : ℕ} (hp : p.Prime) {y : G}
    (hk : 0 < k) (hy : orderOf y = p ^ k) : p ^ a ∣ solEq (p ^ a) y := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : DecidableEq (Subgroup G) := inferInstance
  rw [solEq_eq_card_filter]
  let S := univ.filter (fun x : G => x ^ (p ^ a) = y)
  -- For x ∈ S, we have x ^ (p^a) = y, so by orderOf_of_pow_eq, orderOf x = p^(a+k)
  have hx_order : ∀ x ∈ S, orderOf x = p ^ (a + k) := by
    intro x hx
    simp [S] at hx
    exact orderOf_of_pow_eq hp hk hy hx
  -- Partition S by zpowers
  let f : G → Subgroup G := fun x => Subgroup.zpowers x
  have h_card := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := S.image f)
  have h_maps : Set.MapsTo f ↑S ↑(S.image f) := by
    intro x hx
    exact Finset.mem_image_of_mem f hx
  rw [h_card h_maps]
  apply Finset.dvd_sum
  intro C hC
  rw [Finset.mem_image] at hC
  obtain ⟨x₀, hx₀S, rfl⟩ := hC
  have hx₀S' : x₀ ^ (p ^ a) = y := by simpa [S] using hx₀S
  have h_card_fiber := card_fiber_zpowers (p := p) (a := a) (k := k) hp hk hy hx₀S'
  simp [S] at hx₀S
  have h_eq : {a ∈ S | f a = f x₀} = (univ.filter (fun x : G => x ^ (p ^ a) = y ∧ Subgroup.zpowers x = Subgroup.zpowers x₀)) := by
    simp [S, f, Finset.filter_filter]
  rw [h_eq]
  convert h_card_fiber.symm.dvd using 1
  congr 1
  ext x
  simp

/-- Fibering the solutions of `x ^ (a * b) = 1` over the `a`-th power map. -/
lemma sol_mul_eq_sum_solEq [Fintype G] (a b : ℕ) :
    sol G (a * b) = ∑ y ∈ univ.filter (fun y : G => y ^ b = 1), solEq a y := by
  rw [sol_eq_card_filter]
  have hmaps : ∀ x ∈ univ.filter (fun x : G => x ^ (a * b) = 1),
      x ^ a ∈ univ.filter (fun y : G => y ^ b = 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← pow_mul]
    exact hx
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
  rw [solEq_eq_card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rw [pow_mul, h, hy]

/-- `sol G (p ^ (a+1)) ≡ sol G (p ^ a)` modulo `p ^ a`. -/
lemma sol_modEq_succ [Fintype G] {p a : ℕ} (hp : p.Prime) :
    sol G (p ^ (a + 1)) ≡ sol G (p ^ a) [MOD p ^ a] := by
  rw [pow_succ', mul_comm, sol_mul_eq_sum_solEq (p ^ a) p]
  set S := Finset.filter (fun y : G => y ^ p = 1) Finset.univ with hS
  set T := Finset.filter (fun y : G => y ^ p = 1 ∧ y ≠ 1) Finset.univ with hT
  have hS_eq : S = {1} ∪ T := by
    ext x
    simp only [hS, hT, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hx : x = 1 <;> simp [hx]
  have h1_disj : Disjoint ({1} : Finset G) T := by
    rw [Finset.disjoint_left]
    simp [hT]
  rw [hS_eq, Finset.sum_union h1_disj]
  simp [solEq, sol]
  apply Finset.dvd_sum
  intro y hy
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have hy_order : orderOf y = p := by
    have h := orderOf_dvd_of_pow_eq_one hy.1
    rw [Nat.dvd_prime hp] at h
    cases h with
    | inl h => exact absurd (orderOf_eq_one_iff.mp h) hy.2
    | inr h => exact h
  have hk : orderOf y = p ^ (1 : ℕ) := by rw [hy_order, pow_one]
  have := @solEq_prime_pow_dvd _ _ _ p a 1 hp y one_pos hk
  rwa [solEq, Nat.card_eq_fintype_card] at this

/-- `sol G (p ^ b) ≡ sol G (p ^ a)` modulo `p ^ a` for `a ≤ b`. -/
lemma sol_modEq_le [Fintype G] {p a b : ℕ} (hp : p.Prime) (hab : a ≤ b) :
    sol G (p ^ b) ≡ sol G (p ^ a) [MOD p ^ a] := by
  have step : ∀ n, sol G (p ^ (n + 1)) ≡ sol G (p ^ n) [MOD p ^ n] := fun n => sol_modEq_succ hp
  suffices h : ∀ m, a ≤ m → sol G (p ^ m) ≡ sol G (p ^ a) [MOD p ^ a] by exact h b hab
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have h2 := Nat.ModEq.of_dvd (pow_dvd_pow p hn) (step n)
    exact h2.trans ih

/-- Chinese remainder exponents used for the primary decomposition. -/
lemma exists_crt_exponents {p α u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) (hu0 : 0 < u) :
    ∃ e f : ℕ, p ^ α ∣ e ∧ u ∣ f ∧ e ≡ 1 [MOD u] ∧ f ≡ 1 [MOD p ^ α] ∧
      (e + f) ≡ 1 [MOD p ^ α * u] := by
  have hcop : Nat.Coprime (p ^ α) u := by
    have : Nat.Coprime p u := hp.coprime_iff_not_dvd.mpr hu
    exact Nat.Coprime.pow_left α this
  -- Use Int.gcd_eq_gcd_ab to get Bezout coefficients
  have hgcd : Int.gcd (p ^ α) u = 1 := by exact_mod_cast hcop
  have zabr := Int.gcd_eq_gcd_ab (p ^ α) u
  rw [hgcd] at zabr
  -- zabr : 1 = (p^α) * gcdA + u * gcdB
  set a := Int.gcdA (p ^ α : ℕ) u
  set b := Int.gcdB (p ^ α : ℕ) u
  have zab : ↑p ^ α * a + ↑u * b = 1 := by
    have hpc : ((p ^ α : ℕ) : ℤ) = (p : ℤ) ^ α := by push_cast; ring
    simp only [a, b, hpc]
    push_cast at zabr
    linarith
  -- From zab: a * p^α ≡ 1 [MOD u] and b * u ≡ 1 [MOD p^α]
  have ha_mod : ↑p ^ α * a ≡ 1 [ZMOD ↑u] := by
    rw [Int.modEq_iff_dvd]
    have : (1 : ℤ) - ↑p ^ α * a = ↑u * b := by linarith
    rw [this]
    exact dvd_mul_right _ _
  have hb_mod : ↑u * b ≡ 1 [ZMOD ↑p ^ α] := by
    rw [Int.modEq_iff_dvd]
    have : (1 : ℤ) - ↑u * b = ↑p ^ α * a := by linarith
    rw [this]
    exact dvd_mul_right _ _
  -- Define e = (a % u).toNat * p^α and f = (b % p^α).toNat * u
  set k := (a % ↑u).toNat with hk_def
  set m := (b % ↑(p ^ α)).toNat with hm_def
  use k * p ^ α, m * u
  -- First prove k * p ^ α ≡ 1 [MOD u]
  have hk_pa : k * p ^ α ≡ 1 [MOD u] := by
    have hu_pos : (0 : ℤ) < u := by positivity
    have h_anonneg : 0 ≤ a % ↑u := Int.emod_nonneg _ hu_pos.ne'
    have hk_eq : (k : ℤ) = a % ↑u := Int.toNat_of_nonneg h_anonneg
    have : (k : ℤ) * p ^ α ≡ a % ↑u * p ^ α [ZMOD ↑u] := by simp [hk_eq]
    have h2 : (a % ↑u : ℤ) * p ^ α ≡ a * p ^ α [ZMOD ↑u] := by
      exact Int.ModEq.mul_right _ (Int.emod_emod_of_dvd a (dvd_refl _))
    have h3 : (a : ℤ) * p ^ α ≡ 1 [ZMOD ↑u] := by simpa [mul_comm] using ha_mod
    have h4 : (k : ℤ) * p ^ α ≡ 1 [ZMOD ↑u] := this.trans (h2.trans h3)
    rw [← Int.natCast_modEq_iff]
    convert h4 using 2 <;> (push_cast; try ring)
  -- Then prove m * u ≡ 1 [MOD p^α]
  have hm_u : m * u ≡ 1 [MOD p ^ α] := by
    have hp_pos : (0 : ℕ) < p := hp.pos
    have hpa_pos : (0 : ℤ) < p ^ α := by positivity
    have h_banonneg : 0 ≤ b % ↑(p ^ α) := Int.emod_nonneg _ hpa_pos.ne'
    have hm_eq : (m : ℤ) = b % ↑(p ^ α) := Int.toNat_of_nonneg h_banonneg
    have : (m : ℤ) * u ≡ b % ↑(p ^ α) * u [ZMOD ↑p ^ α] := by simp [hm_eq]
    have h2 : (b % ↑(p ^ α) : ℤ) * u ≡ b * u [ZMOD ↑p ^ α] := Int.ModEq.mul_right _ (Int.emod_emod_of_dvd b (dvd_refl _))
    have h3 : (b : ℤ) * u ≡ 1 [ZMOD ↑p ^ α] := by simpa [mul_comm] using hb_mod
    have h4 : (m : ℤ) * u ≡ 1 [ZMOD ↑p ^ α] := this.trans (h2.trans h3)
    simp only [Int.ModEq] at h4
    exact_mod_cast h4
  refine ⟨dvd_mul_left _ _, dvd_mul_left _ _, hk_pa, hm_u, ?_⟩
  -- Goal: k * p ^ α + m * u ≡ 1 [MOD p^α * u]
  · -- k * p^α ≡ 1 [MOD u] and k * p^α ≡ 0 [MOD p^α]
    -- m * u ≡ 1 [MOD p^α] and m * u ≡ 0 [MOD u]
    -- So k * p^α + m * u ≡ 1 [MOD p^α] and ≡ 1 [MOD u]
    -- By CRT, k * p^α + m * u ≡ 1 [MOD p^α * u]
    have hk0 : k * p ^ α ≡ 0 [MOD p ^ α] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    have hm0 : m * u ≡ 0 [MOD u] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    have hpa_pos : 0 < p ^ α := Nat.one_le_pow _ _ hp.pos
    have hu_pos : 0 < u := hu0
    -- Prove k * p^α + m * u ≡ 1 [MOD p^α]
    have hab_pa : k * p ^ α + m * u ≡ 1 [MOD p ^ α] := by
      calc k * p ^ α + m * u ≡ 0 + 1 [MOD p ^ α] := Nat.ModEq.add hk0 hm_u
        _ = 1 := by ring
    -- Prove k * p^α + m * u ≡ 1 [MOD u]
    have hab_u : k * p ^ α + m * u ≡ 1 [MOD u] := by
      calc k * p ^ α + m * u ≡ 1 + 0 [MOD u] := Nat.ModEq.add hk_pa hm0
        _ = 1 := by ring
    -- By CRT: since gcd(p^α, u) = 1, a ≡ b [MOD p^α] and a ≡ b [MOD u] implies a ≡ b [MOD p^α * u]
    rw [Nat.ModEq] at hab_pa hab_u ⊢
    -- Need to show: (k * p^α + m * u) % (p^α * u) = 1 % (p^α * u)
    -- We have: (k * p^α + m * u) % p^α = 1 % p^α and (k * p^α + m * u) % u = 1 % u
    -- By CRT this implies (k * p^α + m * u) % (p^α * u) = 1 % (p^α * u)
    -- hab_pa : (k * p^α + m*u) % p^α = 1 % p^α
    -- hab_u : (k * p^α + m*u) % u = 1 % u
    -- Need: (k * p^α + m*u) % (p^α * u) = 1 % (p^α * u)
    -- hab_pa : (k * p^α + m*u) % p^α = 1 % p^α
    -- hab_u : (k * p^α + m*u) % u = 1 % u
    -- Need: (k * p^α + m*u) % (p^α * u) = 1 % (p^α * u)
    -- Use Int conversion
    have hi : (k * p ^ α + m * u : ℤ) % (p ^ α * u : ℤ) = (1 : ℤ) % (p ^ α * u : ℤ) := by
      have hab_pa' : (k * p ^ α + m * u : ℤ) ≡ 1 [ZMOD p ^ α] := by
        rw [Int.ModEq]; exact_mod_cast hab_pa
      have hab_u' : (k * p ^ α + m * u : ℤ) ≡ 1 [ZMOD u] := by
        rw [Int.ModEq]; exact_mod_cast hab_u
      -- Need: p^α * u ∣ (k*p^α + m*u - 1)
      -- From hab_pa': p^α ∣ (k*p^α + m*u - 1)
      -- From hab_u': u ∣ (k*p^α + m*u - 1)
      -- Since gcd(p^α, u) = 1, p^α * u ∣ (k*p^α + m*u - 1)
      -- Int.modEq_iff_dvd: a ≡ b [ZMOD n] ↔ n ∣ (b - a)
      rw [Int.modEq_iff_dvd] at hab_pa' hab_u'
      have hcop' : IsCoprime (p ^ α : ℤ) u := by exact_mod_cast hcop
      have hdiv : (p ^ α : ℤ) * u ∣ (1 - (k * p ^ α + m * u)) := hcop'.mul_dvd hab_pa' hab_u'
      have hdiv' : (p ^ α : ℤ) * u ∣ (k * p ^ α + m * u - 1) := by
        exact dvd_sub_comm.mp hdiv
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact Int.emod_eq_zero_of_dvd hdiv'
    exact_mod_cast hi

/-- If `x ^ m = 1` and `m ∣ k` then `x ^ k = 1`. -/
lemma pow_eq_one_of_dvd_of_pow_eq_one {x : G} {m k : ℕ} (hx : x ^ m = 1) (hmk : m ∣ k) :
    x ^ k = 1 := by
  obtain ⟨c, rfl⟩ := hmk
  rw [pow_mul, hx, one_pow]

/-- If `x ^ m = 1` and `k ≡ 1 [MOD m]` then `x ^ k = x`. -/
lemma pow_eq_self_of_modEq {x : G} {m k : ℕ} (hx : x ^ m = 1) (hk : k ≡ 1 [MOD m]) :
    x ^ k = x := by
  have hord : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hx
  have hk' : k ≡ 1 [MOD orderOf x] := hk.of_dvd hord
  calc x ^ k = x ^ 1 := pow_eq_pow_iff_modEq.mpr hk'
    _ = x := pow_one x

/-- If `x ^ (p ^ α * u) = 1` and `u ∣ f`, then `x ^ f` is killed by `p ^ α`. -/
lemma sol_aux_pow_f_eq_one {x : G} {p α u f : ℕ} (hf : u ∣ f) (hx : x ^ (p ^ α * u) = 1) :
    (x ^ f) ^ (p ^ α) = 1 := by
  rw [← pow_mul]
  obtain ⟨c, rfl⟩ := hf
  exact pow_eq_one_of_dvd_of_pow_eq_one hx ⟨c, by ring⟩

/-- A commuting product of a `p'`-element and a `p`-element is killed by `p ^ α * u`. -/
lemma sol_aux_mul_pow_eq_one {w v : G} {p α u : ℕ} (hw : w ^ u = 1) (hv : v ^ (p ^ α) = 1)
    (hc : Commute w v) : (w * v) ^ (p ^ α * u) = 1 := by
  rw [hc.mul_pow, pow_eq_one_of_dvd_of_pow_eq_one hw ⟨p ^ α, by ring⟩,
    pow_eq_one_of_dvd_of_pow_eq_one hv ⟨u, rfl⟩, one_mul]

/-- Raising a commuting product to the exponent `e` recovers the `p'`-part. -/
lemma sol_aux_mul_pow_e {w v : G} {p α u e : ℕ} (he : p ^ α ∣ e) (he1 : e ≡ 1 [MOD u])
    (hw : w ^ u = 1) (hv : v ^ (p ^ α) = 1) (hc : Commute w v) : (w * v) ^ e = w := by
  rw [hc.mul_pow, pow_eq_self_of_modEq hw he1, pow_eq_one_of_dvd_of_pow_eq_one hv he, mul_one]

/-- Raising a commuting product to the exponent `f` recovers the `p`-part. -/
lemma sol_aux_mul_pow_f {w v : G} {p α u f : ℕ} (hf : u ∣ f) (hf1 : f ≡ 1 [MOD p ^ α])
    (hw : w ^ u = 1) (hv : v ^ (p ^ α) = 1) (hc : Commute w v) : (w * v) ^ f = v := by
  rw [hc.mul_pow, pow_eq_self_of_modEq hv hf1, pow_eq_one_of_dvd_of_pow_eq_one hw hf, one_mul]

/-- The two parts multiply back to the original element. -/
lemma sol_aux_pow_e_mul_pow_f {x : G} {p α u e f : ℕ} (hef : (e + f) ≡ 1 [MOD p ^ α * u])
    (hx : x ^ (p ^ α * u) = 1) : x ^ e * x ^ f = x := by
  rw [← pow_add]
  exact pow_eq_self_of_modEq hx hef

/-- The fibre of the map `x ↦ x ^ e` over `w` is in bijection with the set of solutions of
`v ^ (p ^ α) = 1` commuting with `w`, via `x ↦ x ^ f` with inverse `v ↦ w * v`. -/
lemma sol_mul_eq_sum_fiber [Fintype G] {p α u e f : ℕ}
    (he : p ^ α ∣ e) (hf : u ∣ f) (he1 : e ≡ 1 [MOD u]) (hf1 : f ≡ 1 [MOD p ^ α])
    (hef : (e + f) ≡ 1 [MOD p ^ α * u]) (w : G) (hw : w ^ u = 1) :
    ((univ.filter (fun x : G => x ^ (p ^ α * u) = 1)).filter (fun x : G => x ^ e = w)).card
      = (univ.filter (fun v : G => v ^ (p ^ α) = 1 ∧ Commute w v)).card := by
  refine Finset.card_bij' (fun x _ => x ^ f) (fun v _ => w * v) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨sol_aux_pow_f_eq_one hf hx.1, ?_⟩
    rw [← hx.2]
    exact (Commute.refl x).pow_pow e f
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨sol_aux_mul_pow_eq_one hw hv.1 hv.2, sol_aux_mul_pow_e he he1 hw hv.1 hv.2⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h := sol_aux_pow_e_mul_pow_f hef hx.1
    rw [hx.2] at h
    exact h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact sol_aux_mul_pow_f hf hf1 hw hv.1 hv.2

/-- The bijection `x ↦ (x ^ e, x ^ f)` between solutions of `x ^ (p ^ α * u) = 1` and pairs
consisting of a solution `w` of `w ^ u = 1` and a solution `v` of `v ^ (p ^ α) = 1` commuting
with `w`. -/
lemma sol_mul_eq_sum_aux [Fintype G] {p α u e f : ℕ}
    (he : p ^ α ∣ e) (hf : u ∣ f) (he1 : e ≡ 1 [MOD u]) (hf1 : f ≡ 1 [MOD p ^ α])
    (hef : (e + f) ≡ 1 [MOD p ^ α * u]) :
    sol G (p ^ α * u) = ∑ w ∈ univ.filter (fun w : G => w ^ u = 1),
        (univ.filter (fun v : G => v ^ (p ^ α) = 1 ∧ Commute w v)).card := by
  rw [sol_eq_card_filter]
  have hmaps : ∀ x ∈ univ.filter (fun x : G => x ^ (p ^ α * u) = 1),
      x ^ e ∈ univ.filter (fun w : G => w ^ u = 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← pow_mul]
    exact pow_eq_one_of_dvd_of_pow_eq_one hx (mul_dvd_mul_right he u)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact sol_mul_eq_sum_fiber he hf he1 hf1 hef w hw

/-- Counting solutions in the centralizer of `w`. -/
lemma card_commuting_sol_eq [Fintype G] (w : G) (n : ℕ) :
    (univ.filter (fun v : G => v ^ n = 1 ∧ Commute w v)).card
      = sol ↥(Subgroup.centralizer ({w} : Set G)) n := by
  have he : {v : G // v ^ n = 1 ∧ Commute w v}
      ≃ {x : ↥(Subgroup.centralizer ({w} : Set G)) // x ^ n = 1} :=
    { toFun := fun x =>
        ⟨⟨x.val, by
            rw [Subgroup.mem_centralizer_iff]
            rintro y rfl
            exact x.property.2⟩,
          Subtype.ext (by simpa using x.property.1)⟩
      invFun := fun x =>
        ⟨x.val.val, ⟨by
            have h := congrArg Subtype.val x.prop
            simpa using h,
          (Subgroup.mem_centralizer_iff.mp x.val.property) w rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [sol, ← Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Primary decomposition identity.**  Writing `n = p ^ α * u` with `p ∤ u`, every element of `G`
factors uniquely as a commuting product of a `p`-element and a `p'`-element; this gives a bijection
between the solutions of `x ^ n = 1` and the pairs `(w, v)` where `w ^ u = 1` and `v` lies in the
centralizer of `w` with `v ^ (p ^ α) = 1`. -/
lemma sol_mul_eq_sum [Fintype G] {p α u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    sol G (p ^ α * u) =
      ∑ w ∈ univ.filter (fun w : G => w ^ u = 1),
        sol ↥(Subgroup.centralizer ({w} : Set G)) (p ^ α) := by
  obtain ⟨e, f, he, hf, he1, hf1, hef⟩ :=
    exists_crt_exponents hp hu (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p)))
  rw [sol_mul_eq_sum_aux he hf he1 hf1 hef]
  exact Finset.sum_congr rfl fun w _ => card_commuting_sol_eq w (p ^ α)

/-- The size of a conjugacy class is the index of the centralizer. -/
lemma card_conj_class [Fintype G] (w : G) :
    (univ.filter (fun x : G => IsConj w x)).card = (Subgroup.centralizer ({w} : Set G)).index := by
  have h : (univ.filter (fun x : G => IsConj w x)) = {g * w * g⁻¹ | g : G} := by
    ext x
    simp [IsConj, SemiconjBy]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc (c : G) * w * (c : G)⁻¹ = (x * c) * (c : G)⁻¹ := by rw [hc]
        _ = x * (c * (c : G)⁻¹) := by group
        _ = x := by simp
    · rintro ⟨g, hg⟩
      use ⟨g, g⁻¹, by simp, by simp⟩
      simp [← hg]
  simp
  rw [Subgroup.index_eq_card]
  simp_rw [Nat.card_eq_fintype_card]
  have hequiv : (image (fun x => x * w * x⁻¹) univ) ≃ (G ⧸ Subgroup.centralizer {w}) := by
    -- Define the function from G to the conjugacy class
    let f : G → ↥(image (fun x => x * w * x⁻¹) univ) := fun g => ⟨g * w * g⁻¹, Finset.mem_image_of_mem _ (Finset.mem_univ g)⟩
    -- Show that f respects the quotient relation
    have hf : ∀ g1 g2 : G, g1⁻¹ * g2 ∈ Subgroup.centralizer {w} → f g1 = f g2 := by
      intro g1 g2 hg2
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff] at hg2
      simp [f]
      have hg2w : (g1⁻¹ * g2) * w = w * (g1⁻¹ * g2) := (hg2 w rfl).symm
      have : g1 * w * g1⁻¹ = g2 * w * g2⁻¹ := by
        calc g1 * w * g1⁻¹ = g1 * w * g1⁻¹ * (g1⁻¹ * g2) * (g1⁻¹ * g2)⁻¹ := by group
          _ = g1 * (w * (g1⁻¹ * g2)) * (g1⁻¹ * g2)⁻¹ * g1⁻¹ := by group
          _ = g1 * ((g1⁻¹ * g2) * w) * (g1⁻¹ * g2)⁻¹ * g1⁻¹ := by rw [hg2w]
          _ = g2 * w * g2⁻¹ := by group
      simp [this]
    -- Lift f to a map from the quotient using Quotient.lift
    let g : G ⧸ Subgroup.centralizer {w} → ↥(image (fun x => x * w * x⁻¹) univ) :=
      Quotient.lift f (fun g1 g2 hg => by
        have : g1⁻¹ * g2 ∈ Subgroup.centralizer {w} := by
          exact QuotientGroup.leftRel_apply.mp hg
        exact hf g1 g2 this)
    have hg_inj : Function.Injective g := by
      intro q1 q2 heq
      obtain ⟨g1, rfl⟩ := Quotient.exists_rep q1
      obtain ⟨g2, rfl⟩ := Quotient.exists_rep q2
      -- heq : g ⟦g1⟧ = g ⟦g2⟧ where g = Quotient.lift f hf
      have heq' : g1 * w * g1⁻¹ = g2 * w * g2⁻¹ := by
        exact congrArg Subtype.val heq
      have hmem : g1⁻¹ * g2 ∈ Subgroup.centralizer {w} := by
        have hg2w : (g1⁻¹ * g2) * w = w * (g1⁻¹ * g2) := by
          calc (g1⁻¹ * g2) * w = g1⁻¹ * (g2 * w) := by group
            _ = g1⁻¹ * (g2 * w * g2⁻¹ * g2) := by group
            _ = g1⁻¹ * (g1 * w * g1⁻¹ * g2) := by rw [heq']
            _ = w * (g1⁻¹ * g2) := by group
        simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
        intro h hh
        rw [hh]
        exact hg2w.symm
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hmem)
    have hg_surj : Function.Surjective g := by
      intro ⟨x, hx⟩
      obtain ⟨g0, hg0⟩ := Finset.mem_image.mp hx
      refine ⟨Quotient.mk'' g0, ?_⟩
      change (Quotient.lift f _ (Quotient.mk'' g0)) = ⟨x, hx⟩
      rw [Quotient.lift_mk]
      exact Subtype.ext hg0.2
    exact (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm
  rw [← Fintype.card_coe]
  exact Fintype.card_congr hequiv

/-- Grouping a conjugation invariant sum into conjugacy classes. -/
lemma dvd_sum_of_conj_invariant [Fintype G] {d : ℕ} (f : G → ℕ)
    (hf : ∀ g w : G, f (g * w * g⁻¹) = f w)
    (A : Finset G) (hA : ∀ g w : G, w ∈ A → g * w * g⁻¹ ∈ A)
    (h : ∀ w ∈ A, d ∣ (Subgroup.centralizer ({w} : Set G)).index * f w) :
    d ∣ ∑ w ∈ A, f w := by
  -- Define the equivalence relation of conjugacy
  let e : Setoid G := {
    r := fun x y => IsConj x y
    iseqv := {
      refl := fun x => IsConj.refl x
      symm := fun h => h.symm
      trans := fun h1 h2 => h1.trans h2
    }
  }
  -- A is closed under conjugacy, so it's a union of full conjugacy classes
  have hA_conj : ∀ w ∈ A, ∀ x : G, e.r w x → x ∈ A := by
    intro w hw x hx
    obtain ⟨g, hg⟩ := hx
    have : x = (g : G) * w * (g : G)⁻¹ := by
      rw [SemiconjBy] at hg
      calc x = x * (g : G) * (g : G)⁻¹ := by group
        _ = (g : G) * w * (g : G)⁻¹ := by rw [hg]
    rw [this]
    exact hA g w hw
  -- Map A to the quotient
  let A' : Finset (Quotient e) := A.image Quotient.mk''
  -- The sum over A equals sum over A' of (sum over fiber)
  have hsum : ∑ w ∈ A, f w = ∑ q ∈ A', ∑ w ∈ A.filter (fun x => Quotient.mk'' x = q), f w := by
    have hdisj : ∀ q₁ ∈ A', ∀ q₂ ∈ A', q₁ ≠ q₂ → Disjoint (A.filter (fun x => Quotient.mk'' x = q₁))
        (A.filter (fun x => Quotient.mk'' x = q₂)) := by
      intro q₁ hq₁ q₂ hq₂ heq
      simp only [Finset.disjoint_filter]
      intro x _ h1 h2
      rw [← h1, ← h2] at heq
      exact (heq rfl).elim
    calc ∑ w ∈ A, f w
        = ∑ w ∈ A'.biUnion (fun q => A.filter (fun x => Quotient.mk'' x = q)), f w := by
          congr 1
          ext x
          simp only [Finset.mem_biUnion]
          constructor
          · intro hx
            refine ⟨Quotient.mk'' x, ?_, ?_⟩
            · simp [A', Finset.mem_image]
              exact ⟨x, hx, rfl⟩
            · simp [Finset.mem_filter]
              exact hx
          · rintro ⟨q, hq, hq'⟩
            simp [A', Finset.mem_image] at hq
            obtain ⟨a, ha, rfl⟩ := hq
            simp [Finset.mem_filter] at hq'
            simp [hq'] at *
      _ = ∑ q ∈ A', ∑ w ∈ A.filter (fun x => Quotient.mk'' x = q), f w := by
          rw [Finset.sum_biUnion hdisj]
  -- For each conjugacy class, the sum is |class| * f(w) for any w in the class
  -- and |class| = index of centralizer, so d divides each term
  rw [hsum]
  apply Finset.dvd_sum
  intro q hq
  simp [A'] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  -- The filter is the conjugacy class of w
  have hfilter_eq : A.filter (fun x : G => (Quotient.mk'' x : Quotient e) = Quotient.mk'' w) =
      (univ.filter (fun x : G => IsConj w x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rw [Quotient.eq] at hx
      obtain ⟨g, hg⟩ := hx.2
      exact IsConj.symm ⟨g, hg⟩
    · intro hconj
      obtain ⟨u, hu⟩ := hconj
      have heq : (Quotient.mk'' w : Quotient e) = Quotient.mk'' x := Quotient.sound ⟨u, hu⟩
      exact ⟨hA_conj w hw x ⟨u, hu⟩, heq.symm⟩
  -- Rewrite the sum using hfilter_eq
  have hsum' : ∑ x ∈ univ.filter (fun x : G => IsConj w x), f x = ↑(univ.filter (fun x : G => IsConj w x)).card * f w := by
    have hconst : ∀ y ∈ univ.filter (fun x : G => IsConj w x), f y = f w := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨u, hu⟩ := hy
      have heq : y = (u : G) * w * (u⁻¹ : G) := by
        have hu' : (u : G) * w = y * (u : G) := hu
        have : y * (u : G) * (u : G)⁻¹ = (u : G) * w * (u : G)⁻¹ := by rw [hu']
        simp at this
        rw [this]
      rw [heq]
      rw [hf (u : G) w]
    rw [Finset.sum_eq_card_nsmul hconst]
    rfl
  rw [hfilter_eq, hsum']
  have hcard : (univ.filter (fun x : G => IsConj w x)).card = (Subgroup.centralizer ({w} : Set G)).index := by
    exact card_conj_class w
  rw [hcard]
  exact h w hw

/-- If the `p`-part of `|H|` divides `c`, then the `p`-part of `|G|` divides `H.index * c`. -/
lemma pPart_dvd_index_mul [Finite G] {H : Subgroup G} {p c : ℕ}
    (hc : p ^ ((Nat.card H).factorization p) ∣ c) :
    p ^ ((Nat.card G).factorization p) ∣ H.index * c := by
  have card_eq : Nat.card G = H.index * Nat.card H := by
    rw [Subgroup.index_mul_card]
  rw [card_eq]
  have h1 : (H.index * Nat.card H).factorization p =
      (H.index).factorization p + (Nat.card H).factorization p := by
    rw [Nat.factorization_mul]
    · simp
    · rw [Subgroup.index_eq_card]
      exact Nat.ne_of_gt (Nat.card_pos)
    · exact Nat.ne_of_gt (Nat.card_pos)
  rw [h1]
  rw [pow_add]
  refine Nat.mul_dvd_mul ?_ hc
  exact Nat.ordProj_dvd H.index p

/-- The central solutions of `x ^ m = 1` are the solutions inside the center. -/
lemma card_center_sol [Fintype G] (m : ℕ) :
    (univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G)).card
      = sol ↥(Subgroup.center G) m := by
  unfold sol
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype]
  have equiv : {w : G | w ^ m = 1 ∧ w ∈ Subgroup.center G} ≃ {x : Subgroup.center G | x ^ m = 1} :=
    {
      toFun := fun ⟨w, hw⟩ => ⟨⟨w, hw.2⟩, Subtype.ext hw.1⟩
      invFun := fun ⟨x, hx⟩ => ⟨x.1, ⟨by rw [← Subgroup.coe_pow]; rw [hx]; simp, x.2⟩⟩
      left_inv := fun ⟨w, hw⟩ => by simp
      right_inv := fun ⟨x, hx⟩ => by simp
    }
  convert Fintype.card_congr equiv using 2 <;> simp [Fintype.card_subtype]

/-- Every element satisfies `x ^ |G| = 1`. -/
lemma sol_card_eq [Fintype G] : sol G (Nat.card G) = Nat.card G := by
  rw [sol_eq_card_filter, Nat.card_eq_fintype_card]
  simp only [pow_card_eq_one]
  simp

/-- The contribution of the central elements to the primary decomposition identity. -/
lemma sum_central_eq [Fintype G] (m n : ℕ) :
    ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G),
      sol ↥(Subgroup.centralizer ({w} : Set G)) n
      = sol ↥(Subgroup.center G) m * sol G n := by
  have h_sol_centralizer_eq : ∀ w : G, w ∈ Subgroup.center G →
      sol ↥(Subgroup.centralizer ({w} : Set G)) n = sol G n := by
    intro w hw
    have : Subgroup.centralizer ({w} : Set G) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_iff]
      exact hw.comm g
    rw [this]
    exact sol_top n
  calc ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G),
        sol ↥(Subgroup.centralizer ({w} : Set G)) n
      = ∑ _w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G), sol G n :=
        Finset.sum_congr rfl fun w hw => h_sol_centralizer_eq w ((Finset.mem_filter.mp hw).2).2
    _ = (univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G)).card * sol G n := by
        simp [Finset.sum_const, smul_eq_mul]
    _ = sol ↥(Subgroup.center G) m * sol G n := by rw [card_center_sol]

/-- The contribution of the non-central elements to the primary decomposition identity is
divisible by the `p`-part of `|G|`. -/
lemma pPart_dvd_noncentral_sum [Fintype G] {p : ℕ} (hp : p.Prime)
    (IH : ∀ (H : Type u) [Group H] [Fintype H], Nat.card H < Nat.card G →
      p ^ ((Nat.card H).factorization p) ∣ sol H (p ^ ((Nat.card H).factorization p)))
    (m : ℕ) :
    p ^ ((Nat.card G).factorization p) ∣
      ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G),
        sol ↥(Subgroup.centralizer ({w} : Set G)) (p ^ ((Nat.card G).factorization p)) := by
  refine dvd_sum_of_conj_invariant _ ?_ _ ?_ ?_
  · -- Show sol in centralizer is conjugation-invariant
    exact fun g w => sol_centralizer_conj g w _
  · -- Show the set is closed under conjugation
    intro g w hw
    simp at hw ⊢
    refine ⟨hw.1, ?_⟩
    intro hw_cen
    apply hw.2
    rw [Subgroup.mem_center_iff] at hw_cen ⊢
    intro h
    have := hw_cen (g * h * g⁻¹)
    simp at this
    simpa [mul_assoc] using this
  · -- Show d divides index * f w for each w
    intro w hw
    simp at hw
    -- The centralizer of a non-central element is a proper subgroup
    have hne : (Subgroup.centralizer {w} : Set G) ≠ Set.univ := by
      intro h.eq_univ
      apply hw.2
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ (Subgroup.centralizer {w} : Set G) := h.eq_univ ▸ Set.mem_univ g
      simp [Subgroup.mem_centralizer_iff] at this
      exact this.symm
    have hcard : Nat.card ↥(Subgroup.centralizer {w}) < Nat.card G := by
      have hproper : (Subgroup.centralizer {w} : Subgroup G) ≠ ⊤ := by
        intro h.eq_top
        apply hne
        rw [h.eq_top, Subgroup.coe_top]
      have hcard_eq : (Nat.card ↥(Subgroup.centralizer {w})) * (Subgroup.centralizer {w}).index = Nat.card G := by
        exact Subgroup.card_mul_index _
      have hidx_pos : 0 < (Subgroup.centralizer {w}).index := by
        by_contra h
        push Not at h
        simp [Nat.le_zero.mp h] at hcard_eq
        exact Nat.ne_of_lt (Fintype.card_pos) hcard_eq
      have hidx_gt_one : 1 < (Subgroup.centralizer {w}).index := by
        by_contra h_le
        push Not at h_le
        have h_eq : (Subgroup.centralizer {w}).index = 1 := by omega
        exact hproper (Subgroup.index_eq_one.mp h_eq)
      have hcard_pos_C : 0 < Nat.card ↥(Subgroup.centralizer {w}) := Nat.card_pos (α := ↥(Subgroup.centralizer {w}))
      have hcard_lt : Nat.card ↥(Subgroup.centralizer {w}) < Nat.card G := by
        have h := hcard_eq
        calc Nat.card ↥(Subgroup.centralizer {w})
            = Nat.card ↥(Subgroup.centralizer {w}) * 1 := by ring
          _ < Nat.card ↥(Subgroup.centralizer {w}) * (Subgroup.centralizer {w}).index := by nlinarith
          _ = Nat.card G := h
      exact hcard_lt
    -- Apply IH to centralizer
    haveI : Nonempty ↥(Subgroup.centralizer {w}) := ⟨⟨w, by simp [Subgroup.mem_centralizer_iff]⟩⟩
    have hiht := IH ↥(Subgroup.centralizer {w}) hcard
    -- Since centralizer ≤ G, (Nat.card centralizer).factorization p ≤ (Nat.card G).factorization p
    have hv_le : (Nat.card ↥(Subgroup.centralizer {w})).factorization p
                ≤ (Nat.card G).factorization p := by
      have hdvd : Nat.card ↥(Subgroup.centralizer {w}) ∣ Nat.card G := by
        have := Subgroup.card_mul_index (Subgroup.centralizer {w})
        exact ⟨_, this.symm⟩
      obtain ⟨k, hk⟩ := hdvd
      have hk_ne : k ≠ 0 := Nat.ne_of_gt (by nlinarith : 0 < k)
      rw [hk, Nat.factorization_mul (by simp : Nat.card ↥(Subgroup.centralizer {w}) ≠ 0) hk_ne]
      exact Nat.le_add_right _ _
    -- sol centralizer (p ^ v_G) ≡ sol centralizer (p ^ v_C) [MOD p ^ v_C]
    have hmodEq : sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card G).factorization p)
                  ≡ sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p)
                    [MOD p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p] :=
      sol_modEq_le hp hv_le
    -- Therefore p ^ v_C divides sol centralizer (p ^ v_G)
    have hdvd_sol : p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p
                    ∣ sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card G).factorization p) := by
      have hiht' : sol ↥(Subgroup.centralizer {w}) (p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p) ≡ 0 [MOD p ^ (Nat.card ↥(Subgroup.centralizer {w})).factorization p] := Nat.modEq_zero_iff_dvd.mpr hiht
      exact Nat.modEq_zero_iff_dvd.mp (hmodEq.trans hiht')
    -- Use pPart_dvd_index_mul
    exact pPart_dvd_index_mul hdvd_sol

set_option maxHeartbeats 1000000 in
/-- The induction step for Theorem P. -/
lemma pPart_step [Fintype G] {p : ℕ} (hp : p.Prime)
    (IH : ∀ (H : Type u) [Group H] [Fintype H], Nat.card H < Nat.card G →
      p ^ ((Nat.card H).factorization p) ∣ sol H (p ^ ((Nat.card H).factorization p))) :
    p ^ ((Nat.card G).factorization p) ∣ sol G (p ^ ((Nat.card G).factorization p)) := by
  -- Write |G| = p^v * m where p ∤ m
  set v := (Nat.card G).factorization p with hv_def
  obtain ⟨m, hm⟩ : ∃ m, Nat.card G = p ^ v * m ∧ ¬ p ∣ m := by
    use Nat.card G / p ^ v
    have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
    constructor
    · rw [Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)]
    · intro hdvd
      have h1 : p ^ v ∣ Nat.card G := Nat.ordProj_dvd _ _
      have : p ^ (v + 1) ∣ Nat.card G := by
        rw [pow_succ]
        convert Nat.mul_dvd_mul_left (p ^ v) hdvd using 1
        exact (Nat.mul_div_cancel' h1).symm
      have hcontra : ¬ p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G :=
        Nat.pow_succ_factorization_not_dvd hne hp
      exact hcontra this
  have hv_pos : 0 < p ^ v := pow_pos hp.pos _
  have hm_pos : 0 < m := by nlinarith [Nat.card_pos (α := G)]
  -- sol G |G| = |G|
  have hcard : sol G (Nat.card G) = Nat.card G := sol_card_eq
  -- sol G (p^v * m) = ∑_{w^m=1} sol(centralizer w, p^v)
  have hdec := @sol_mul_eq_sum G _ _ p v m hp hm.2
  -- Split sum into central and non-central
  have hcard_eq : Nat.card G = p ^ v * m := hm.1
  -- sol G (p^v * m) = |G| = p^v * m
  have hsol_eq : sol G (p ^ v * m) = p ^ v * m := by
    calc sol G (p ^ v * m) = sol G (Nat.card G) := by rw [hcard_eq]
      _ = Nat.card G := hcard
      _ = p ^ v * m := hcard_eq
  -- Split the filter into central and non-central
  have hsplit : (univ.filter (fun w : G => w ^ m = 1)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) =
      (univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) +
      (univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) := by
    rw [← Finset.sum_union]
    · congr 1
      ext w
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · exact Finset.disjoint_filter.mpr (fun x _ h1 h2 => h2.2 h1.2)
  -- Non-central sum is divisible by p^v by IH
  have hnoncen : p ^ v ∣ ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G),
      sol ↥(Subgroup.centralizer {w}) (p ^ v) := pPart_dvd_noncentral_sum hp IH m
  -- Central sum equals |center solutions| * sol G (p^v)
  have hcent : ∑ w ∈ univ.filter (fun w : G => w ^ m = 1 ∧ w ∈ Subgroup.center G),
      sol ↥(Subgroup.centralizer {w}) (p ^ v) = sol ↥(Subgroup.center G) m * sol G (p ^ v) :=
    sum_central_eq m (p ^ v)
  -- So sol G (p^v * m) = c * sol G (p^v) + (multiple of p^v)
  have hmain : p ^ v * m = sol ↥(Subgroup.center G) m * sol G (p ^ v) +
      (univ.filter (fun w : G => w ^ m = 1 ∧ w ∉ Subgroup.center G)).sum
      (fun w => sol ↥(Subgroup.centralizer {w}) (p ^ v)) := by
    rw [← hsol_eq, hdec, hsplit, hcent]
  -- p^v divides the RHS sum, so p^v | sol(center G, m) * sol G (p^v)
  have hdiv : p ^ v ∣ sol ↥(Subgroup.center G) m * sol G (p ^ v) := by
    have : p ^ v ∣ p ^ v * m := dvd_mul_right _ _
    rw [hmain] at this
    exact Nat.dvd_add_left hnoncen |>.mp this
  -- sol(center G, m) is coprime to p (since center G is abelian and p ∤ m)
  have hcenter_not_dvd : ¬ p ∣ sol ↥(Subgroup.center G) m :=
    not_dvd_sol_of_comm (fun x y => Subtype.ext (Subgroup.mem_center_iff.mp x.2 y.1).symm) hp hm.2
  -- Therefore p^v and sol(center G, m) are coprime
  have hcoprime : Nat.Coprime (p ^ v) (sol ↥(Subgroup.center G) m) := by
    rcases Nat.eq_zero_or_pos v with hv_zero | hv_pos'
    · simp [hv_zero]
    · rw [Nat.coprime_pow_left_iff hv_pos']
      exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr hcenter_not_dvd
  -- Conclude p^v | sol G (p^v)
  exact hcoprime.dvd_of_dvd_mul_left hdiv

/-- **Theorem P.**  The number of `p`-elements of a finite group is divisible by the order of a
Sylow `p`-subgroup.  Proof by induction on `|G|`: writing `|G| = p ^ v * m` with `p ∤ m`, the
primary decomposition identity gives `|G| = ∑_{w ^ m = 1} sol (centralizer w) (p ^ v)`.  The terms
with `w` non-central are divisible by `p ^ v` (by induction, after grouping into conjugacy
classes), and the central terms contribute `c * sol G (p ^ v)` where `c`, the number of central
`p'`-elements, is prime to `p`. -/
theorem pPart_dvd_sol_pPart {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∀ (H : Type u) [Group H] [Fintype H], Nat.card H = N →
      p ^ ((Nat.card H).factorization p) ∣ sol H (p ^ ((Nat.card H).factorization p)) := by
  have key : ∀ (n : ℕ), (∀ (H : Type u) [Group H] [Fintype H], Nat.card H = n →
      p ^ ((Nat.card H).factorization p) ∣ sol H (p ^ ((Nat.card H).factorization p))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H _ _ hcard_eq_n
      apply pPart_step hp
      intro H' _ _ hcard_eq_H'
      exact ih (Nat.card H') (by linarith) H' rfl
  exact key N

/-- Frobenius's theorem for prime powers. -/
theorem sol_prime_pow_dvd [Fintype G] {p a : ℕ} (hp : p.Prime) :
    p ^ (min a ((Nat.card G).factorization p)) ∣ sol G (p ^ a) := by
  have hcard_pos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [sol_eq_gcd (p ^ a), gcd_prime_pow hp a (Nat.card G) hcard_pos]
  by_cases hab : a ≤ (Nat.card G).factorization p
  · have h1 : p ^ (Nat.card G).factorization p ∣ sol G (p ^ (Nat.card G).factorization p) :=
      pPart_dvd_sol_pPart hp (Nat.card G) G rfl
    have h2 : sol G (p ^ (Nat.card G).factorization p) ≡ sol G (p ^ a) [MOD p ^ a] :=
      sol_modEq_le hp hab
    rw [min_eq_left hab]
    exact (Nat.modEq_zero_iff_dvd.1
      (((Nat.modEq_zero_iff_dvd.2 ((pow_dvd_pow p hab).trans h1)).symm.trans h2).symm))
  · rw [min_eq_right (Nat.le_of_not_le hab)]
    exact pPart_dvd_sol_pPart hp (Nat.card G) G rfl

/-- A version of `pPart_dvd_index_mul` with a truncated exponent. -/
lemma pPart_min_dvd_index_mul [Finite G] {H : Subgroup G} {p α c : ℕ}
    (hc : p ^ (min α ((Nat.card H).factorization p)) ∣ c) :
    p ^ (min α ((Nat.card G).factorization p)) ∣ H.index * c := by
  have card_eq : Nat.card G = H.index * Nat.card H := (Subgroup.index_mul_card H).symm
  have hidx : H.index ≠ 0 := by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card G).factorization p
      = (H.index).factorization p + (Nat.card H).factorization p := by
    rw [card_eq, Nat.factorization_mul hidx hH]; simp
  have hle : min α ((Nat.card G).factorization p)
      ≤ (H.index).factorization p + min α ((Nat.card H).factorization p) := by
    rw [hfact]; omega
  calc p ^ (min α ((Nat.card G).factorization p))
      ∣ p ^ ((H.index).factorization p + min α ((Nat.card H).factorization p)) :=
        pow_dvd_pow p hle
    _ = p ^ ((H.index).factorization p) * p ^ (min α ((Nat.card H).factorization p)) := pow_add _ _ _
    _ ∣ H.index * c := Nat.mul_dvd_mul (Nat.ordProj_dvd _ _) hc

/-- Frobenius's theorem, one prime at a time. -/
lemma prime_pow_dvd_sol [Fintype G] {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ (min (n.factorization p) ((Nat.card G).factorization p)) ∣ sol G n := by
  set α := n.factorization p with hα
  set u := n / p ^ α with hu_def
  have hn_eq : n = p ^ α * u := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hu : ¬ p ∣ u := Nat.not_dvd_ordCompl hp hn
  rw [hn_eq, sol_mul_eq_sum hp hu]
  refine dvd_sum_of_conj_invariant (d := p ^ (min α ((Nat.card G).factorization p)))
    (fun w => sol ↥(Subgroup.centralizer ({w} : Set G)) (p ^ α))
    (fun g w => sol_centralizer_conj g w (p ^ α))
    (univ.filter (fun w : G => w ^ u = 1)) ?_ ?_
  · intro g w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [conj_pow, hw]
    group
  · intro w _
    refine pPart_min_dvd_index_mul ?_
    exact sol_prime_pow_dvd (G := ↥(Subgroup.centralizer ({w} : Set G))) hp

/-- Frobenius's theorem: `gcd n |G|` divides the number of solutions of `x ^ n = 1`. -/
theorem gcd_dvd_sol [Fintype G] (n : ℕ) : Nat.gcd n (Nat.card G) ∣ sol G n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : sol G 0 = Nat.card G := by
      simp [sol]
    simp [this]
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hg : Nat.gcd n (Nat.card G) ≠ 0 := Nat.gcd_ne_zero_left hn
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  have hk : k ≤ (Nat.gcd n (Nat.card G)).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hg).mp hpk
  have hfg : (Nat.gcd n (Nat.card G)).factorization p
      = min (n.factorization p) ((Nat.card G).factorization p) := by
    rw [Nat.factorization_gcd hn hG]
    simp [Nat.min_def]
  rw [hfg] at hk
  exact dvd_trans (pow_dvd_pow p hk) (prime_pow_dvd_sol hp hn)

/-- Frobenius's theorem: for a finite group G and any n, gcd(n, |G|) divides the number of
    solutions of xⁿ = 1 in G. -/
theorem frobenius_group (G : Type*) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) :
    Nat.gcd n (Fintype.card G) ∣ (Finset.univ.filter (fun g : G => g ^ n = 1)).card := by
  have h := @gcd_dvd_sol G _ _ n
  rw [sol_eq_card_filter] at h
  convert h using 1
  rw [Nat.card_eq_fintype_card]
  congr 1
  ext x
  simp

end Brockian.MsFrobeniusGroup

