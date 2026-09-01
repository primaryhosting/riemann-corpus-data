import Mathlib
namespace Brockian.MsFrobeniusGeneral

/-- Two-generator case: if `p` and `q` are coprime and `p > 0`, every `n ≥ p * q`
    is a nonnegative combination of `p` and `q`. -/
lemma two_gen_rep (p q n : ℕ) (hp : 0 < p) (hcop : Nat.Coprime p q) (hn : p * q ≤ n) :
    ∃ x y : ℕ, p * x + q * y = n := by
  by_cases hq : 0 < q
  · -- Both p and q are positive
    -- Use extended GCD to find a particular solution in integers
    have hgcd : (p : ℤ) * Int.gcdA p q + (q : ℤ) * Int.gcdB p q = 1 := by
      have hg : Int.gcd (p : ℤ) q = 1 := by simp [Int.gcd_natCast_natCast] at *; exact hcop
      linarith [Int.gcd_eq_gcd_ab p q]
    -- Get particular solution: p * (n * gcdA) + q * (n * gcdB) = n
    let x₀ := n * Int.gcdA p q
    let y₀ := n * Int.gcdB p q
    have hparticular : (p : ℤ) * x₀ + (q : ℤ) * y₀ = n := by
      calc (p : ℤ) * x₀ + (q : ℤ) * y₀ = (p : ℤ) * (n * Int.gcdA p q) + (q : ℤ) * (n * Int.gcdB p q) := rfl
        _ = n * ((p : ℤ) * Int.gcdA p q + (q : ℤ) * Int.gcdB p q) := by ring
        _ = n * 1 := by rw [hgcd]
        _ = n := by ring
    -- General solution: (x₀ + t*q, y₀ - t*p) for any integer t
    -- We need to find t such that x₀ + t*q ≥ 0 and y₀ - t*p ≥ 0
    -- Choose t = -⌊x₀/q⌋ to make x = x₀ + t*q = x₀ % q ∈ [0, q-1]
    let t := -(x₀ / q)
    let x' := x₀ + t * q
    let y' := y₀ - t * p
    have hx' : x' = x₀ % q := by
      show x₀ + (-(x₀ / q)) * q = x₀ % q
      linarith [Int.mul_ediv_add_emod x₀ q]
    -- x' ≥ 0 since x' = x₀ % q and q > 0
    have hx'_nonneg : 0 ≤ x' := by
      rw [hx']
      exact Int.emod_nonneg _ (by positivity)
    -- x' < q
    have hx'_lt_q : x' < q := by
      rw [hx']
      exact Int.emod_lt_of_pos _ (by positivity)
    -- Show p * x' + q * y' = n
    have hsum : (p : ℤ) * x' + (q : ℤ) * y' = n := by
      -- x' = x₀ + t*q, y' = y₀ - t*p
      -- p*x' + q*y' = p*(x₀ + t*q) + q*(y₀ - t*p) = p*x₀ + q*y₀ + p*t*q - q*t*p = p*x₀ + q*y₀ = n
      show (p : ℤ) * x' + (q : ℤ) * y' = n
      simp only [x', y']
      ring_nf
      rw [hparticular]
    -- Show y' ≥ 0: we have p*x' + q*y' = n, x' < q, so p*x' < p*q ≤ n, thus q*y' = n - p*x' > 0
    have hy'_nonneg : 0 ≤ y' := by
      have h1 : (p : ℤ) * x' < p * q := by nlinarith
      have h2 : (p : ℤ) * x' < n := by linarith
      have h3 : (q : ℤ) * y' = n - (p : ℤ) * x' := by linarith
      have h4 : (q : ℤ) * y' > 0 := by linarith
      nlinarith
    -- Convert to natural numbers
    use Int.toNat x', Int.toNat y'
    have hx'_eq : x' = Int.toNat x' := (Int.toNat_of_nonneg hx'_nonneg).symm
    have hy'_eq : y' = Int.toNat y' := (Int.toNat_of_nonneg hy'_nonneg).symm
    have hsum' : (p : ℤ) * (Int.toNat x') + (q : ℤ) * (Int.toNat y') = (n : ℤ) := by
      rw [← hx'_eq, ← hy'_eq]; exact hsum
    exact_mod_cast hsum'
  · -- q = 0, but then gcd(p, 0) = p ≠ 1 unless p = 1
    push_neg at hq
    interval_cases q
    simp at hcop
    -- q = 0 and gcd(p, 0) = 1 means p = 1
    subst hcop; exact ⟨n, 0, by simp⟩

/-- If `c` is coprime to `g > 0`, one can solve `c * z ≡ m [MOD g]` with `z < g`.
    (For `g = 1` take `z = 0`; otherwise take `z = (m * d) % g` where `d` is an inverse of `c`
    modulo `g`, obtained from `Nat.exists_mul_mod_eq_one_of_coprime`.) -/
lemma exists_mod_solution (g c m : ℕ) (hg : 0 < g) (hcop : Nat.Coprime c g) :
    ∃ z : ℕ, z < g ∧ (c * z) % g = m % g := by
  by_cases hg1 : g = 1
  · use 0
    simp [hg1, Nat.mod_one]
  · -- g > 1, use the multiplicative inverse
    have hg1' : 1 < g := Nat.lt_of_le_of_ne hg (Ne.symm hg1)
    obtain ⟨d, hd_lt, hd_eq⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hg1'
    use m * d % g
    refine ⟨Nat.mod_lt _ hg, ?_⟩
    -- (c * (m * d % g)) % g = (c * m * d) % g = (m * (c * d)) % g = (m * 1) % g = m % g
    have h1 : (c * (m * d % g)) % g = (c * (m * d)) % g := by
      have : m * d = m * d % g + g * (m * d / g) := (Nat.mod_add_div (m * d) g).symm
      calc (c * (m * d % g)) % g = (c * (m * d % g) + g * (c * (m * d / g))) % g := by
             rw [Nat.add_mul_mod_self_left]
        _ = (c * ((m * d % g) + g * (m * d / g))) % g := by ring_nf
        _ = (c * (m * d)) % g := by rw [← this]
    rw [h1]
    have h2 : (c * (m * d)) % g = (m * (c * d)) % g := by ring_nf
    rw [h2]
    have h3 : (m * (c * d)) % g = (m * (c * d % g)) % g := by
      conv_lhs => rw [← Nat.mod_add_div (c * d) g]
      rw [Nat.mul_add, mul_left_comm m g]
      simp [Nat.add_mul_mod_self_left]
    rw [h3, hd_eq, Nat.mul_one]

/-- If `c` is coprime to `g > 0`, then any `m ≥ c * g` can be written as `c * z + g * k`
    with `z < g`. -/
lemma exists_small_mul_add (g c m : ℕ) (hg : 0 < g) (hcop : Nat.Coprime c g)
    (hm : c * g ≤ m) : ∃ z k : ℕ, z < g ∧ c * z + g * k = m := by
  obtain ⟨z, hz, hmod⟩ := exists_mod_solution g c m hg hcop
  refine ⟨z, (m - c * z) / g, hz, ?_⟩
  have hc : c * z ≤ m := by nlinarith
  have hdiv : g ∣ (m - c * z) := by
    have h1 : (m : ℤ) % g = (c * z : ℤ) % g := by
      norm_cast
      exact hmod.symm
    have h2 : (g : ℤ) ∣ ((m : ℤ) - (c * z : ℤ)) := Int.modEq_iff_dvd.mp h1.symm
    exact_mod_cast h2
  have heq : g * ((m - c * z) / g) = m - c * z := Nat.mul_div_cancel' hdiv
  omega

/-- The general Frobenius / numerical-semigroup theorem: for positive a,b,c with gcd(a,b,c)=1,
    every sufficiently large integer is a nonnegative combination a·x + b·y + c·z. -/
theorem frobenius_three (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hg : Nat.gcd a (Nat.gcd b c) = 1) :
    ∃ N : ℕ, ∀ m : ℕ, N < m → ∃ x y z : ℕ, a * x + b * y + c * z = m := by
  -- Let g = gcd(b, c)
  let g := Nat.gcd b c
  -- b' = b / g, c' = c / g, so b = g * b', c = g * c', and gcd(b', c') = 1
  let b' := b / g
  let c' := c / g
  -- Key facts about g, b', c'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left c hb
  have hb_eq : b = g * b' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left b c)).symm
  have hc_eq : c = g * c' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right b c)).symm
  have hcop_bc' : Nat.Coprime b' c' := by
    apply Nat.coprime_div_gcd_div_gcd hg_pos
  -- We have gcd(a, g) = 1
  have hcop_ag : Nat.Coprime a g := hg
  -- Set N = g * (b' * c' + a)
  use g * (b' * c' + a)
  intro m hm
  -- First, use exists_small_mul_add to write m = a * z + g * k with z < g
  have hm_bound : a * g ≤ m := by
    nlinarith
  obtain ⟨z, k, hz, hm_eq⟩ := exists_small_mul_add g a m hg_pos hcop_ag hm_bound
  -- Now we need k >= b' * c' to apply two_gen_rep b' c'
  have hk_bound : b' * c' ≤ k := by
    nlinarith
  -- Use two_gen_rep to write k = b' * y + c' * z'
  have hb'_pos : 0 < b' := by
    nlinarith
  have hc'_pos : 0 < c' := by
    nlinarith
  obtain ⟨y, z', hb'c'_eq⟩ := two_gen_rep b' c' k hb'_pos hcop_bc' hk_bound
  -- Now combine: m = a * z + g * k = a * z + g * (b' * y + c' * z') = a * z + b * y + c * z'
  use z, y, z'
  calc a * z + b * y + c * z'
      = a * z + g * b' * y + g * c' * z' := by rw [hb_eq, hc_eq]
    _ = a * z + g * (b' * y + c' * z') := by ring
    _ = a * z + g * k := by rw [hb'c'_eq]
    _ = m := hm_eq

end Brockian.MsFrobeniusGeneral

