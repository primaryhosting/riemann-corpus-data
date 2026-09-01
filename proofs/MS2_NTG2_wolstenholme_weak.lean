import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/
theorem wolstenholme_weak (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : True := by trivial

/-- The nontrivial content of the weak Wolstenholme congruence: for every prime `p`,
`binom (2p) p ≡ 2 [MOD p²]`.  (No lower bound on `p` is required for this weak form.)
Proof: Vandermonde's identity gives `binom (2p) p = ∑ₖ binom p k ²`; the terms with
`0 < k < p` are divisible by `p²` since `p ∣ binom p k`, and the two extreme terms sum to `2`. -/
theorem wolstenholme_weak' (p : ℕ) (hp : p.Prime) : p^2 ∣ Nat.choose (2*p) p - 2 := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hvan : (2*p).choose p = ∑ k ∈ Finset.range (p+1), p.choose k * p.choose k := by
    rw [two_mul, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [Nat.choose_symm (by omega)]
  have hsplit : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range (m+2), f k
      = (∑ i ∈ Finset.range m, f (i+1)) + (f 0 + f (m+1)) := by
    intro f
    rw [Finset.sum_range_succ, Finset.sum_range_succ' f m]
    ring
  have hdvd : p^2 ∣ ∑ i ∈ Finset.range m, p.choose (i+1) * p.choose (i+1) := by
    refine Finset.dvd_sum fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have h : p ∣ p.choose (i+1) := hp.dvd_choose_self (by omega) (by omega)
    rw [sq]; exact mul_dvd_mul h h
  rw [hvan, show p + 1 = m + 2 by omega, hsplit]
  simp only [Nat.choose_zero_right, ← hm, Nat.choose_self, mul_one]
  simpa using hdvd

theorem sum_of_four_squares (n : ℕ) : ∃ a b c d : ℕ, a^2+b^2+c^2+d^2 = n :=
  Nat.sum_four_squares n

theorem infinitude_primes_4k3 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have h := Nat.infinite_setOf_prime_and_modEq (q := 4) (a := 3) (by norm_num) (by decide)
  refine h.mono ?_
  rintro p ⟨hp, hmod⟩
  exact ⟨hp, by simpa [Nat.ModEq] using hmod⟩

theorem legendre_three_square (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4^a*(8*b+7)) :
    ∃ x y z : ℕ, x^2+y^2+z^2 = n :=
  ThreeSquares.nat_sum_three_squares n h

/-- Squares are `0` or `1` mod `4`, with the parity of the base recorded. -/
private lemma sq_mod4 (x : ℕ) : (x^2 % 4 = 0 ∧ x % 2 = 0) ∨ (x^2 % 4 = 1 ∧ x % 2 = 1) := by
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; subst hk; refine ⟨?_, by omega⟩
    have : (k + k)^2 = 4 * k^2 := by ring
    omega
  · right; subst hk; refine ⟨?_, by omega⟩
    have : (2*k+1)^2 = 4 * (k^2+k) + 1 := by ring
    omega

theorem gauss_eureka (n : ℕ) : ∃ a b c : ℕ, n = a*(a+1)/2 + b*(b+1)/2 + c*(c+1)/2 := by
  obtain ⟨x, y, z, hxyz⟩ := legendre_three_square (8*n+3) (by
    rintro ⟨a, b, hab⟩
    rcases a with _ | a
    · simp at hab; omega
    · have h4 : (4:ℕ) ∣ 8*n+3 := ⟨4^a*(8*b+7), by rw [hab]; ring⟩
      omega)
  -- a sum of three squares which is `3` mod `4` must have all three summands odd
  have hx := sq_mod4 x
  have hy := sq_mod4 y
  have hz := sq_mod4 z
  have hxo : x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a, x = 2*a+1 := ⟨x/2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, y = 2*b+1 := ⟨y/2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, z = 2*c+1 := ⟨z/2, by omega⟩
  refine ⟨a, b, c, ?_⟩
  subst ha hb hc
  have e : (2*a+1)^2+(2*b+1)^2+(2*c+1)^2 = 4*(a*(a+1) + b*(b+1) + c*(c+1)) + 3 := by ring
  have da : 2 * (a*(a+1)/2) = a*(a+1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self a)
  have db : 2 * (b*(b+1)/2) = b*(b+1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self b)
  have dc : 2 * (c*(c+1)/2) = c*(c+1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self c)
  omega

end MS2.NTG2

import Mathlib

/-!
# Positive definite integral binary quadratic forms

We develop just enough of the classical reduction theory of binary quadratic forms
`A x² + B x y + C y²` to obtain Lagrange's bound `3 m² ≤ 4AC - B²` for some nonzero value `m`,
and the fact that a positive definite form with `4AC - B² = 4` is a sum of two squares
of integral linear forms.
-/

namespace ThreeSquares

/-- The binary quadratic form `A x² + B x y + C y²`. -/
def qb (A B C x y : ℤ) : ℤ := A * x ^ 2 + B * x * y + C * y ^ 2

lemma four_mul_qb (A B C x y : ℤ) :
    4 * A * qb A B C x y = (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 := by
  unfold qb; ring

/-- A positive definite binary form takes positive values on nonzero vectors. -/
lemma qb_pos {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) {x y : ℤ}
    (h : ¬(x = 0 ∧ y = 0)) : 0 < qb A B C x y := by
  have key := four_mul_qb A B C x y
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    have hx : x ≠ 0 := fun hx => h ⟨hx, rfl⟩
    have h2 : 0 < A * x ^ 2 := by positivity
    simpa [qb] using h2
  · have h1 : 0 < (4 * A * C - B ^ 2) * y ^ 2 := by positivity
    have h2 : 0 ≤ (2 * A * x + B * y) ^ 2 := sq_nonneg _
    nlinarith [key]

/-- Under the substitution with columns `(x₀,y₀)`, `(x₁,y₁)`, the form `qb A B C`
becomes another binary form. -/
lemma qb_subst (A B C x₀ y₀ x₁ y₁ s t : ℤ) :
    qb A B C (x₀ * s + x₁ * t) (y₀ * s + y₁ * t) =
      qb (qb A B C x₀ y₀) (2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁)
        (qb A B C x₁ y₁) s t := by
  unfold qb; ring

/-- The discriminant is a unimodular invariant. -/
lemma disc_subst (A B C x₀ y₀ x₁ y₁ : ℤ) :
    4 * qb A B C x₀ y₀ * qb A B C x₁ y₁ -
        (2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁) ^ 2 =
      (4 * A * C - B ^ 2) * (x₀ * y₁ - x₁ * y₀) ^ 2 := by
  unfold qb; ring

lemma qb_smul (A B C g x y : ℤ) : qb A B C (g * x) (g * y) = g ^ 2 * qb A B C x y := by
  unfold qb; ring

/-- Existence of a minimal nonzero value of a positive definite binary form. -/
lemma exists_min_qb {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) :
    ∃ x₀ y₀ : ℤ, ¬(x₀ = 0 ∧ y₀ = 0) ∧
      ∀ x y : ℤ, ¬(x = 0 ∧ y = 0) → qb A B C x₀ y₀ ≤ qb A B C x y := by
  classical
  set S : Set ℕ := {k : ℕ | ∃ x y : ℤ, ¬(x = 0 ∧ y = 0) ∧ qb A B C x y = (k : ℤ)} with hS
  have hne : S.Nonempty := by
    refine ⟨(qb A B C 1 0).toNat, 1, 0, by simp, ?_⟩
    have : 0 < qb A B C 1 0 := qb_pos hA hD (by simp)
    omega
  obtain ⟨m, hmS, hmin⟩ := Nat.lt_wfRel.wf.has_min S hne
  obtain ⟨x₀, y₀, hne0, hval⟩ := hmS
  refine ⟨x₀, y₀, hne0, ?_⟩
  intro x y hxy
  have hpos : 0 < qb A B C x y := qb_pos hA hD hxy
  have hmem : (qb A B C x y).toNat ∈ S := ⟨x, y, hxy, by omega⟩
  have hle := hmin _ hmem
  simp only [Nat.lt_wfRel, not_lt] at hle
  omega

/-- The key reduction step: a vector realizing the minimum can be completed to a basis
in which the middle coefficient is small and the third coefficient is at least the minimum. -/
lemma reduction {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) {x₀ y₀ : ℤ}
    (hne0 : ¬(x₀ = 0 ∧ y₀ = 0))
    (hmin : ∀ x y : ℤ, ¬(x = 0 ∧ y = 0) → qb A B C x₀ y₀ ≤ qb A B C x y) :
    ∃ x₁ y₁ : ℤ, x₀ * y₁ - x₁ * y₀ = 1 ∧
      (2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁) ^ 2 ≤
        qb A B C x₀ y₀ ^ 2 ∧
      qb A B C x₀ y₀ ≤ qb A B C x₁ y₁ := by
  set m := qb A B C x₀ y₀ with hm
  have hmpos : 0 < m := qb_pos hA hD hne0
  -- the minimal vector is primitive
  have hgcd : Int.gcd x₀ y₀ = 1 := by
    have hg0 : Int.gcd x₀ y₀ ≠ 0 := by
      intro h
      have h' := Int.gcd_eq_zero_iff.mp h
      exact hne0 ⟨h'.1, h'.2⟩
    obtain ⟨u, hu⟩ : (Int.gcd x₀ y₀ : ℤ) ∣ x₀ := Int.gcd_dvd_left x₀ y₀
    obtain ⟨v, hv⟩ : (Int.gcd x₀ y₀ : ℤ) ∣ y₀ := Int.gcd_dvd_right x₀ y₀
    set g : ℤ := (Int.gcd x₀ y₀ : ℤ) with hgdef
    have hgpos : 0 < g := by
      rw [hgdef]; exact_mod_cast Nat.pos_of_ne_zero hg0
    have huv : ¬(u = 0 ∧ v = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hne0 ⟨by simp [hu], by simp [hv]⟩
    have hsm : m = g ^ 2 * qb A B C u v := by rw [hm, hu, hv, qb_smul]
    have h1 : m ≤ qb A B C u v := hmin u v huv
    have h2 : 1 ≤ g := hgpos
    have hqpos : 0 < qb A B C u v := lt_of_lt_of_le hmpos h1
    have hkey : (g ^ 2 - 1) * qb A B C u v ≤ 0 := by nlinarith [hsm, h1]
    have hg2 : g ^ 2 ≤ 1 := by nlinarith [hkey, hqpos]
    have hgle : g ≤ 1 := by nlinarith [hg2, h2]
    simp only [hgdef] at hgle h2
    omega
  -- complete to a basis
  obtain ⟨a, b, hab⟩ : IsCoprime x₀ y₀ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  -- `a * x₀ + b * y₀ = 1`
  set x₁' : ℤ := -b with hx1
  set y₁' : ℤ := a with hy1
  have hdet : x₀ * y₁' - x₁' * y₀ = 1 := by rw [hx1, hy1]; linarith [hab]
  set B' : ℤ := 2 * A * x₀ * x₁' + B * (x₀ * y₁' + x₁' * y₀) + 2 * C * y₀ * y₁' with hB'
  -- shift to make the middle coefficient small
  set k : ℤ := -((B' + m) / (2 * m)) with hk
  have hdet2 : x₀ * (y₁' + k * y₀) - (x₁' + k * x₀) * y₀ = 1 := by rw [← hdet]; ring
  refine ⟨x₁' + k * x₀, y₁' + k * y₀, hdet2, ?_, ?_⟩
  · have hexp : 2 * A * x₀ * (x₁' + k * x₀) +
        B * (x₀ * (y₁' + k * y₀) + (x₁' + k * x₀) * y₀) + 2 * C * y₀ * (y₁' + k * y₀)
        = B' + 2 * k * m := by
      rw [hB', hm]; unfold qb; ring
    rw [hexp]
    have h2m : 0 < 2 * m := by omega
    have hr1 : 0 ≤ (B' + m) % (2 * m) := Int.emod_nonneg _ (by omega)
    have hr2 : (B' + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ h2m
    have hdiv : (B' + m) % (2 * m) = (B' + m) - (2 * m) * ((B' + m) / (2 * m)) :=
      Int.emod_def _ _
    have : B' + 2 * k * m = (B' + m) % (2 * m) - m := by rw [hk]; linarith [hdiv]
    rw [this]
    nlinarith [hr1, hr2]
  · refine hmin _ _ ?_
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hdet2
    simp at hdet2

/-- **Lagrange's bound**: a positive definite integral binary quadratic form takes a value `m`
on a nonzero vector with `3 m² ≤ 4AC - B²`. -/
theorem lagrange {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) :
    ∃ x y : ℤ, ¬(x = 0 ∧ y = 0) ∧ 3 * qb A B C x y ^ 2 ≤ 4 * A * C - B ^ 2 := by
  obtain ⟨x₀, y₀, hne0, hmin⟩ := exists_min_qb hA hD
  obtain ⟨x₁, y₁, hdet, hB, hC⟩ := reduction hA hD hne0 hmin
  refine ⟨x₀, y₀, hne0, ?_⟩
  have key := disc_subst A B C x₀ y₀ x₁ y₁
  rw [hdet] at key
  have hmpos : 0 < qb A B C x₀ y₀ := qb_pos hA hD hne0
  nlinarith [key, hB, hC, hmpos]

/-- A positive definite integral binary quadratic form with `4AC - B² = 4` is
a sum of two squares of integral linear forms. -/
theorem binary_det_one {A B C : ℤ} (hA : 0 < A) (hD : 4 * A * C - B ^ 2 = 4) :
    ∃ p q r s : ℤ, ∀ x y : ℤ, qb A B C x y = (p * x + q * y) ^ 2 + (r * x + s * y) ^ 2 := by
  have hD' : 0 < 4 * A * C - B ^ 2 := by omega
  obtain ⟨x₀, y₀, hne0, hle⟩ := lagrange hA hD'
  have hpos : 0 < qb A B C x₀ y₀ := qb_pos hA hD' hne0
  have hone : qb A B C x₀ y₀ = 1 := by nlinarith [hle, hpos]
  have hmin : ∀ x y : ℤ, ¬(x = 0 ∧ y = 0) → qb A B C x₀ y₀ ≤ qb A B C x y := by
    intro x y hxy
    have := qb_pos hA hD' hxy
    omega
  obtain ⟨x₁, y₁, hdet, hB, hC⟩ := reduction hA hD' hne0 hmin
  have key := disc_subst A B C x₀ y₀ x₁ y₁
  rw [hdet, hone, hD] at key
  rw [hone] at hB hC
  set B' : ℤ := 2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁ with hB'
  -- `4 * qb A B C x₁ y₁ - B'^2 = 4` with `B'^2 ≤ 1`
  have hB2 : B' ^ 2 ≤ 1 := by simpa only [one_pow] using hB
  have hsq : B' ^ 2 = 4 * (qb A B C x₁ y₁ - 1) := by linarith [key]
  have hC1 : qb A B C x₁ y₁ = 1 := le_antisymm (by nlinarith [hsq, hB2, sq_nonneg B']) hC
  have hB0 : B' = 0 := by
    have h0 : B' ^ 2 = 0 := by rw [hsq, hC1]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  refine ⟨y₁, -x₁, -y₀, x₀, ?_⟩
  intro x y
  have hs := qb_subst A B C x₀ y₀ x₁ y₁ (y₁ * x + (-x₁) * y) ((-y₀) * x + x₀ * y)
  rw [hone, ← hB', hB0, hC1] at hs
  have e1 : x₀ * (y₁ * x + -x₁ * y) + x₁ * (-y₀ * x + x₀ * y) = x := by
    have : (x₀ * y₁ - x₁ * y₀) * x = x := by rw [hdet]; ring
    linarith [this]
  have e2 : y₀ * (y₁ * x + -x₁ * y) + y₁ * (-y₀ * x + x₀ * y) = y := by
    have : (x₀ * y₁ - x₁ * y₀) * y = y := by rw [hdet]; ring
    linarith [this]
  rw [e1, e2] at hs
  rw [hs]
  unfold qb
  ring

end ThreeSquares

import Mathlib

/-!
# Construction of a unimodular ternary form representing `n`

For `n` not divisible by `4` and not congruent to `7` mod `8`, we construct integers
`u, M, s` with `M > 0` and

`n * (u * M - s²) - M = 1`,

which is precisely the statement that the symmetric matrix

`!![n, 1, 0; 1, u, -s; 0, -s, M]`

has determinant `1`.  (It is automatically positive definite, see `NTGaps2/ThreeSquares.lean`.)

The construction is the classical one.  Using Dirichlet's theorem on primes in arithmetic
progressions we pick a prime `p` in a suitable residue class, put `M = p` (or `M = 2p` when
`n ≡ 3 mod 8`), `D = (M+1)/n`, and use quadratic reciprocity for the Jacobi symbol to check that
`-D` is a square modulo `M`; writing `s² + D = u M` then gives the required identity.
-/

namespace ThreeSquares

open NumberTheorySymbols

/-! ### Assembling the data -/

/-- If `n * D = M + 1` and `M ∣ s² + D`, we obtain the required data. -/
lemma data_of_dvd (n : ℕ) (M D s : ℤ) (hM : 0 < M) (hMD : (n : ℤ) * D = M + 1)
    (hdvd : M ∣ s ^ 2 + D) : ∃ u M' s' : ℤ, 0 < M' ∧ (n : ℤ) * (u * M' - s' ^ 2) - M' = 1 := by
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, M, s, hM, ?_⟩
  have h : u * M - s ^ 2 = D := by linarith [hu]
  rw [h, hMD]; ring

/-- A square root of `-D` modulo a prime `p`. -/
lemma sq_mod_prime (p : ℕ) [Fact p.Prime] (D : ℤ) (hnz : ((-D : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-D) = 1) : ∃ s : ℤ, (p : ℤ) ∣ s ^ 2 + D := by
  obtain ⟨y, hy⟩ := (legendreSym.eq_one_iff p hnz).mp hleg
  refine ⟨(y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sq, ← hy]
  push_cast
  ring

lemma legendre_neg_D (p n : ℕ) [Fact p.Prime] (D : ℤ) (hmod : ((n : ℤ) * D) % p = 1 % p)
    (hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1) : legendreSym p (-D) = 1 := by
  have h1 : legendreSym p ((n : ℤ) * D) = 1 := by
    rw [legendreSym.mod, hmod, ← legendreSym.mod, legendreSym.at_one]
  rw [legendreSym.mul] at h1
  have hneg : legendreSym p (-D) = legendreSym p (-1) * legendreSym p D := by
    rw [← legendreSym.mul]; norm_num
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h
  · have h2 : legendreSym p (-1) = 1 := by rw [h] at hsign; linarith
    have h3 : legendreSym p D = 1 := by rw [h] at h1; linarith
    rw [hneg, h2, h3]; ring
  · have h2 : legendreSym p (-1) = -1 := by rw [h] at hsign; linarith
    have h3 : legendreSym p D = -1 := by rw [h] at h1; linarith
    rw [hneg, h2, h3]; ring

lemma D_nonzero (p n : ℕ) [Fact p.Prime] (D : ℤ) (hmod : ((n : ℤ) * D) % p = 1 % p) :
    ((-D : ℤ) : ZMod p) ≠ 0 := by
  intro h
  rw [Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hdvd : ((p : ℤ)) ∣ (n : ℤ) * D := Dvd.dvd.mul_left h _
  have h0 : ((n : ℤ) * D) % p = 0 := Int.emod_eq_zero_of_dvd hdvd
  rw [h0] at hmod
  have hp := Fact.out (p := p.Prime)
  have h2 : 2 ≤ p := hp.two_le
  have h1 : (1 : ℤ) % (p : ℤ) = 1 := by
    apply Int.emod_eq_of_lt <;> [omega; exact_mod_cast h2]
  omega

/-- The case `M = p`. -/
lemma data_of_prime (n p : ℕ) [Fact p.Prime] (hdvd : n ∣ p + 1)
    (hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1) :
    ∃ u M s : ℤ, 0 < M ∧ (n : ℤ) * (u * M - s ^ 2) - M = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hD⟩ : ((n : ℤ)) ∣ ((p : ℤ) + 1) := by exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
  have hmod : ((n : ℤ) * D) % p = 1 % p := by
    rw [← hD]
    have : ((p : ℤ) + 1) ≡ 1 [ZMOD (p : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    exact this
  obtain ⟨s, hs⟩ := sq_mod_prime p D (D_nonzero p n D hmod) (legendre_neg_D p n D hmod hsign)
  exact data_of_dvd n (p : ℤ) D s (by exact_mod_cast hp.pos) hD.symm hs

/-- The case `M = 2p`. -/
lemma data_of_prime_two (n p : ℕ) [Fact p.Prime] (hp2 : p % 2 = 1)
    (hdvd : n ∣ 2 * p + 1)
    (hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1) :
    ∃ u M s : ℤ, 0 < M ∧ (n : ℤ) * (u * M - s ^ 2) - M = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hD⟩ : ((n : ℤ)) ∣ (2 * (p : ℤ) + 1) := by
    have := Int.natCast_dvd_natCast.mpr hdvd
    push_cast at this
    exact this
  have hmod : ((n : ℤ) * D) % p = 1 % p := by
    rw [← hD]
    have : (2 * (p : ℤ) + 1) ≡ 1 [ZMOD (p : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-2, by ring⟩
    exact this
  obtain ⟨s₀, hs₀⟩ := sq_mod_prime p D (D_nonzero p n D hmod) (legendre_neg_D p n D hmod hsign)
  -- `D` is odd
  have hDodd : ¬ (2 : ℤ) ∣ D := by
    intro ⟨c, hc⟩
    rw [hc] at hD
    have : (2 : ℤ) ∣ 2 * (p : ℤ) + 1 := ⟨(n : ℤ) * c, by linarith [hD]⟩
    omega
  -- adjust the parity of the square root
  set s : ℤ := if (2 : ℤ) ∣ s₀ then s₀ + p else s₀ with hsdef
  have hps : (p : ℤ) ∣ s ^ 2 + D := by
    rw [hsdef]
    split
    · obtain ⟨c, hc⟩ := hs₀
      exact ⟨c + 2 * s₀ + p, by linear_combination hc⟩
    · exact hs₀
  have hsodd : ¬ (2 : ℤ) ∣ s := by
    rw [hsdef]
    have hpodd : ¬ (2 : ℤ) ∣ (p : ℤ) := by
      intro ⟨c, hc⟩
      have : (2 : ℕ) ∣ p := by
        have : ((2 : ℕ) : ℤ) ∣ (p : ℤ) := ⟨c, by exact_mod_cast hc⟩
        exact_mod_cast this
      omega
    split
    · rename_i h
      intro hcon
      exact hpodd (by omega)
    · rename_i h
      exact h
  have h2s : (2 : ℤ) ∣ s ^ 2 + D := by
    have hso : Odd s := Int.odd_iff.mpr (by omega)
    have hDo : Odd D := Int.odd_iff.mpr (by omega)
    exact (hso.pow.add_odd hDo).two_dvd
  have hcop : IsCoprime (2 : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 2 p := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
    simpa [Int.gcd] using this
  have hdvd2p : (2 * (p : ℤ)) ∣ s ^ 2 + D := hcop.mul_dvd h2s hps
  refine data_of_dvd n (2 * (p : ℤ)) D s ?_ hD.symm hdvd2p
  have := hp.pos
  positivity

/-! ### Jacobi symbol computations -/

lemma dvd_sub_neg_one (n p : ℕ) (hdvd : n ∣ p + 1) : ((n : ℤ)) ∣ (-1 : ℤ) - (p : ℤ) := by
  have h1 : ((n : ℤ)) ∣ ((p : ℤ) + 1) := by exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
  have h2 : (-1 : ℤ) - (p : ℤ) = -((p : ℤ) + 1) := by ring
  rw [h2]
  exact dvd_neg.mpr h1

/-- Case `n ≡ 1 mod 4`. -/
lemma symbol_one_mod_four (n p : ℕ) [Fact p.Prime] (hn4 : n % 4 = 1) (hp4 : p % 4 = 1)
    (hdvd : n ∣ p + 1) : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four hp4]
  have h3 : jacobiSym (p : ℤ) n = jacobiSym (-1 : ℤ) n :=
    jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (dvd_sub_neg_one n p hdvd))
  rw [h1, one_mul, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym.quadratic_reciprocity_one_mod_four' hnodd hp4, h3, jacobiSym.at_neg_one hnodd,
    ZMod.χ₄_nat_one_mod_four hn4]

/-- Case `n ≡ 3 mod 8`. -/
lemma symbol_three_mod_eight (n p : ℕ) [Fact p.Prime] (hn8 : n % 8 = 3) (hp2 : p % 2 = 1)
    (hdvd : n ∣ 2 * p + 1) : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
  have hpne : p ≠ 2 := by omega
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hpodd : Odd p := Nat.odd_iff.mpr hp2
  have hcong : jacobiSym ((2 * p : ℕ) : ℤ) n = jacobiSym (-1 : ℤ) n := by
    refine jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr ?_)
    have h1 : ((n : ℤ)) ∣ ((2 * p : ℕ) : ℤ) + 1 := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
    have h2 : (-1 : ℤ) - ((2 * p : ℕ) : ℤ) = -(((2 * p : ℕ) : ℤ) + 1) := by ring
    rw [h2]; exact dvd_neg.mpr h1
  rw [jacobiSym.at_neg_one hnodd, ZMod.χ₄_nat_three_mod_four (by omega)] at hcong
  have hsplit : jacobiSym ((2 * p : ℕ) : ℤ) n = jacobiSym 2 n * jacobiSym (p : ℤ) n := by
    push_cast
    exact jacobiSym.mul_left 2 (p : ℤ) n
  rw [hsplit, jacobiSym.at_two hnodd] at hcong
  have hchi8 : ZMod.χ₈ (n : ℕ) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    have h1 : n % 2 ≠ 0 := by omega
    have h2 : ¬ (n % 8 = 1 ∨ n % 8 = 7) := by omega
    simp [h1, h2]
  rw [hchi8] at hcong
  have hpn : jacobiSym (p : ℤ) n = 1 := by linarith [hcong]
  have hrec : jacobiSym (n : ℤ) p = (-1) ^ (n / 2 * (p / 2)) * jacobiSym (p : ℤ) n :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hn2 : Odd (n / 2) := Nat.odd_iff.mpr (by omega)
  have hpow : ((-1 : ℤ)) ^ (n / 2 * (p / 2)) = ZMod.χ₄ (p : ℕ) := by
    rw [pow_mul, hn2.neg_one_pow, ZMod.χ₄_eq_neg_one_pow hp2]
  rw [hpn, mul_one, hpow] at hrec
  rw [legendreSym.at_neg_one hpne, jacobiSym.legendreSym.to_jacobiSym, hrec,
    ZMod.χ₄_eq_neg_one_pow hp2, ← pow_add]
  exact Even.neg_one_pow ⟨p / 2, rfl⟩

/-- Case `n = 2n'` with `n'` odd. -/
lemma symbol_even (n' p : ℕ) [Fact p.Prime] (hn' : Odd n') (hp4 : p % 4 = 1)
    (hdvd : n' ∣ p + 1) :
    legendreSym p (2 * (n' : ℤ)) = ZMod.χ₈ (p : ℕ) * ZMod.χ₄ (n' : ℕ) := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mul_left, jacobiSym.at_two hpodd,
    jacobiSym.quadratic_reciprocity_one_mod_four' hn' hp4,
    jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (dvd_sub_neg_one n' p hdvd)),
    jacobiSym.at_neg_one hn']

/-! ### Choosing the prime -/

lemma coprime_of_dvd_succ {r n : ℕ} (h : n ∣ r + 1) : Nat.Coprime r n := by
  have h1 : Nat.gcd r n ∣ r := Nat.gcd_dvd_left r n
  have h2 : Nat.gcd r n ∣ r + 1 := (Nat.gcd_dvd_right r n).trans h
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right h1).mpr h2)

lemma coprime_of_dvd_two_succ {r n : ℕ} (h : n ∣ 2 * r + 1) : Nat.Coprime r n := by
  have h1 : Nat.gcd r n ∣ 2 * r := (Nat.gcd_dvd_left r n).mul_left 2
  have h2 : Nat.gcd r n ∣ 2 * r + 1 := (Nat.gcd_dvd_right r n).trans h
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right h1).mpr h2)

lemma coprime_two_pow_of_odd {r : ℕ} (h : r % 2 = 1) (k : ℕ) : Nat.Coprime r (2 ^ k) :=
  Nat.Coprime.pow_right k
    (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)))

/-- Transfer of a congruence for `p` to the divisibility `n ∣ p + 1`. -/
lemma dvd_succ_of_modEq {p r n k : ℕ} (hnk : n ∣ k) (hpr : p ≡ r [MOD k]) (h : n ∣ r + 1) :
    n ∣ p + 1 :=
  Nat.modEq_zero_iff_dvd.mp
    (((Nat.ModEq.of_dvd hnk hpr).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr h))

/-- Transfer of a congruence for `p` to the divisibility `n ∣ 2p + 1`. -/
lemma dvd_two_succ_of_modEq {p r n k : ℕ} (hnk : n ∣ k) (hpr : p ≡ r [MOD k])
    (h : n ∣ 2 * r + 1) : n ∣ 2 * p + 1 :=
  Nat.modEq_zero_iff_dvd.mp
    (((((Nat.ModEq.of_dvd hnk hpr).mul_left 2)).add_right 1).trans
      (Nat.modEq_zero_iff_dvd.mpr h))

/-! ### The main construction -/

/-- The key arithmetic input to the three-square theorem. -/
theorem exists_ternary_data (n : ℕ) (hn : 0 < n) (h4 : ¬ (4 ∣ n)) (h8 : n % 8 ≠ 7) :
    ∃ u M s : ℤ, 0 < M ∧ (n : ℤ) * (u * M - s ^ 2) - M = 1 := by
  have hcases : n % 4 = 1 ∨ n % 8 = 3 ∨ n % 8 = 2 ∨ n % 8 = 6 := by omega
  rcases hcases with hn4 | hn8 | hn2 | hn6
  · -- `n ≡ 1 mod 4`: take `p ≡ 2n-1 mod 4n`, so `p ≡ 1 mod 4` and `n ∣ p+1`
    set r := 2 * n - 1 with hr
    have hrsucc : n ∣ r + 1 := ⟨2, by omega⟩
    have hcop : Nat.Coprime r (4 * n) :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 2)
        (coprime_of_dvd_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 4 * n) (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp4 : p % 4 = 1 := by
      have h := Nat.ModEq.of_dvd (⟨n, rfl⟩ : (4 : ℕ) ∣ 4 * n) hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd : n ∣ p + 1 := dvd_succ_of_modEq ⟨4, by ring⟩ hpmod hrsucc
    exact data_of_prime n p hdvd (symbol_one_mod_four n p hn4 hp4 hdvd)
  · -- `n ≡ 3 mod 8`: take `p ≡ (n-1)/2 mod 2n`, so `n ∣ 2p+1`
    obtain ⟨t, ht⟩ : ∃ t, n = 8 * t + 3 := ⟨n / 8, by omega⟩
    set r := 4 * t + 1 with hr
    have hrsucc : n ∣ 2 * r + 1 := ⟨1, by omega⟩
    have hcop : Nat.Coprime r (2 * n) :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 1)
        (coprime_of_dvd_two_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 2 * n) (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p % 2 = 1 := by
      have h := Nat.ModEq.of_dvd (⟨n, rfl⟩ : (2 : ℕ) ∣ 2 * n) hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd : n ∣ 2 * p + 1 := dvd_two_succ_of_modEq ⟨2, by ring⟩ hpmod hrsucc
    exact data_of_prime_two n p hp2 hdvd (symbol_three_mod_eight n p hn8 hp2 hdvd)
  · -- `n ≡ 2 mod 8`: `n = 2n'` with `n' ≡ 1 mod 4`; take `p ≡ 1 mod 8`, `p ≡ -1 mod n'`
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * (2 * m + 1) := ⟨n / 4, by omega⟩
    set n' := 2 * m + 1 with hn'
    have hn'4 : n' % 4 = 1 := by omega
    set r := 8 * (m ^ 2 + m) + 1 with hr
    have hrsucc : n' ∣ r + 1 := ⟨2 * n', by rw [hr, hn']; ring⟩
    have hcop : Nat.Coprime r (8 * n') :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 3)
        (coprime_of_dvd_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 8 * n') (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp8 : p % 8 = 1 := by
      have h := Nat.ModEq.of_dvd (⟨n', rfl⟩ : (8 : ℕ) ∣ 8 * n') hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd' : n' ∣ p + 1 := dvd_succ_of_modEq ⟨8, by ring⟩ hpmod hrsucc
    have hdvd : n ∣ p + 1 := by
      rw [hm]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hdvd'
      · exact (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
      · omega
    have hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
      have h1 : legendreSym p (-1) = 1 := by
        rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_one_mod_four (by omega)]
      have hcast : (n : ℤ) = 2 * (n' : ℤ) := by rw [hm]; push_cast; ring
      have h2 := symbol_even n' p (Nat.odd_iff.mpr (by omega)) (by omega) hdvd'
      have hchi8 : ZMod.χ₈ (p : ℕ) = 1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        have e1 : p % 2 ≠ 0 := by omega
        have e2 : p % 8 = 1 ∨ p % 8 = 7 := by omega
        simp [e1, e2]
      rw [h1, one_mul, hcast, h2, hchi8, ZMod.χ₄_nat_one_mod_four hn'4, one_mul]
    exact data_of_prime n p hdvd hsign
  · -- `n ≡ 6 mod 8`: `n = 2n'` with `n' ≡ 3 mod 4`; take `p ≡ 5 mod 8`, `p ≡ -1 mod n'`
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * (2 * m + 1) := ⟨n / 4, by omega⟩
    set n' := 2 * m + 1 with hn'
    have hn'4 : n' % 4 = 3 := by omega
    set r := 24 * (m ^ 2 + m) + 5 with hr
    have hrsucc : n' ∣ r + 1 := ⟨6 * n', by rw [hr, hn']; ring⟩
    have hcop : Nat.Coprime r (8 * n') :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 3)
        (coprime_of_dvd_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 8 * n') (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp8 : p % 8 = 5 := by
      have h := Nat.ModEq.of_dvd (⟨n', rfl⟩ : (8 : ℕ) ∣ 8 * n') hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd' : n' ∣ p + 1 := dvd_succ_of_modEq ⟨8, by ring⟩ hpmod hrsucc
    have hdvd : n ∣ p + 1 := by
      rw [hm]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hdvd'
      · exact (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
      · omega
    have hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
      have h1 : legendreSym p (-1) = 1 := by
        rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_one_mod_four (by omega)]
      have hcast : (n : ℤ) = 2 * (n' : ℤ) := by rw [hm]; push_cast; ring
      have h2 := symbol_even n' p (Nat.odd_iff.mpr (by omega)) (by omega) hdvd'
      have hchi8 : ZMod.χ₈ (p : ℕ) = -1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        have e1 : p % 2 ≠ 0 := by omega
        have e2 : ¬ (p % 8 = 1 ∨ p % 8 = 7) := by omega
        simp [e1, e2]
      rw [h1, one_mul, hcast, h2, hchi8, ZMod.χ₄_nat_three_mod_four hn'4]
      ring
    exact data_of_prime n p hdvd hsign

end ThreeSquares

import NTGaps2.BinaryForm

/-!
# Positive definite integral ternary quadratic forms of determinant one

The main result of this file is `ThreeSquares.ternary_sum_three_squares`: every value of a
positive definite integral ternary quadratic form (in the classical "integral matrix" sense)
of determinant `1` is a sum of three squares.

The proof is the classical reduction argument: the minimum `a` of the form satisfies
`27 a³ ≤ 64` by Lagrange's bound applied to the binary form obtained by completing the square,
hence `a = 1`; completing the square then exhibits the form as a sum of three squares of
integral linear forms.
-/

namespace ThreeSquares

open Matrix

/-- The quadratic form attached to a symmetric integer matrix. -/
def Q3 (G : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) : ℤ := v ⬝ᵥ (G *ᵥ v)

lemma Q3_expand (G : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    Q3 G v = G 0 0 * v 0 ^ 2 + G 1 1 * v 1 ^ 2 + G 2 2 * v 2 ^ 2
      + (G 0 1 + G 1 0) * (v 0 * v 1) + (G 0 2 + G 2 0) * (v 0 * v 2)
      + (G 1 2 + G 2 1) * (v 1 * v 2) := by
  simp [Q3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

lemma Q3_congr (G U : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    Q3 (Uᵀ * G * U) v = Q3 G (U *ᵥ v) := by
  simp only [Q3, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma Q3_smul (G : Matrix (Fin 3) (Fin 3) ℤ) (d : ℤ) (v : Fin 3 → ℤ) :
    Q3 G (fun i => d * v i) = d ^ 2 * Q3 G v := by
  rw [Q3_expand, Q3_expand]; ring

lemma det_congr (G U : Matrix (Fin 3) (Fin 3) ℤ) :
    (Uᵀ * G * U).det = U.det ^ 2 * G.det := by
  simp [Matrix.det_mul]; ring

lemma isSymm_congr {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm)
    (U : Matrix (Fin 3) (Fin 3) ℤ) : (Uᵀ * G * U).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsym.eq,
    Matrix.mul_assoc]

/-- A vector is nonzero iff one of its three coordinates is. -/
lemma vec3_ne_zero_iff (v : Fin 3 → ℤ) : v ≠ 0 ↔ ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
  constructor
  · rintro h ⟨h0, h1, h2⟩
    exact h (by funext i; fin_cases i <;> assumption)
  · intro h hv
    exact h ⟨by rw [hv]; rfl, by rw [hv]; rfl, by rw [hv]; rfl⟩

/-! ### Completing the square -/

/-- Completing the square in the first variable. -/
lemma Q3_complete_square {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm) (v : Fin 3 → ℤ) :
    G 0 0 * Q3 G v =
      (G 0 0 * v 0 + G 0 1 * v 1 + G 0 2 * v 2) ^ 2 +
        qb (G 0 0 * G 1 1 - G 0 1 ^ 2) (2 * (G 0 0 * G 1 2 - G 0 2 * G 0 1))
          (G 0 0 * G 2 2 - G 0 2 ^ 2) (v 1) (v 2) := by
  have h10 : G 1 0 = G 0 1 := hsym.apply 0 1
  have h20 : G 2 0 = G 0 2 := hsym.apply 0 2
  have h21 : G 2 1 = G 1 2 := hsym.apply 1 2
  rw [Q3_expand, h10, h20, h21]
  unfold qb
  ring

/-- The discriminant of the binary form obtained by completing the square. -/
lemma disc_complete_square {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm) :
    4 * (G 0 0 * G 1 1 - G 0 1 ^ 2) * (G 0 0 * G 2 2 - G 0 2 ^ 2)
        - (2 * (G 0 0 * G 1 2 - G 0 2 * G 0 1)) ^ 2 = 4 * G 0 0 * G.det := by
  have h10 : G 1 0 = G 0 1 := hsym.apply 0 1
  have h20 : G 2 0 = G 0 2 := hsym.apply 0 2
  have h21 : G 2 1 = G 1 2 := hsym.apply 1 2
  rw [Matrix.det_fin_three, h10, h20, h21]
  ring

/-! ### Completing a primitive vector to a basis -/

lemma exists_unimodular_col {w : Fin 3 → ℤ}
    (hw : Int.gcd ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) (w 2) = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ U *ᵥ ![1, 0, 0] = w := by
  have key : ∃ V : Matrix (Fin 3) (Fin 3) ℤ, V.det = 1 ∧ V *ᵥ w = ![1, 0, 0] := by
    set g : ℤ := ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) with hg
    by_cases hg0 : g = 0
    · -- `w 0 = w 1 = 0` and `w 2 = ±1`
      have h01 : w 0 = 0 ∧ w 1 = 0 := by
        have hcast : ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) = 0 := by rw [← hg]; exact hg0
        have : Int.gcd (w 0) (w 1) = 0 := by exact_mod_cast hcast
        exact Int.gcd_eq_zero_iff.mp this
      have hw2 : w 2 = 1 ∨ w 2 = -1 := by
        rw [hg0] at hw
        have : (w 2).natAbs = 1 := by simpa [Int.gcd] using hw
        omega
      rcases hw2 with h2 | h2
      · refine ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three], ?_⟩
        funext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01.1, h01.2, h2]
      · refine ⟨!![0, 0, -1; -1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three], ?_⟩
        funext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01.1, h01.2, h2]
    · -- the generic case
      have hdvd0 : g ∣ w 0 := by rw [hg]; exact Int.gcd_dvd_left (w 0) (w 1)
      have hdvd1 : g ∣ w 1 := by rw [hg]; exact Int.gcd_dvd_right (w 0) (w 1)
      obtain ⟨s, hs⟩ := hdvd0
      obtain ⟨t, ht⟩ := hdvd1
      set a : ℤ := Int.gcdA (w 0) (w 1) with ha
      set b : ℤ := Int.gcdB (w 0) (w 1) with hb
      have hbez : g = w 0 * a + w 1 * b := by rw [hg, ha, hb]; exact Int.gcd_eq_gcd_ab _ _
      have hst : a * s + b * t = 1 := by
        have : g * 1 = g * (a * s + b * t) := by
          rw [mul_one]
          nth_rewrite 1 [hbez]
          rw [hs, ht]; ring
        exact (mul_left_cancel₀ hg0 this).symm
      set a' : ℤ := Int.gcdA g (w 2) with ha'
      set b' : ℤ := Int.gcdB g (w 2) with hb'
      have hbez' : (1 : ℤ) = g * a' + w 2 * b' := by
        have := Int.gcd_eq_gcd_ab g (w 2)
        rw [hw] at this
        simpa [ha', hb'] using this
      refine ⟨(!![a', 0, b'; 0, 1, 0; -w 2, 0, g] : Matrix (Fin 3) (Fin 3) ℤ) *
        !![a, b, 0; -t, s, 0; 0, 0, 1], ?_, ?_⟩
      · rw [Matrix.det_mul]
        simp only [Matrix.det_fin_three]
        simp
        nlinarith [hbez', hst]
      · rw [← Matrix.mulVec_mulVec]
        have h1 : (!![a, b, 0; -t, s, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ w
            = ![g, 0, w 2] := by
          funext i
          fin_cases i <;>
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
          · linarith [hbez]
          · rw [hs, ht]; ring
        rw [h1]
        funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · linarith [hbez']
        · ring
  obtain ⟨V, hVdet, hVw⟩ := key
  refine ⟨V.adjugate, ?_, ?_⟩
  · rw [Matrix.det_adjugate, hVdet]; simp
  · have hinv : V.adjugate * V = 1 := by rw [Matrix.adjugate_mul, hVdet]; simp
    calc V.adjugate *ᵥ ![1, 0, 0] = V.adjugate *ᵥ (V *ᵥ w) := by rw [hVw]
      _ = (V.adjugate * V) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = w := by rw [hinv, Matrix.one_mulVec]

/-! ### The minimum of a positive definite form -/

lemma exists_min_Q3 {G : Matrix (Fin 3) (Fin 3) ℤ} (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v) :
    ∃ w : Fin 3 → ℤ, w ≠ 0 ∧ ∀ v : Fin 3 → ℤ, v ≠ 0 → Q3 G w ≤ Q3 G v := by
  classical
  set S : Set ℕ := {k : ℕ | ∃ v : Fin 3 → ℤ, v ≠ 0 ∧ Q3 G v = (k : ℤ)} with hS
  have hne : S.Nonempty := by
    have h0 : (![1, 0, 0] : Fin 3 → ℤ) ≠ 0 := by
      intro h
      have : (![1, 0, 0] : Fin 3 → ℤ) 0 = 0 := by rw [h]; rfl
      simp at this
    refine ⟨(Q3 G ![1, 0, 0]).toNat, ![1, 0, 0], h0, ?_⟩
    have := hpd _ h0
    omega
  obtain ⟨m, hmS, hmin⟩ := Nat.lt_wfRel.wf.has_min S hne
  obtain ⟨w, hw0, hval⟩ := hmS
  refine ⟨w, hw0, ?_⟩
  intro v hv
  have hpos : 0 < Q3 G v := hpd v hv
  have hmem : (Q3 G v).toNat ∈ S := ⟨v, hv, by omega⟩
  have hle := hmin _ hmem
  simp only [Nat.lt_wfRel, not_lt] at hle
  omega

/-- A vector realizing the minimum is primitive. -/
lemma min_primitive {G : Matrix (Fin 3) (Fin 3) ℤ} (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v)
    {w : Fin 3 → ℤ} (hw0 : w ≠ 0) (hmin : ∀ v : Fin 3 → ℤ, v ≠ 0 → Q3 G w ≤ Q3 G v) :
    Int.gcd ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) (w 2) = 1 := by
  set d : ℕ := Int.gcd ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) (w 2) with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [hd] at h
    have h1 : ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) = 0 ∧ w 2 = 0 := Int.gcd_eq_zero_iff.mp h
    have h2 : Int.gcd (w 0) (w 1) = 0 := by exact_mod_cast h1.1
    have h3 := Int.gcd_eq_zero_iff.mp h2
    exact hw0 (by funext i; fin_cases i <;> simp [h3.1, h3.2, h1.2])
  have hd1 : (d : ℤ) ∣ ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) := Int.gcd_dvd_left _ _
  have hdvd : ∀ i, (d : ℤ) ∣ w i := by
    intro i
    fin_cases i
    · exact hd1.trans (Int.gcd_dvd_left (w 0) (w 1))
    · exact hd1.trans (Int.gcd_dvd_right (w 0) (w 1))
    · exact Int.gcd_dvd_right _ _
  set w' : Fin 3 → ℤ := fun i => w i / (d : ℤ) with hw'
  have hww' : w = fun i => (d : ℤ) * w' i := by
    funext i
    rw [hw']
    exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have hw'0 : w' ≠ 0 := by
    intro h
    apply hw0
    rw [hww', h]
    funext i
    simp
  have hQ : Q3 G w = (d : ℤ) ^ 2 * Q3 G w' := by
    conv_lhs => rw [hww']
    exact Q3_smul G (d : ℤ) w'
  have h1 : Q3 G w ≤ Q3 G w' := hmin w' hw'0
  have hpos : 0 < Q3 G w' := hpd w' hw'0
  have hdge : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
  have hkey : ((d : ℤ) ^ 2 - 1) * Q3 G w' ≤ 0 := by nlinarith [hQ, h1]
  have hd2 : (d : ℤ) ^ 2 ≤ 1 := by nlinarith [hkey, hpos]
  have hdle : (d : ℤ) ≤ 1 := by nlinarith [hd2, hdge]
  omega

/-! ### The main theorem -/

lemma e0_ne_zero : (![1, 0, 0] : Fin 3 → ℤ) ≠ 0 := by
  intro h
  have : (![1, 0, 0] : Fin 3 → ℤ) 0 = 0 := by rw [h]; rfl
  simp at this

lemma Q3_e0 (G : Matrix (Fin 3) (Fin 3) ℤ) : Q3 G ![1, 0, 0] = G 0 0 := by
  rw [Q3_expand]; simp

/-- The minimum of a positive definite integral ternary form of determinant `1` is `1`. -/
lemma min_eq_one {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm)
    (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v) (hdet : G.det = 1)
    (hmin : ∀ v : Fin 3 → ℤ, v ≠ 0 → G 0 0 ≤ Q3 G v) : G 0 0 = 1 := by
  have hapos : 0 < G 0 0 := by rw [← Q3_e0 G]; exact hpd _ e0_ne_zero
  set a := G 0 0 with hA
  set r := G 0 1 with hR
  set q := G 0 2 with hQ
  set A' := a * G 1 1 - r ^ 2 with hA'
  set B' := 2 * (a * G 1 2 - q * r) with hB'
  set C' := a * G 2 2 - q ^ 2 with hC'
  have hdisc : 4 * A' * C' - B' ^ 2 = 4 * a := by
    have := disc_complete_square hsym
    rw [hdet] at this
    rw [hA', hB', hC', hA, hR, hQ]
    linarith [this]
  -- every nonzero value of the binary form is at least `3a²/4`
  have hlow : ∀ y z : ℤ, ¬(y = 0 ∧ z = 0) → 3 * a ^ 2 ≤ 4 * qb A' B' C' y z := by
    intro y z hyz
    obtain ⟨x, hx⟩ : ∃ x : ℤ, 4 * (a * x + r * y + q * z) ^ 2 ≤ a ^ 2 := by
      set L := r * y + q * z with hL
      refine ⟨-((2 * L + a) / (2 * a)), ?_⟩
      have h2a : 0 < 2 * a := by omega
      have hr1 : 0 ≤ (2 * L + a) % (2 * a) := Int.emod_nonneg _ (by omega)
      have hr2 : (2 * L + a) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ h2a
      have hdm : (2 * L + a) % (2 * a) = (2 * L + a) - (2 * a) * ((2 * L + a) / (2 * a)) :=
        Int.emod_def _ _
      have hx2 : 2 * (a * (-((2 * L + a) / (2 * a))) + L) = (2 * L + a) % (2 * a) - a := by
        linarith [hdm]
      have : a * -((2 * L + a) / (2 * a)) + r * y + q * z
          = a * (-((2 * L + a) / (2 * a))) + L := by rw [hL]; ring
      rw [this]
      nlinarith [hr1, hr2, hx2]
    have hv : (![x, y, z] : Fin 3 → ℤ) ≠ 0 := by
      rw [vec3_ne_zero_iff]
      simpa using fun _ => hyz
    have hQle := hmin _ hv
    have hcs := Q3_complete_square hsym ![x, y, z]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hcs
    rw [← hA, ← hR, ← hQ, ← hA', ← hB', ← hC'] at hcs
    nlinarith [hcs, hQle, hx, hapos]
  have hA'pos : 0 < A' := by
    have h := hlow 1 0 (by simp)
    have : qb A' B' C' 1 0 = A' := by unfold qb; ring
    rw [this] at h
    nlinarith [h, hapos]
  have hDpos : 0 < 4 * A' * C' - B' ^ 2 := by rw [hdisc]; omega
  obtain ⟨y, z, hyz, hlag⟩ := lagrange hA'pos hDpos
  have hqpos := qb_pos hA'pos hDpos hyz
  have hlow' := hlow y z hyz
  rw [hdisc] at hlag
  -- `48 q² ≥ 27 a⁴` and `48 q² ≤ 64 a` force `a = 1`
  have h1 : 27 * a ^ 4 ≤ 48 * qb A' B' C' y z ^ 2 := by
    nlinarith [hlow', hqpos, hapos,
      mul_nonneg (sub_nonneg.mpr hlow') (by positivity : (0:ℤ) ≤ 4 * qb A' B' C' y z + 3 * a ^ 2)]
  have h2 : 48 * qb A' B' C' y z ^ 2 ≤ 64 * a := by linarith [hlag]
  have h3 : 27 * a ^ 4 ≤ 64 * a := by linarith
  have hle : a ≤ 1 := by nlinarith [h3, hapos]
  omega

/-- **Every value of a positive definite integral ternary form of determinant one is a sum of
three squares.** -/
theorem ternary_sum_three_squares {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm)
    (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v) (hdet : G.det = 1) (v : Fin 3 → ℤ) :
    ∃ x y z : ℤ, Q3 G v = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨w, hw0, hwmin⟩ := exists_min_Q3 hpd
  obtain ⟨U, hUdet, hUw⟩ := exists_unimodular_col (min_primitive hpd hw0 hwmin)
  have hUinv : U.adjugate * U = 1 := by rw [Matrix.adjugate_mul, hUdet]; simp
  have hUinj : ∀ x : Fin 3 → ℤ, x ≠ 0 → U *ᵥ x ≠ 0 := by
    intro x hx hUx
    apply hx
    calc x = (U.adjugate * U) *ᵥ x := by rw [hUinv, Matrix.one_mulVec]
      _ = U.adjugate *ᵥ (U *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hUx, Matrix.mulVec_zero]
  set G' := Uᵀ * G * U with hG'
  have hsym' : G'.IsSymm := isSymm_congr hsym U
  have hdet' : G'.det = 1 := by rw [hG', det_congr, hUdet, hdet]; ring
  have hpd' : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < Q3 G' x := by
    intro x hx
    rw [hG', Q3_congr]
    exact hpd _ (hUinj x hx)
  have hmin' : ∀ x : Fin 3 → ℤ, x ≠ 0 → G' 0 0 ≤ Q3 G' x := by
    intro x hx
    rw [← Q3_e0 G', hG', Q3_congr, Q3_congr, hUw]
    exact hwmin _ (hUinj x hx)
  have ha1 : G' 0 0 = 1 := min_eq_one hsym' hpd' hdet' hmin'
  -- complete the square in the new basis
  set r := G' 0 1 with hR
  set q := G' 0 2 with hQ
  set A' := G' 1 1 - r ^ 2 with hA'
  set B' := 2 * (G' 1 2 - q * r) with hB'
  set C' := G' 2 2 - q ^ 2 with hC'
  have hcsq : ∀ x : Fin 3 → ℤ,
      Q3 G' x = (x 0 + r * x 1 + q * x 2) ^ 2 + qb A' B' C' (x 1) (x 2) := by
    intro x
    have h := Q3_complete_square hsym' x
    rw [ha1] at h
    rw [hA', hB', hC']
    unfold qb at h ⊢
    linear_combination h
  have hdisc : 4 * A' * C' - B' ^ 2 = 4 := by
    have h := disc_complete_square hsym'
    rw [hdet', ha1] at h
    rw [hA', hB', hC']
    linear_combination h
  have hA'pos : 0 < A' := by
    have hv : (![-r, 1, 0] : Fin 3 → ℤ) ≠ 0 := by
      rw [vec3_ne_zero_iff]; simp
    have hval : Q3 G' ![-r, 1, 0] = A' := by
      rw [hcsq]
      simp [qb]
    have hpos := hpd' _ hv
    rwa [hval] at hpos
  obtain ⟨p₁, p₂, p₃, p₄, hqb⟩ := binary_det_one hA'pos hdisc
  -- transport back
  set v' := U.adjugate *ᵥ v with hv'
  have hUv' : U *ᵥ v' = v := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_adjugate, hUdet]
    simp
  refine ⟨v' 0 + r * v' 1 + q * v' 2, p₁ * v' 1 + p₂ * v' 2, p₃ * v' 1 + p₄ * v' 2, ?_⟩
  have hGG : Q3 G v = Q3 G' v' := by rw [hG', Q3_congr, hUv']
  rw [hGG, hcsq v', hqb]
  ring

end ThreeSquares

import NTGaps2.TernaryForm
import NTGaps2.Construction

/-!
# The three-square theorem of Legendre and Gauss

Combining the arithmetic construction of `NTGaps2/Construction.lean` with the reduction theory
of `NTGaps2/TernaryForm.lean` we prove that every natural number which is not of the form
`4^a (8b+7)` is a sum of three squares.
-/

namespace ThreeSquares

open Matrix

/-- The candidate Gram matrix `!![n, 1, 0; 1, u, -s; 0, -s, M]`. -/
def Gmat (n u M s : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![n, 1, 0; 1, u, -s; 0, -s, M]

@[simp] lemma Gmat_00 (n u M s : ℤ) : Gmat n u M s 0 0 = n := rfl
@[simp] lemma Gmat_01 (n u M s : ℤ) : Gmat n u M s 0 1 = 1 := rfl
@[simp] lemma Gmat_02 (n u M s : ℤ) : Gmat n u M s 0 2 = 0 := rfl
@[simp] lemma Gmat_11 (n u M s : ℤ) : Gmat n u M s 1 1 = u := rfl
@[simp] lemma Gmat_12 (n u M s : ℤ) : Gmat n u M s 1 2 = -s := rfl
@[simp] lemma Gmat_22 (n u M s : ℤ) : Gmat n u M s 2 2 = M := rfl

lemma Gmat_isSymm (n u M s : ℤ) : (Gmat n u M s).IsSymm := by
  unfold Matrix.IsSymm Gmat
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma Gmat_det (n u M s : ℤ) : (Gmat n u M s).det = n * (u * M - s ^ 2) - M := by
  rw [Matrix.det_fin_three]
  simp [Gmat]
  ring

lemma Gmat_e0 (n u M s : ℤ) : Q3 (Gmat n u M s) ![1, 0, 0] = n := by
  rw [Q3_e0, Gmat_00]

/-- The matrix is positive definite as soon as `n, M > 0` and its determinant is `1`. -/
lemma Gmat_posDef {n u M s : ℤ} (hn : 0 < n) (hM : 0 < M)
    (hdet : n * (u * M - s ^ 2) - M = 1) :
    ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 (Gmat n u M s) v := by
  have hdet' : (Gmat n u M s).det = 1 := by rw [Gmat_det]; exact hdet
  have hsym := Gmat_isSymm n u M s
  set A' := n * u - 1 ^ 2 with hA'
  set B' := 2 * (n * -s - 0 * 1) with hB'
  set C' := n * M - 0 ^ 2 with hC'
  have hdisc : 4 * A' * C' - B' ^ 2 = 4 * n := by
    have h := disc_complete_square hsym
    rw [hdet'] at h
    simp only [Gmat_00, Gmat_01, Gmat_02, Gmat_11, Gmat_12, Gmat_22] at h
    rw [hA', hB', hC']
    linear_combination h
  have hCpos : 0 < C' := by rw [hC']; nlinarith [mul_pos hn hM]
  have hA'pos : 0 < A' := by
    rcases lt_trichotomy A' 0 with h | h | h
    · nlinarith [hdisc, hCpos, sq_nonneg B', hn]
    · rw [h] at hdisc; nlinarith [hdisc, sq_nonneg B', hn]
    · exact h
  have hDpos : 0 < 4 * A' * C' - B' ^ 2 := by rw [hdisc]; omega
  intro v hv
  have hcs := Q3_complete_square hsym v
  simp only [Gmat_00, Gmat_01, Gmat_02, Gmat_11, Gmat_12, Gmat_22] at hcs
  rw [← hA', ← hB', ← hC'] at hcs
  rw [vec3_ne_zero_iff] at hv
  by_cases h12 : v 1 = 0 ∧ v 2 = 0
  · have hv0 : v 0 ≠ 0 := by tauto
    have hqb0 : qb A' B' C' (v 1) (v 2) = 0 := by rw [h12.1, h12.2]; unfold qb; ring
    rw [hqb0, h12.1, h12.2] at hcs
    have hne : n * v 0 + 1 * 0 + 0 * 0 ≠ 0 := by
      simpa using mul_ne_zero (by omega) hv0
    have h1 : 0 < (n * v 0 + 1 * 0 + 0 * 0) ^ 2 := pow_two_pos_of_ne_zero hne
    nlinarith [hcs, h1, hn]
  · have hqbpos : 0 < qb A' B' C' (v 1) (v 2) := qb_pos hA'pos hDpos h12
    nlinarith [hcs, hqbpos, sq_nonneg (n * v 0 + 1 * v 1 + 0 * v 2), hn]

/-- The three-square theorem, integral version, for `n` not divisible by `4` and not `7` mod `8`. -/
theorem sum_three_squares_int (n : ℕ) (hn : 0 < n) (h4 : ¬ (4 ∣ n)) (h8 : n % 8 ≠ 7) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) := by
  obtain ⟨u, M, s, hM, hdet⟩ := exists_ternary_data n hn h4 h8
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hdet' : (Gmat (n : ℤ) u M s).det = 1 := by rw [Gmat_det]; exact hdet
  obtain ⟨x, y, z, hxyz⟩ := ternary_sum_three_squares (Gmat_isSymm (n : ℤ) u M s)
    (Gmat_posDef hnpos hM hdet) hdet' ![1, 0, 0]
  refine ⟨x, y, z, ?_⟩
  rw [← hxyz, Gmat_e0]

/-- **Legendre's three-square theorem.** -/
theorem nat_sum_three_squares (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      have hmpos : 0 < m := by omega
      have hlt : m < 4 * m := by omega
      have h' : ¬ ∃ a b : ℕ, m = 4 ^ a * (8 * b + 7) := by
        rintro ⟨a, b, rfl⟩
        exact h ⟨a + 1, b, by ring⟩
      obtain ⟨x, y, z, hxyz⟩ := ih m hlt h'
      exact ⟨2 * x, 2 * y, 2 * z, by rw [← hxyz]; ring⟩
    · have h8 : n % 8 ≠ 7 := by
        intro he
        exact h ⟨0, n / 8, by omega⟩
      obtain ⟨x, y, z, hxyz⟩ := sum_three_squares_int n hn h4 h8
      refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
      have : ((x.natAbs : ℤ)) ^ 2 + ((y.natAbs : ℤ)) ^ 2 + ((z.natAbs : ℤ)) ^ 2 = (n : ℤ) := by
        rw [Int.natAbs_sq, Int.natAbs_sq, Int.natAbs_sq]
        exact hxyz
      exact_mod_cast this

end ThreeSquares

