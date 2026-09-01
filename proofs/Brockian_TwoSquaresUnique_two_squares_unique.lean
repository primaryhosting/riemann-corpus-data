import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/
private lemma pos_of_prime_sq_add_sq {p a b : ℕ} (hp : p.Prime) (h : p = a ^ 2 + b ^ 2) :
    0 < a := by
  by_contra ha
  push_neg at ha
  interval_cases a
  simp at h
  subst h
  rcases b with _ | _ | b <;> simp_all [Nat.Prime]
  have : (b + 1 + 1) ^ 2 = (b + 1 + 1) * (b + 1 + 1) := by ring
  rw [this] at hp
  rcases hp.isUnit_or_isUnit rfl with h | h <;> simp at h

/-- If `p` is prime and `p = a^2 + b^2`, then `a` and `b` are coprime. -/
private lemma coprime_of_prime_sq_add_sq {p a b : ℕ} (hp : p.Prime) (h : p = a ^ 2 + b ^ 2) :
    Nat.Coprime a b := by
  by_contra hng
  set g := Nat.gcd a b with hgdef
  have ha_pos : 0 < a := pos_of_prime_sq_add_sq hp h
  have hg_pos : 0 < g := Nat.pos_of_ne_zero (fun hz => by
    have := Nat.eq_zero_of_gcd_eq_zero_left (hgdef ▸ hz)
    omega)
  have hg_gt_one : 1 < g :=
    Nat.lt_of_le_of_ne hg_pos (Ne.symm (fun hg1 => hng (by rw [hgdef] at hg1; exact hg1)))
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hg2 : g ^ 2 ∣ p := by
    rw [h]
    exact Nat.dvd_add (pow_dvd_pow_of_dvd hga 2) (pow_dvd_pow_of_dvd hgb 2)
  have hg2_eq : g ^ 2 = p :=
    (hp.eq_one_or_self_of_dvd (g ^ 2) hg2).resolve_left (by nlinarith)
  rw [← hg2_eq] at hp
  have hdvd : g ∣ g ^ 2 := ⟨g, by ring⟩
  rcases hp.eq_one_or_self_of_dvd g hdvd with h1 | h2
  · linarith
  · nlinarith

/-- If `P^2 = X^2 + Y^2` and `P ∣ Y`, then `Y = 0` or `X = 0`. -/
private lemma int_sq_split {P X Y : ℤ} (h : P ^ 2 = X ^ 2 + Y ^ 2) (hdvd : P ∣ Y) :
    Y = 0 ∨ X = 0 := by
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at h
  have h'' : P ^ 2 * (1 - k ^ 2) = X ^ 2 := by nlinarith [sq_nonneg X]
  by_cases hk0 : k = 0
  · left; simp [hk0, hk]
  · right
    have hk1 : k ≤ -1 ∨ 1 ≤ k := by omega
    have hk2 : k ^ 2 ≥ 1 := by rcases hk1 with hk1 | hk1 <;> nlinarith
    have : P ^ 2 * (1 - k ^ 2) ≤ 0 := by nlinarith
    nlinarith [sq_nonneg X]

/-- Cross-multiplication cancellation for two coprime pairs. -/
private lemma eq_of_mul_eq_mul_coprime {a b c d : ℕ} (hab : Nat.Coprime a b)
    (hcd : Nat.Coprime c d) (hc : 0 < c) (h : a * d = b * c) :
    a = c ∧ b = d := by
  have hac : a ∣ c := by
    have : a ∣ b * c := h.symm ▸ dvd_mul_right a d
    exact hab.dvd_of_dvd_mul_left this
  have hca : c ∣ a := by
    have : c ∣ a * d := h.symm ▸ dvd_mul_left c b
    exact hcd.dvd_of_dvd_mul_right this
  have eq1 : a = c := Nat.dvd_antisymm hac hca
  have eq2 : b = d := by
    have : b * c = d * c := by rw [eq1] at h; ring_nf; exact h.symm
    exact Nat.eq_of_mul_eq_mul_right hc this
  exact ⟨eq1, eq2⟩

/-- Brahmagupta–Fibonacci identity, first form. -/
private lemma brahmagupta_one (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-- Brahmagupta–Fibonacci identity, second form. -/
private lemma brahmagupta_two (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- `p` divides the product `(ad - bc)(ad + bc)`. -/
private lemma dvd_mul_cross {p a b c d : ℕ} (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2) :
    (p : ℤ) ∣ ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) := by
  have heq : (a : ℤ) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
    norm_cast
    linarith
  have h : ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) = (p : ℤ) * (p - c ^ 2 - b ^ 2) := by
    have hc2 : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + b ^ 2 - d ^ 2 := by linarith
    push_cast [hab]
    ring_nf
    rw [hc2]
    ring
  rw [h]
  exact dvd_mul_right _ _

/-- Two representations of a prime as a sum of two squares satisfy one of the two
Brahmagupta degeneracies. -/
private lemma mul_eq_mul_of_two_reps {p a b c d : ℕ} (hp : p.Prime)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2) :
    a * d = b * c ∨ a * c = b * d := by
  have hdiv : (p : ℤ) ∣ ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) := dvd_mul_cross hab hcd
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr hp
  have ha : 0 < a := pos_of_prime_sq_add_sq hp hab
  have hb : 0 < b := pos_of_prime_sq_add_sq hp (by rw [hab, add_comm] : p = b ^ 2 + a ^ 2)
  have hc : 0 < c := pos_of_prime_sq_add_sq hp hcd
  have hd : 0 < d := pos_of_prime_sq_add_sq hp (by rw [hcd, add_comm] : p = d ^ 2 + c ^ 2)
  have hab' : ((p : ℤ)) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab
  have hcd' : ((p : ℤ)) = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hcd
  have hp2 : ((p : ℤ) ^ 2) = ((a : ℤ) * c + b * d) ^ 2 + ((a : ℤ) * d - b * c) ^ 2 := by
    have := brahmagupta_one a b c d
    simp only [← hab', ← hcd'] at this ⊢
    linarith
  have hp2' : ((p : ℤ) ^ 2) = ((a : ℤ) * c - b * d) ^ 2 + ((a : ℤ) * d + b * c) ^ 2 := by
    have := brahmagupta_two a b c d
    simp only [← hab', ← hcd'] at this ⊢
    linarith
  rcases hprime.dvd_or_dvd hdiv with hdvd1 | hdvd2
  · -- Case: p ∣ (ad - bc)
    rcases int_sq_split hp2 hdvd1 with heq | heq
    · left; exact_mod_cast (sub_eq_zero.mp heq)
    · nlinarith [show (a : ℤ) > 0 from mod_cast ha, show (b : ℤ) > 0 from mod_cast hb,
        show (c : ℤ) > 0 from mod_cast hc, show (d : ℤ) > 0 from mod_cast hd]
  · -- Case: p ∣ (ad + bc)
    rcases int_sq_split hp2' hdvd2 with heq | heq
    · nlinarith [show (a : ℤ) > 0 from mod_cast ha, show (b : ℤ) > 0 from mod_cast hb,
        show (c : ℤ) > 0 from mod_cast hc, show (d : ℤ) > 0 from mod_cast hd]
    · right; exact_mod_cast (sub_eq_zero.mp heq)

/-- Uniqueness in Fermat's two-square theorem: a prime p ≡ 1 (mod 4) has an essentially unique
    representation as a sum of two squares (ordered a ≤ b).

    (The hypothesis `hp1 : p % 4 = 1` is not needed for uniqueness; it is kept as it is part of
    the requested statement.) -/
theorem two_squares_unique {p a b c d : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2)
    (h1 : a ≤ b) (h2 : c ≤ d) : a = c ∧ b = d := by
  have hc : 0 < c := pos_of_prime_sq_add_sq hp hcd
  have hdpos : 0 < d := pos_of_prime_sq_add_sq hp (by rw [hcd, add_comm] : p = d ^ 2 + c ^ 2)
  have hcop1 : Nat.Coprime a b := coprime_of_prime_sq_add_sq hp hab
  have hcop2 : Nat.Coprime c d := coprime_of_prime_sq_add_sq hp hcd
  rcases mul_eq_mul_of_two_reps hp hab hcd with h | h
  · exact eq_of_mul_eq_mul_coprime hcop1 hcop2 hc h
  · have := eq_of_mul_eq_mul_coprime hcop1 hcop2.symm hdpos h
    omega

end Brockian.TwoSquaresUnique

