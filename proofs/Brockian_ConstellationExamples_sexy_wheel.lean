import Mathlib
import Brockian.ConstellationLocalCount
import Brockian.ConstellationMultiplicative
import Brockian.ConstellationWheel

/-
# Constellation Sieve Spectrum — worked NAMED constellations (generalization module).

The three verified bricks establish a *general* prime-constellation confinement theory:

* Brick 1 (`ConstellationLocalCount.local_admissible_count_prime`): at a prime `p`, the residues
  dodging a constellation `H` number exactly `p − ν_p`, where `ν_p = |H mod p|`.
* Brick 2 (`ConstellationMultiplicative`): wheel admissibility is multiplicative across coprime
  moduli.
* Brick 3 (`ConstellationWheel.admissibleU_squarefree`): for squarefree `Q`, the wheel count is
  the exact Euler product `∏_{p ∣ Q} (p − ν_p)`.

This file exercises that machinery on named constellations *beyond twins*, proving the LOCAL
confinement count `p − ν` and the WHEEL Euler product `∏ (p − ν)` for each. The pattern in each
case is: (i) compute the distinct-residue count `ν_p = |H mod p|` at the relevant primes by
showing the offsets are pairwise distinct mod `p` (each nonzero pairwise difference is a unit,
i.e. `p` does not divide it); (ii) instantiate Brick 1 for the local count; (iii) instantiate
Brick 3 for the wheel product.

Constellations covered:

* **COUSIN primes** `H = {0, 4}` — `cousin_local` (`p ≥ 3`), `cousin_wheel`. `ν = 2`.
* **SEXY primes**   `H = {0, 6}` — `sexy_local`   (`p ≥ 5`), `sexy_wheel`.   `ν = 2`.
* **PRIME TRIPLE**  `H = {0, 2, 6}` — `triple_local` (`p ≥ 7`), `triple_wheel`. `ν = 3`.

These are *exact counts of admissible residues*, generalizing the twin factor `∏ (p − 2)` to
other Hardy–Littlewood constellation factors. This is a demonstration that the Brick-1/Brick-3
machinery is a general constellation theory — it is **NOT** a proof of any open conjecture
(the infinitude of cousin/sexy primes or admissible triples remains open).

No `sorry`, `admit`, `native_decide`, or `axiom` is used. Core Mathlib only.
-/

namespace Brockian.ConstellationExamples

open Finset
open Brockian.ConstellationMultiplicative
open Brockian.ConstellationWheel

/-! ## 1. Cousin primes `H = {0, 4}` — local count and wheel product (`ν = 2`). -/

/-- **Cousin constellation confinement (local).** For a prime `p ≥ 3`, the cousin pattern
`H = {0, 4}` admits exactly `p − 2` residues: those `a` with `a ≠ 0` and `a + 4 ≠ 0`. The two
offsets `0, 4` are distinct mod `p` because `p ∤ 4` for `p ≥ 3` (`4 = 2·2`, so `p ∣ 4 ⇒ p = 2`),
giving `ν = 2`. -/
theorem cousin_local (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (univ.filter (fun a : ZMod p => a ≠ 0 ∧ a + 4 ≠ 0)).card = p - 2 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hpp : p.Prime := Fact.out
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hc
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 4] at h4
    have h4' : p ∣ 2 * 2 := by rw [show (2 : ℕ) * 2 = 4 from by norm_num]; exact h4
    rcases (hpp.dvd_mul).mp h4' with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have hne : ((0 : ℤ) : ZMod p) ≠ ((4 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h4ne hc.symm
  have himg : (({0, 4} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 2 := by
    rw [Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  have key := Brockian.ConstellationLocalCount.local_admissible_count_prime p ({0, 4} : Finset ℤ)
  rw [himg] at key
  rw [← key]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h0, h4'⟩ h (rfl | rfl)
    · simpa using h0
    · simpa using h4'
  · intro h
    exact ⟨by simpa using h 0 (Or.inl rfl), by simpa using h 4 (Or.inr rfl)⟩

/-- **Cousin wheel product.** For a squarefree modulus `Q` all of whose prime factors are `≥ 3`,
the cousin constellation `H = {0, 4}` has wheel count exactly `∏_{p ∣ Q} (p − 2)`. At each prime
`p ≥ 3` the offsets `0, 4` are distinct mod `p`, so `ν_p = 2`; rewriting each factor of the wheel
product of `admissibleU_squarefree` gives the result. -/
theorem cousin_wheel (Q : ℕ) [NeZero Q] (hQ : Squarefree Q)
    (h3 : ∀ p ∈ Q.primeFactors, 3 ≤ p) :
    (admissibleU Q ({0, 4} : Finset ℤ)).card = ∏ p ∈ Q.primeFactors, (p - 2) := by
  classical
  rw [Brockian.ConstellationWheel.admissibleU_squarefree Q hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hp3 : 3 ≤ p := h3 p hp
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hc
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 4] at h4
    have h4' : p ∣ 2 * 2 := by rw [show (2 : ℕ) * 2 = 4 from by norm_num]; exact h4
    rcases (hpp.dvd_mul).mp h4' with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have hne : ((0 : ℤ) : ZMod p) ≠ ((4 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h4ne hc.symm
  have himg : (({0, 4} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 2 := by
    rw [Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  rw [himg]

/-! ## 2. Sexy primes `H = {0, 6}` — local count and wheel product (`ν = 2`). -/

/-- **Sexy constellation confinement (local).** For a prime `p ≥ 5`, the sexy pattern
`H = {0, 6}` admits exactly `p − 2` residues: those `a` with `a ≠ 0` and `a + 6 ≠ 0`. The two
offsets `0, 6` are distinct mod `p` because `p ∤ 6` for `p ≥ 5` (`6 = 2·3`, so `p ∣ 6 ⇒ p ∈
{2,3}`), giving `ν = 2`. -/
theorem sexy_local (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (univ.filter (fun a : ZMod p => a ≠ 0 ∧ a + 6 ≠ 0)).card = p - 2 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hpp : p.Prime := Fact.out
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro hc
    have h6 : ((6 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 6] at h6
    have h6' : p ∣ 2 * 3 := by rw [show (2 : ℕ) * 3 = 6 from by norm_num]; exact h6
    rcases (hpp.dvd_mul).mp h6' with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have hne : ((0 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h6ne hc.symm
  have himg : (({0, 6} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 2 := by
    rw [Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  have key := Brockian.ConstellationLocalCount.local_admissible_count_prime p ({0, 6} : Finset ℤ)
  rw [himg] at key
  rw [← key]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h0, h6'⟩ h (rfl | rfl)
    · simpa using h0
    · simpa using h6'
  · intro h
    exact ⟨by simpa using h 0 (Or.inl rfl), by simpa using h 6 (Or.inr rfl)⟩

/-- **Sexy wheel product.** For a squarefree modulus `Q` all of whose prime factors are `≥ 5`,
the sexy constellation `H = {0, 6}` has wheel count exactly `∏_{p ∣ Q} (p − 2)`. At each prime
`p ≥ 5` the offsets `0, 6` are distinct mod `p`, so `ν_p = 2`. -/
theorem sexy_wheel (Q : ℕ) [NeZero Q] (hQ : Squarefree Q)
    (h5 : ∀ p ∈ Q.primeFactors, 5 ≤ p) :
    (admissibleU Q ({0, 6} : Finset ℤ)).card = ∏ p ∈ Q.primeFactors, (p - 2) := by
  classical
  rw [Brockian.ConstellationWheel.admissibleU_squarefree Q hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hp5 : 5 ≤ p := h5 p hp
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro hc
    have h6 : ((6 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 6] at h6
    have h6' : p ∣ 2 * 3 := by rw [show (2 : ℕ) * 3 = 6 from by norm_num]; exact h6
    rcases (hpp.dvd_mul).mp h6' with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have hne : ((0 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h6ne hc.symm
  have himg : (({0, 6} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 2 := by
    rw [Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  rw [himg]

/-! ## 3. Prime triple `H = {0, 2, 6}` — local count and wheel product (`ν = 3`). -/

/-- **Prime-triple constellation confinement (local).** For a prime `p ≥ 7`, the admissible
triple pattern `H = {0, 2, 6}` admits exactly `p − 3` residues: those `a` with `a ≠ 0`,
`a + 2 ≠ 0`, and `a + 6 ≠ 0`. The three offsets `0, 2, 6` are pairwise distinct mod `p` because
their pairwise differences `2, 4, 6` are all `< 7 ≤ p` (so `p` divides none of them), giving
`ν = 3`. -/
theorem triple_local (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (univ.filter (fun a : ZMod p => a ≠ 0 ∧ a + 2 ≠ 0 ∧ a + 6 ≠ 0)).card = p - 3 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 2] at h2
    have := Nat.le_of_dvd (by norm_num) h2; omega
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hc
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 4] at h4
    have := Nat.le_of_dvd (by norm_num) h4; omega
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro hc
    have h6 : ((6 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 6] at h6
    have := Nat.le_of_dvd (by norm_num) h6; omega
  have hne02 : ((0 : ℤ) : ZMod p) ≠ ((2 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h2ne hc.symm
  have hne06 : ((0 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h6ne hc.symm
  have hne26 : ((2 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; apply h4ne; linear_combination -hc
  have himg : (({0, 2, 6} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 3 := by
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hne02, hne06⟩),
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne26),
        Finset.card_singleton]
  have key := Brockian.ConstellationLocalCount.local_admissible_count_prime p ({0, 2, 6} : Finset ℤ)
  rw [himg] at key
  rw [← key]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h0, h2, h6⟩ h (rfl | rfl | rfl)
    · simpa using h0
    · simpa using h2
    · simpa using h6
  · intro h
    exact ⟨by simpa using h 0 (Or.inl rfl),
           by simpa using h 2 (Or.inr (Or.inl rfl)),
           by simpa using h 6 (Or.inr (Or.inr rfl))⟩

/-- **Prime-triple wheel product.** For a squarefree modulus `Q` all of whose prime factors are
`≥ 7`, the admissible triple `H = {0, 2, 6}` has wheel count exactly `∏_{p ∣ Q} (p − 3)`. At each
prime `p ≥ 7` the offsets `0, 2, 6` are pairwise distinct mod `p`, so `ν_p = 3`. -/
theorem triple_wheel (Q : ℕ) [NeZero Q] (hQ : Squarefree Q)
    (h7 : ∀ p ∈ Q.primeFactors, 7 ≤ p) :
    (admissibleU Q ({0, 2, 6} : Finset ℤ)).card = ∏ p ∈ Q.primeFactors, (p - 3) := by
  classical
  rw [Brockian.ConstellationWheel.admissibleU_squarefree Q hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hp7 : 7 ≤ p := h7 p hp
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 2] at h2
    have := Nat.le_of_dvd (by norm_num) h2; omega
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hc
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 4] at h4
    have := Nat.le_of_dvd (by norm_num) h4; omega
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro hc
    have h6 : ((6 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 6] at h6
    have := Nat.le_of_dvd (by norm_num) h6; omega
  have hne02 : ((0 : ℤ) : ZMod p) ≠ ((2 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h2ne hc.symm
  have hne06 : ((0 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; exact h6ne hc.symm
  have hne26 : ((2 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) := by
    intro hc; push_cast at hc; apply h4ne; linear_combination -hc
  have himg : (({0, 2, 6} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 3 := by
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hne02, hne06⟩),
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne26),
        Finset.card_singleton]
  rw [himg]

end Brockian.ConstellationExamples
