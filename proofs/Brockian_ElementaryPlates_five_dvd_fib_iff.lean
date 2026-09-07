/-
  Brockian/ElementaryPlates.lean — THE ELEMENTARY PLATES CAMPAIGN
  (July 30, from the observation: "if you count by 1 or 6, it makes a
  spiral pattern ray to ray... 4, 9 a mirror of that spiral... 2, 7 a
  star pattern by skipping a ray... 3 and 8 a mirror star... the 5 ray
  is the most interesting as it only has one prime").

  Three plates, three finite theorems:

    PLATE I  (the fold at rest)      — squares mod 5 land on {0,1,4};
                                       the mirror x ↦ −x swaps 1↔4, 2↔3.
    PLATE II (the fold in motion)    — counting by a SQUARE step spirals
                                       (pentagon sides, adjacent rays);
                                       counting by a NONSQUARE step stars
                                       (pentagram diagonals); mirror
                                       partners are negatives.
    PLATE III (the golden return)    — 5 ∣ F_n ⟺ 5 ∣ n; the window
                                       between homecomings turns by ×3
                                       (a nonsquare — the mirror-star
                                       generator); Lucas never comes
                                       home; 20 is a Fibonacci period mod 5.

  Everything on Plates I–II is decidable over ZMod 5. Plate III's
  divisibility law follows from Nat.fib_gcd; the Lucas exclusion and
  Pisano periodicity are induction targets. The geometric φ statement
  (pentagram diagonal / pentagon side = φ) is REAL geometry and is
  deliberately NOT posed here — it lives in prose with a \bC badge.

  Charter as Core.lean. Every `sorry` is a statement target.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.ElementaryPlates

/-! ## Plate I — the fold at rest -/

/-- EP-1 (target, decidable): the squares mod 5 are exactly {0, 1, 4}. -/
theorem squares_mod_five :
    ∀ d : ZMod 5, (∃ x : ZMod 5, x ^ 2 = d) ↔
      d ∈ ({0, 1, 4} : Finset (ZMod 5)) := by decide

/-- EP-2 (target, decidable): the mirror x ↦ −x swaps the two square
rays and the two nonsquare rays: −1 = 4, −2 = 3 in ZMod 5. -/
theorem mirror_pairing :
    (-1 : ZMod 5) = 4 ∧ (-2 : ZMod 5) = 3 := by decide

/-- EP-3 (target, decidable): squaring is mirror-blind — (−x)² = x²,
so the fold cannot see the difference between a number and its mirror. -/
theorem square_mirror_blind :
    ∀ x : ZMod 5, (-x) ^ 2 = x ^ 2 := by
  intro x
  ring

/-! ## Plate II — the fold in motion (the counting-pattern dichotomy) -/

/-- EP-4 (target, decidable): THE COUNTING-PATTERN DICHOTOMY. A nonzero
step d traces the spiral or its mirror (rotation by ±1: pentagon sides)
exactly when d is a square mod 5, and the star or its mirror (rotation
by ±2: pentagram diagonals) exactly when d is a nonsquare. Pattern type
IS the quadratic character of the step. -/
theorem counting_pattern_dichotomy :
    ∀ d : ZMod 5, d ≠ 0 →
      ((d = 1 ∨ d = -1) ↔ IsSquare d) ∧
      ((d = 2 ∨ d = -2) ↔ ¬ IsSquare d) := by decide

/-- EP-5 (target, decidable): mirror partners are negatives — the
mirror spiral is the spiral run backward (4 = −1) and the mirror star
is the star run backward (3 = −2); one symmetry serves both plates. -/
theorem mirror_patterns_are_negatives :
    (4 : ZMod 5) = -1 ∧ (3 : ZMod 5) = -2 ∧
    (∀ d : ZMod 5, IsSquare d → IsSquare (-d)) := by decide
-- NOTE the third conjunct is the invariance that makes "mirror of a
-- spiral is a spiral, mirror of a star is a star" a theorem: −1 is a
-- square mod 5, so negation preserves the sectors.

/-- EP-6 (target, decidable): the radial step. d = 5 (≡ 0) never leaves
its ray, and ray 0 carries exactly one prime among the positive
integers — 5 itself — since any other multiple of 5 is composite.
Finite form: 5 is prime, and n ≡ 0 mod 5 with 5 < n ≤ 100 is never
prime (the decidable window; the general statement is EP-6′ below). -/
theorem radial_ray_one_prime_window :
    Nat.Prime 5 ∧ ∀ n : ℕ, n ≤ 100 → 5 ∣ n → 5 < n → ¬ Nat.Prime n := by
  decide

/-- EP-6′ (target): the general statement — the only prime divisible by
5 is 5. Immediate from Nat.Prime.eq_one_of_self_dvd-style lemmas. -/
theorem radial_ray_one_prime (n : ℕ) (hn : Nat.Prime n) (h5 : 5 ∣ n) :
    n = 5 := by
  obtain ⟨k, rfl⟩ := h5
  rw [Nat.prime_mul_iff] at hn
  omega

/-! ## Plate III — the golden return -/

/-- EP-7 (target): F₅ = 5 — the fifth Fibonacci number is five; the
recurrence of φ manufactures the wheel's own modulus. -/
theorem fib_five : Nat.fib 5 = 5 := by decide

/-- EP-8 (target): THE HOMECOMING LAW. 5 divides F_n exactly when 5
divides n. (Via Nat.fib_gcd: gcd(F₅, F_n) = F_{gcd(5,n)}, and F₅ = 5.) -/
theorem five_dvd_fib_iff (n : ℕ) : 5 ∣ Nat.fib n ↔ 5 ∣ n := by
  constructor
  · intro h
    have hg : 5 ∣ Nat.fib (Nat.gcd 5 n) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd (by norm_num) h
    have hd : Nat.gcd 5 n = 1 ∨ Nat.gcd 5 n = 5 :=
      (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (Nat.gcd_dvd_left 5 n)
    rcases hd with hd | hd
    · simp [hd] at hg
    · exact Nat.gcd_eq_left_iff_dvd.mp hd
  · intro h
    simpa [fib_five] using Nat.fib_dvd 5 n h

/-- EP-9 (target): THE WINDOW TURN. F_{n+5} ≡ 3·F_n (mod 5) — between
homecomings the four-step window is multiplied by 3, a NONSQUARE: the
mirror-star generator drives the golden spiral's ray dance. Iterating this
turn yields the period-20 identity below. -/
theorem fib_window_turn (n : ℕ) :
    (Nat.fib (n + 5) : ZMod 5) = 3 * (Nat.fib n : ZMod 5) := by
  rw [Nat.fib_add]
  push_cast
  norm_num
  rw [show (5 : ZMod 5) = 0 by decide]
  ring

/-- EP-10: `20` is a period of the Fibonacci sequence modulo five. -/
theorem pisano_five (n : ℕ) :
    (Nat.fib (n + 20) : ZMod 5) = (Nat.fib n : ZMod 5) := by
  rw [Nat.fib_add]
  push_cast
  norm_num
  rw [show (4181 : ZMod 5) = 1 by decide,
      show (6765 : ZMod 5) = 0 by decide]
  ring

/-- The Lucas sequence (local definition; Mathlib's lucas via
fib-recurrence identities may be substituted at proving time). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

/-- The Lucas residues modulo five repeat as `2, 1, 3, 4`. -/
lemma lucas_mod_five_cycle (n : ℕ) :
    lucas n % 5 = match n % 4 with
      | 0 => 2
      | 1 => 1
      | 2 => 3
      | _ => 4 := by
  have period4 : ∀ k, lucas (4 * k) % 5 = 2 ∧ lucas (4 * k + 1) % 5 = 1 ∧
             lucas (4 * k + 2) % 5 = 3 ∧ lucas (4 * k + 3) % 5 = 4 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have h4k4 : lucas (4 * (k + 1)) = lucas (4 * k + 4) := by ring_nf
      have h4k5 : lucas (4 * (k + 1) + 1) = lucas (4 * k + 5) := by ring_nf
      have h4k6 : lucas (4 * (k + 1) + 2) = lucas (4 * k + 6) := by ring_nf
      have h4k7 : lucas (4 * (k + 1) + 3) = lucas (4 * k + 7) := by ring_nf
      rw [h4k4, h4k5, h4k6, h4k7]
      have rec1 : lucas (4 * k + 4) = lucas (4 * k + 2) + lucas (4 * k + 3) := by
        simp [lucas]
      have rec2 : lucas (4 * k + 5) = lucas (4 * k + 3) + lucas (4 * k + 4) := by
        simp [lucas]
      have rec3 : lucas (4 * k + 6) = lucas (4 * k + 4) + lucas (4 * k + 5) := by
        simp [lucas]
      have rec4 : lucas (4 * k + 7) = lucas (4 * k + 5) + lucas (4 * k + 6) := by
        simp [lucas]
      rw [rec1, rec2, rec3, rec4]
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      omega
  obtain ⟨h0, h1, h2, h3⟩ := period4 (n / 4)
  have hmod : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  have heq : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  interval_cases n % 4 <;> rw [heq] <;> assumption

/-- EP-11 (target): THE EXILE. 5 never divides a Lucas number — the
same recurrence, seeded 2, 1, never touches the home ray. (Mod-5 orbit
is the 4-cycle 2, 1, 3, 4; induction on the period-4 pattern.) -/
theorem lucas_never_home (n : ℕ) : ¬ (5 ∣ lucas n) := by
  rw [Nat.dvd_iff_mod_eq_zero, lucas_mod_five_cycle]
  have h : n % 4 < 4 := Nat.mod_lt n (by omega)
  interval_cases n % 4 <;> simp

end Brockian.ElementaryPlates
