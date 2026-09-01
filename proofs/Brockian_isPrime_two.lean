/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-! ## Primes and admissibility -/

/-- Primality of a natural number. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  have hle : m ≤ 2 := Nat.le_of_dvd (by omega) hm
  have hm0 : m ≠ 0 := by
    intro h
    subst h
    obtain ⟨k, hk⟩ := hm
    omega
  omega

/-- A finite tuple `H` of integers (a *gap pattern*) is **admissible** if for every prime `p`
the members of `H` do not cover all residue classes modulo `p`, i.e. some class `r` is avoided.
Equivalently, every local factor of the Hardy–Littlewood singular series of `H` is nonzero. -/
def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, IsPrime p → ∃ r : Int, ∀ h ∈ H, ¬ ((p : Int) ∣ h - r)

/-- No nonzero integer of absolute value smaller than `p` is divisible by `p`. -/
theorem not_dvd_of_abs_lt {p : Nat} {x : Int} (hx : x ≠ 0) (h1 : -(p : Int) < x)
    (h2 : x < (p : Int)) : ¬ ((p : Int) ∣ x) := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  by_cases hpos : 0 < x
  · have := Int.le_of_dvd hpos ⟨k, hk⟩
    omega
  · have hneg : x < 0 := by omega
    have hd' : (p : Int) ∣ -x := ⟨-k, by simp [hk, Int.mul_neg]⟩
    have := Int.le_of_dvd (by omega) hd'
    omega

/-- A prime other than `2` is at least `3`. -/
theorem three_le_of_prime_ne_two {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.1
  omega

/-- **Admissibility of a two-element gap pattern.**
The pattern `{0, h}` is admissible if and only if the gap `h` is even. -/
theorem admissible_pair_iff_even (h : Int) : Admissible [0, h] ↔ h % 2 = 0 := by
  constructor
  · intro hadm
    obtain ⟨r, hr⟩ := hadm 2 isPrime_two
    have h0 : ¬ ((2 : Int) ∣ (0 : Int) - r) := hr 0 (by simp)
    have h1 : ¬ ((2 : Int) ∣ h - r) := hr h (by simp)
    omega
  · intro he p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, ?_⟩
      intro x hx
      have hx' : x = 0 ∨ x = h := by simpa using hx
      rcases hx' with rfl | rfl
      · intro hd
        omega
      · intro hd
        omega
    · have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp hp2
      have hp3' : (3 : Int) ≤ (p : Int) := by omega
      by_cases hd : (p : Int) ∣ h - 1
      · refine ⟨2, ?_⟩
        intro x hx
        have hx' : x = 0 ∨ x = h := by simpa using hx
        rcases hx' with rfl | rfl
        · exact not_dvd_of_abs_lt (by omega) (by omega) (by omega)
        · intro hcon
          have hsub : (p : Int) ∣ (x - 1) - (x - 2) := Int.dvd_sub hd hcon
          have h1 : (x - 1) - (x - 2) = 1 := by omega
          rw [h1] at hsub
          exact not_dvd_of_abs_lt (x := 1) (by omega) (by omega) (by omega) hsub
      · refine ⟨1, ?_⟩
        intro x hx
        have hx' : x = 0 ∨ x = h := by simpa using hx
        rcases hx' with rfl | rfl
        · exact not_dvd_of_abs_lt (by omega) (by omega) (by omega)
        · exact hd

/-! ## The singular series factor -/

/-- Boolean primality test by trial division. -/
def isPrimeB (p : Nat) : Bool :=
  2 ≤ p && (List.range p).all (fun d => d < 2 || !(p % d == 0))

/-- The list of odd prime divisors of `h`. -/
def oddPrimeDivisors (h : Nat) : List Nat :=
  (List.range (h + 1)).filter (fun p => (3 ≤ p) && (h % p == 0) && isPrimeB p)

/-- The boolean test is sound: it only accepts primes. -/
theorem isPrime_of_isPrimeB {p : Nat} (hp : isPrimeB p = true) : IsPrime p := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨hp2, hall⟩ := hp
  refine ⟨hp2, ?_⟩
  intro m hm
  by_cases hmp : m = p
  · exact Or.inr hmp
  · left
    have hmle : m ≤ p := Nat.le_of_dvd (by omega) hm
    have hmlt : m < p := by omega
    have := hall m (List.mem_range.mpr hmlt)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] at this
    obtain ⟨k, hk⟩ := hm
    have hmod : p % m = 0 := by rw [hk]; exact Nat.mul_mod_right m k
    have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      omega
    rcases this with h | h
    · omega
    · exact absurd hmod h

/-- Every member of `oddPrimeDivisors h` really is an odd prime divisor of `h`. -/
theorem mem_oddPrimeDivisors_spec {h p : Nat} (hp : p ∈ oddPrimeDivisors h) :
    3 ≤ p ∧ IsPrime p ∧ p ∣ h := by
  have h2 := (List.mem_filter.mp hp).2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  exact ⟨h2.1.1, isPrime_of_isPrimeB h2.2, Nat.dvd_of_mod_eq_zero h2.1.2⟩

theorem three_le_of_mem_oddPrimeDivisors {h p : Nat} (hp : p ∈ oddPrimeDivisors h) : 3 ≤ p :=
  (mem_oddPrimeDivisors_spec hp).1

/-- Numerator of the singular series factor: `∏ (p - 1)`. -/
def numProd : List Nat → Nat
  | [] => 1
  | p :: l => (p - 1) * numProd l

/-- Denominator of the singular series factor: `∏ (p - 2)`. -/
def denProd : List Nat → Nat
  | [] => 1
  | p :: l => (p - 2) * denProd l

theorem denProd_pos {l : List Nat} (hl : ∀ p ∈ l, 3 ≤ p) : 0 < denProd l := by
  induction l with
  | nil => exact Nat.zero_lt_one
  | cons p l ih =>
      have hp : 3 ≤ p := hl p (by simp)
      have hrest : ∀ q ∈ l, 3 ≤ q := fun q hq => hl q (by simp [hq])
      have hih := ih hrest
      show 0 < (p - 2) * denProd l
      exact Nat.mul_pos (by omega) hih

theorem denProd_le_numProd {l : List Nat} (hl : ∀ p ∈ l, 3 ≤ p) : denProd l ≤ numProd l := by
  induction l with
  | nil => exact Nat.le_refl 1
  | cons p l ih =>
      have hp : 3 ≤ p := hl p (by simp)
      have hrest : ∀ q ∈ l, 3 ≤ q := fun q hq => hl q (by simp [hq])
      have hih := ih hrest
      show (p - 2) * denProd l ≤ (p - 1) * numProd l
      exact Nat.mul_le_mul (by omega) hih

/-- The odd part of the Hardy–Littlewood singular series factor,
`𝔖₀(h) = ∏_{p ∣ h, p > 2} (p-1)/(p-2)`, is well defined and at least `1`:
its denominator is positive and bounded above by its numerator. -/
theorem singularFactor_ge_one (h : Nat) :
    0 < denProd (oddPrimeDivisors h) ∧
      denProd (oddPrimeDivisors h) ≤ numProd (oddPrimeDivisors h) :=
  ⟨denProd_pos (fun _ hp => three_le_of_mem_oddPrimeDivisors hp),
   denProd_le_numProd (fun _ hp => three_le_of_mem_oddPrimeDivisors hp)⟩

/-! ## Main result -/

/-- **Singular Series Gaps 1240–1250.**

For every gap `h` in the range `1240 ≤ h ≤ 1250`:

* the gap pattern `{0, h}` is admissible exactly when `h` is even, and
* for such an admissible gap the singular series factor `∏_{p ∣ h, p > 2} (p-1)/(p-2)`
  is a well-defined rational number that is at least `1` (its denominator is positive and
  at most its numerator), so the Hardy–Littlewood singular series of the pattern `{0, h}`
  is strictly positive.
-/
theorem SingularSeriesGaps12401250 :
    ∀ h : Nat, 1240 ≤ h → h ≤ 1250 →
      (Admissible [0, (h : Int)] ↔ h % 2 = 0) ∧
      (h % 2 = 0 →
        0 < denProd (oddPrimeDivisors h) ∧
          denProd (oddPrimeDivisors h) ≤ numProd (oddPrimeDivisors h)) := by
  intro h _ _
  refine ⟨?_, fun _ => singularFactor_ge_one h⟩
  rw [admissible_pair_iff_even]
  omega

/-! ## Explicit data for the range 1240–1250 -/

/-- Each even gap in the range `1240 ≤ h ≤ 1250` is admissible. -/
theorem admissible_even_gaps_1240_1250 :
    ∀ h ∈ [1240, 1242, 1244, 1246, 1248, 1250], Admissible [0, (h : Int)] := by
  intro h hh
  have hcases : h = 1240 ∨ h = 1242 ∨ h = 1244 ∨ h = 1246 ∨ h = 1248 ∨ h = 1250 := by
    simpa using hh
  refine (admissible_pair_iff_even _).mpr ?_
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Each odd gap in the range `1240 ≤ h ≤ 1250` fails to be admissible. -/
theorem not_admissible_odd_gaps_1240_1250 :
    ∀ h ∈ [1241, 1243, 1245, 1247, 1249], ¬ Admissible [0, (h : Int)] := by
  intro h hh
  have hcases : h = 1241 ∨ h = 1243 ∨ h = 1245 ∨ h = 1247 ∨ h = 1249 := by
    simpa using hh
  intro hadm
  have := (admissible_pair_iff_even (h : Int)).mp hadm
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- The odd prime divisors of the even gaps in the range `1240 ≤ h ≤ 1250`. -/
theorem oddPrimeDivisors_values_1240_1250 :
    oddPrimeDivisors 1240 = [5, 31] ∧ oddPrimeDivisors 1242 = [3, 23] ∧
      oddPrimeDivisors 1244 = [311] ∧ oddPrimeDivisors 1246 = [7, 89] ∧
      oddPrimeDivisors 1248 = [3, 13] ∧ oddPrimeDivisors 1250 = [5] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Explicit values of the singular series factor `∏_{p ∣ h, p > 2} (p-1)/(p-2)`
for the even gaps in the range `1240 ≤ h ≤ 1250`:
`120/87, 44/21, 310/309, 528/435, 24/11, 4/3`. -/
theorem singularFactor_values_1240_1250 :
    (numProd (oddPrimeDivisors 1240) = 120 ∧ denProd (oddPrimeDivisors 1240) = 87) ∧
    (numProd (oddPrimeDivisors 1242) = 44 ∧ denProd (oddPrimeDivisors 1242) = 21) ∧
    (numProd (oddPrimeDivisors 1244) = 310 ∧ denProd (oddPrimeDivisors 1244) = 309) ∧
    (numProd (oddPrimeDivisors 1246) = 528 ∧ denProd (oddPrimeDivisors 1246) = 435) ∧
    (numProd (oddPrimeDivisors 1248) = 24 ∧ denProd (oddPrimeDivisors 1248) = 11) ∧
    (numProd (oddPrimeDivisors 1250) = 4 ∧ denProd (oddPrimeDivisors 1250) = 3) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := oddPrimeDivisors_values_1240_1250
  refine ⟨⟨by rw [e1]; decide, by rw [e1]; decide⟩, ⟨by rw [e2]; decide, by rw [e2]; decide⟩, ⟨by rw [e3]; decide, by rw [e3]; decide⟩,
    ⟨by rw [e4]; decide, by rw [e4]; decide⟩, ⟨by rw [e5]; decide, by rw [e5]; decide⟩, ⟨by rw [e6]; decide, by rw [e6]; decide⟩⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

