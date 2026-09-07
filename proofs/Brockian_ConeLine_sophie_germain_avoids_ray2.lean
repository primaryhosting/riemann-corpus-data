import Mathlib

/-!
# Brockian Cone Line — Ray-Walks on the Number Line mod 5 / mod 20
Category: Cone Line
Provenance: Aristotle theorem prover (Harmonic); assembled from individually
AXLE-verified proof files into a single module.

Shared defs + helper lemmas declared once, followed by the distinct main
theorems (statements preserved verbatim from their canonically-named source
files).
-/

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

namespace Brockian.ConeLine

/-! ## Shared helper lemmas -/

/-- A prime `n > 5` is not divisible by `5`, i.e. `n % 5 ≠ 0`. -/
theorem mod_five_ne_zero_of_prime {n : ℕ} (hn : n.Prime) (h5 : 5 < n) : n % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h1 <;> omega

/-- A prime `q` greater than `5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
theorem mod_five_ne_zero_of_prime_gt_five {q : ℕ} (hq : Nat.Prime q) (h5 : 5 < q) :
    q % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h | h <;> omega

/-! ## Cousin prime roads -/

/-- **Cousin prime roads.** For a cousin prime pair `(p, p + 4)` with `5 < p`, the residues
mod `5` travel exactly the roads `2 → 1`, `3 → 2`, `4 → 3` on the five-ray wheel. -/
theorem cousin_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 4))
    (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have hp5 : p % 5 ≠ 0 := by
    intro h
    have hdvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 5 hdvd) with h1 | h1 <;> omega
  have hq5 : (p + 4) % 5 ≠ 0 := by
    intro h
    have hdvd : (5 : ℕ) ∣ (p + 4) := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h1 | h1 <;> omega
  simp only [Prod.mk.injEq]
  omega

/-! ## Sexy prime roads -/

/-- A sexy prime pair `(p, p + 6)` with `p > 5` travels exactly the roads
`1 → 2`, `2 → 3`, `3 → 4` modulo `5`. -/
theorem sexy_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 6))
    (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have hnp : ¬ (5 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h
    omega
  have hnq : ¬ (5 ∣ (p + 6)) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h
    omega
  have h1 : p % 5 ≠ 0 := fun h => hnp (Nat.dvd_of_mod_eq_zero h)
  have h2 : (p + 6) % 5 ≠ 0 := fun h => hnq (Nat.dvd_of_mod_eq_zero h)
  simp only [Prod.mk.injEq]
  omega

/-! ## Sophie Germain avoids ray 2 -/

/-- A Sophie Germain prime `p > 5` never has residue `2` modulo `5`, and the pair of
residues `(p % 5, (2 * p + 1) % 5)` is one of `(1, 3)`, `(3, 2)`, `(4, 4)`. -/
theorem sophie_germain_avoids_ray2 (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (2 * p + 1))
    (h5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hp5 : ¬ (5 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h
    omega
  have hq5 : ¬ (5 ∣ (2 * p + 1)) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).1 h
    omega
  have hp5' : p % 5 ≠ 0 := fun h => hp5 (Nat.dvd_of_mod_eq_zero h)
  have hq5' : (2 * p + 1) % 5 ≠ 0 := fun h => hq5 (Nat.dvd_of_mod_eq_zero h)
  refine ⟨by omega, ?_⟩
  have : p % 5 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases this with h | h | h
  · exact Or.inl (by simp [Prod.ext_iff]; omega)
  · exact Or.inr (Or.inl (by simp [Prod.ext_iff]; omega))
  · exact Or.inr (Or.inr (by simp [Prod.ext_iff]; omega))

/-! ## Triplet two patterns -/

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible residue
patterns modulo `5`: `(1, 3, 2)` or `(2, 4, 3)`. -/
theorem triplet_two_patterns {p : ℕ} (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hp6 : Nat.Prime (p + 6)) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
      (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h0 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime_gt_five hp h5
  have h2 : (p + 2) % 5 ≠ 0 := mod_five_ne_zero_of_prime_gt_five hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := mod_five_ne_zero_of_prime_gt_five hp6 (by omega)
  omega

/-- Both patterns are realized: `(11, 13, 17)` gives the pattern `(1, 3, 2)`. -/
example : Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ 5 < 11 ∧
    11 % 5 = 1 ∧ 13 % 5 = 3 ∧ 17 % 5 = 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Both patterns are realized: `(17, 19, 23)` gives the pattern `(2, 4, 3)`. -/
example : Nat.Prime 17 ∧ Nat.Prime 19 ∧ Nat.Prime 23 ∧ 5 < 17 ∧
    17 % 5 = 2 ∧ 19 % 5 = 4 ∧ 23 % 5 = 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Quadruplet visits all active rays -/

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` visits all four nonzero residue
classes mod `5`, in the order `(1, 3, 2, 4)`; in particular `p ≡ 1 [MOD 5]`. -/
theorem quadruplet_visits_all_active_rays {p : ℕ} (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hp6 : Nat.Prime (p + 6)) (hp8 : Nat.Prime (p + 8)) (hgt : 5 < p) :
    p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2 ∧ (p + 8) % 5 = 4 := by
  have h0 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp (by omega)
  have h2 : (p + 2) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp6 (by omega)
  have h8 : (p + 8) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp8 (by omega)
  omega

/-! ## Square residues mod 5 -/

/-- Perfect squares land only on rays `0`, `1`, `4`: for every `n : ZMod 5`,
`n ^ 2` is `0`, `1` or `4` (rays `2` and `3` are square-free). -/
theorem square_mod5_mem (n : ZMod 5) : n ^ 2 = 0 ∨ n ^ 2 = 1 ∨ n ^ 2 = 4 := by
  revert n
  decide +kernel

/-- Integer form: for every `n : ℤ`, the class of `n ^ 2` in `ZMod 5` is `0`, `1` or `4`. -/
theorem square_mod5_mem_int (n : ℤ) :
    ((n ^ 2 : ℤ) : ZMod 5) = 0 ∨ ((n ^ 2 : ℤ) : ZMod 5) = 1 ∨ ((n ^ 2 : ℤ) : ZMod 5) = 4 := by
  rw [Int.cast_pow]
  exact square_mod5_mem (n : ZMod 5)

/-- `Finset` membership form of `square_mod5_mem`. -/
theorem square_mod5_mem_finset (n : ZMod 5) : n ^ 2 ∈ ({0, 1, 4} : Finset (ZMod 5)) := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using square_mod5_mem n

/-- Integer/`Int.emod` form: `n ^ 2 % 5 ∈ {0, 1, 4}` for every integer `n`. -/
theorem square_mod5_emod_mem (n : ℤ) : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
  have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hsq : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by
    rw [pow_two, pow_two, Int.mul_emod]
  rcases h with h | h | h | h | h <;> rw [hsq, h] <;> norm_num

/-! ## Square-ray primes mod 20 -/

/-- A prime `p > 5` with `p ≡ 1` or `4 (mod 5)` satisfies `p % 20 ∈ {1, 9, 11, 19}`. -/
theorem square_ray_primes_mod20 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 < p)
    (h : p % 5 = 1 ∨ p % 5 = 4) :
    p % 20 = 1 ∨ p % 20 = 9 ∨ p % 20 = 11 ∨ p % 20 = 19 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  omega

/-! ## Triangular numbers mod 5 -/

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division,
which is exact since `n(n+1)` is even). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Shifting the index by `10` does not change a triangular number modulo `5`:
`T (n + 10) = T n + 10 * n + 55`. -/
lemma T_add_ten_mod_five (n : ℕ) : T (n + 10) % 5 = T n % 5 := by
  have hx : (n + 10) * (n + 10 + 1) = n * (n + 1) + 20 * n + 110 := by ring
  have h2 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  unfold T
  rw [hx]
  omega

/-- Modulo `5`, a triangular number is `0`, `1` or `3`. -/
lemma T_mod_five (n : ℕ) : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 10 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      rw [T_add_ten_mod_five]
      exact ih m (by omega)

/-- **Triangular numbers land only on rays `0`, `1`, `3` modulo `5`.**
For every `n`, the triangular number `T n = n(n+1)/2`, viewed in `ZMod 5`,
lies in `{0, 1, 3}`; rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_mem (n : ℕ) : ((T n : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have h : ((T n : ℕ) : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod _ _).symm
  rcases T_mod_five n with h5 | h5 | h5 <;> rw [h, h5] <;> simp

/-! ## Fibonacci uniformity mod 5 -/

/-- Within one Pisano period (20 terms), each residue mod 5 occurs exactly 4 times
among `Nat.fib k % 5` for `k < 20`; together with the Pisano-20 restart
`fib 20 % 5 = 0` and `fib 21 % 5 = 1`. -/
theorem fib_uniform_mod5 :
    (∀ r : Fin 5,
      ((Finset.range 20).filter (fun k => Nat.fib k % 5 = r.val)).card = 4) ∧
    Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  decide

/-! ## Stride ray-walk classification -/

/-- The ray reached after `k+1` strides of length `s`, i.e. `((k+1)*s) % 5`. -/
def rayWalk (s : ℕ) : List ℕ := (List.range 5).map (fun k => ((k + 1) * s) % 5)

/-- Each stride advances the ray by the constant `s % 5`. -/
theorem ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  rw [Nat.add_mul, one_mul, Nat.add_mod]

/-- The walk of `s` on the five rays is determined by `s % 5`:
    `≡ 2` traces the pentagram order `[2,4,1,3,0]`, `≡ 3` its mirror `[3,1,4,2,0]`,
    `≡ 1` the pentagon `[1,2,3,4,0]`, `≡ 4` its mirror `[4,3,2,1,0]`,
    and `≡ 0` never leaves ray `0`. -/
theorem stride_ray_walk_classification :
    (∀ s k : ℕ, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : ℕ, s % 5 = 2 → rayWalk s = [2, 4, 1, 3, 0]) ∧
    (∀ s : ℕ, s % 5 = 3 → rayWalk s = [3, 1, 4, 2, 0]) ∧
    (∀ s : ℕ, s % 5 = 1 → rayWalk s = [1, 2, 3, 4, 0]) ∧
    (∀ s : ℕ, s % 5 = 4 → rayWalk s = [4, 3, 2, 1, 0]) ∧
    (∀ s : ℕ, s % 5 = 0 → rayWalk s = [0, 0, 0, 0, 0]) := by
  refine ⟨ray_step, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro s hs <;>
    simp [rayWalk, List.range_succ, Nat.mul_mod, hs]

end Brockian.ConeLine
