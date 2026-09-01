import Mathlib

/-!
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

namespace Brockian
namespace ConeLine

/-- A prime `p > 5` is not divisible by `5`. -/
theorem not_five_dvd_of_prime_gt_five {n : ℕ} (hn : n.Prime) (h : 5 < n) : ¬ (5 ∣ n) := by
  intro hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h1 <;> omega

/-- Cousin primes `(p, p+4)` with `p > 5` travel exactly the roads
`2 → 1`, `3 → 2`, `4 → 3` on the five-ray wheel. -/
theorem cousin_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 4).Prime) (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have h1 : ¬ (5 ∣ p) := not_five_dvd_of_prime_gt_five hp h5
  have h2 : ¬ (5 ∣ (p + 4)) := not_five_dvd_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at h1 h2
  have hmod : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hkey : (p + 4) % 5 = (p % 5 + 4) % 5 := by
    omega
  simp only [Prod.mk.injEq]
  interval_cases h : (p % 5) <;> omega

end ConeLine
end Brockian

