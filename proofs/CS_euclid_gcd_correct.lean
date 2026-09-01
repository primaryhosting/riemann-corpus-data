/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- Euclid's algorithm, in its modulus form.
The recursion is on the second argument, which strictly decreases at each
recursive call; the termination checker verifies this, so the function is
total: the algorithm terminates on every input. -/
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- The step equation of Euclid's algorithm for an arbitrary nonzero modulus. -/
theorem euclid_pos (a b : Nat) (hb : 0 < b) : euclid a b = euclid b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact euclid_succ a c

/-- Euclid's algorithm computes the greatest common divisor. -/
theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction a, b using euclid.induct with
  | case1 a => rw [euclid_zero, Nat.gcd_zero_right]
  | case2 a b ih =>
      rw [euclid_succ, ih, Nat.gcd_comm (b + 1) (a % (b + 1)), ← Nat.gcd_rec, Nat.gcd_comm]

/-- **Correctness and termination of Euclid's algorithm.**

`CS.euclid` is defined by a recursion whose measure (the second argument)
strictly decreases at every recursive call, hence it is a total function: the
algorithm terminates on every input.  Its value at `(a, b)` is a greatest
common divisor of `a` and `b`: it divides both arguments, every common divisor
of the arguments divides it, and it agrees with `Nat.gcd a b`. -/
theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
      euclid a b ∣ a ∧ euclid a b ∣ b ∧
        ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  have h := euclid_eq_gcd a b
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [h]; exact Nat.gcd_dvd_left a b
  · rw [h]; exact Nat.gcd_dvd_right a b
  · intro d hda hdb; rw [h]; exact Nat.dvd_gcd hda hdb

end CS

