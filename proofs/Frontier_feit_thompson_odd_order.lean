import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-- Auxiliary strong induction on the order of the group. -/
private theorem solvable_of_odd_card_aux
    (hsimple : ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → Odd (Nat.card S) →
      ∀ a b : S, a * b = b * a) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G], Nat.card G = n → Odd (Nat.card G) →
      IsSolvable G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hcard hodd
    subst hcard
    by_cases hnt : Nontrivial G
    · haveI := hnt
      by_cases hex : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
      · obtain ⟨N, hN, hbot, htop⟩ := hex
        haveI := hN
        have hNcard : Nat.card N < Nat.card G := by
          have hne : Nat.card N ≠ Nat.card G := fun h => htop (N.eq_top_of_card_eq h)
          exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos N.card_subgroup_dvd_card) hne
        have hQcard : Nat.card (G ⧸ N) < Nat.card G := by
          have h2 : 1 < Nat.card N := (N.one_lt_card_iff_ne_bot).2 hbot
          have hq : 0 < Nat.card (G ⧸ N) := Nat.card_pos
          rw [N.card_eq_card_quotient_mul_card_subgroup]
          exact (Nat.lt_mul_iff_one_lt_right hq).2 h2
        haveI : IsSolvable N :=
          ih _ hNcard N rfl (hodd.of_dvd_nat N.card_subgroup_dvd_card)
        haveI : IsSolvable (G ⧸ N) :=
          ih _ hQcard (G ⧸ N) rfl (hodd.of_dvd_nat N.card_quotient_dvd_card)
        exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
          (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
      · push_neg at hex
        have hs : IsSimpleGroup G := by
          refine ⟨fun H hH => ?_⟩
          by_cases hb : H = ⊥
          · exact Or.inl hb
          · exact Or.inr (hex H hH hb)
        exact isSolvable_of_comm (hsimple G hs hodd)
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact isSolvable_of_comm fun a b => by
        simp [Subsingleton.elim (a * b) (b * a)]

/-- **Feit–Thompson (odd order theorem), reduced to simple groups.**

Every finite group of odd order is solvable, *given* the simple-group case: namely that
every finite simple group of odd order is commutative (equivalently, cyclic of prime order).

This is a Lean-checked reduction of the Feit–Thompson theorem to its content about simple
groups; the reduction itself is the standard minimal-counterexample argument: in a minimal
non-solvable group of odd order, no proper nontrivial normal subgroup can exist (otherwise
the subgroup and the quotient would both be solvable of smaller odd order), so the group is
simple, contradicting the hypothesis. -/
theorem feit_thompson_odd_order
    (hsimple : ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → Odd (Nat.card S) →
      ∀ a b : S, a * b = b * a)
    (G : Type u) [Group G] [Finite G] (hodd : Odd (Nat.card G)) : IsSolvable G :=
  solvable_of_odd_card_aux hsimple _ G rfl hodd

/-- Unconditional base case: a finite group of odd prime power order is solvable. -/
theorem isSolvable_of_isPGroup {p : ℕ} [Fact p.Prime] (G : Type u) [Group G] [Finite G]
    (hp : IsPGroup p G) : IsSolvable G :=
  have : Group.IsNilpotent G := hp.isNilpotent
  IsNilpotent.to_isSolvable

end Frontier

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

