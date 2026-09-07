/-
  Brockian/AdmissibilityCriterionScaffold.lean

  Finite local scaffold for the Hardy-Littlewood admissibility criterion.

  This module proves the local, finite statement behind the slogan

      "a tuple has no obstruction modulo q iff ν(q) < q".

  Here `ν(q)` is the number of distinct occupied residue classes modulo `q`.
  The global criterion for integer tuples is only the prime-quantified wrapper
  over these local facts.  No prime distribution, sieve asymptotic, or global
  representation theorem is asserted here.
-/
import Brockian.AdmissibilityKTuple

set_option autoImplicit false

open Finset
open Brockian.AdmissibilityKTuple

namespace Brockian.Admissibility.CriterionScaffold

variable {q : ℕ}

/-- Finite local admissibility for a residue tuple `H ⊆ ZMod q`: there is a start
residue avoiding every forbidden shifted zero. -/
def LocalTupleAdmissible (q : ℕ) [NeZero q] (H : Finset (ZMod q)) : Prop :=
  ∃ a : ZMod q, a ∈ admissibleTupleResidues q H

/-- The occupied residue classes of an integer tuple modulo `q`. -/
def localResidueSet (q : ℕ) (G : Finset ℕ) : Finset (ZMod q) :=
  G.image (fun n : ℕ => (n : ZMod q))

/-- The finite local obstruction count `ν(q)`: the number of distinct occupied
residue classes modulo `q`. -/
def localNu (q : ℕ) (G : Finset ℕ) : ℕ :=
  (localResidueSet q G).card

/-- Finite local admissibility for an integer tuple modulo `q`, expressed through
its occupied residue classes in `ZMod q`. -/
def LocalIntegerTupleAdmissible (q : ℕ) [NeZero q] (G : Finset ℕ) : Prop :=
  LocalTupleAdmissible q (localResidueSet q G)

/-- The global Hardy-Littlewood local-admissibility condition is just the
prime-quantified form of the finite obstruction inequality.  This is a definition,
not an asymptotic theorem. -/
def PrimeLocalAdmissible (G : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → localNu p G < p

/-- Local admissibility means exactly that some start avoids all shifted zeros. -/
theorem localTupleAdmissible_iff_exists_avoids (H : Finset (ZMod q)) [NeZero q] :
    LocalTupleAdmissible q H ↔ ∃ a : ZMod q, ∀ h ∈ H, a + h ≠ 0 := by
  unfold LocalTupleAdmissible
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (mem_admissibleTupleResidues H a).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (mem_admissibleTupleResidues H a).mpr ha⟩

/-- Any finite set of residues in `ZMod q` has at most `q` elements. -/
theorem residueSet_card_le_modulus (H : Finset (ZMod q)) [NeZero q] :
    H.card ≤ q := by
  calc
    H.card ≤ Fintype.card (ZMod q) := Finset.card_le_univ H
    _ = q := ZMod.card q

/-- The finite local admissibility criterion: a residue tuple has an admissible
start modulo `q` iff its obstruction count is strictly smaller than `q`. -/
theorem localTupleAdmissible_iff_obstruction_lt (H : Finset (ZMod q)) [NeZero q] :
    LocalTupleAdmissible q H ↔ H.card < q := by
  unfold LocalTupleAdmissible
  change (admissibleTupleResidues q H).Nonempty ↔ H.card < q
  rw [← Finset.card_pos, admissibleTupleResidues_card]
  omega

/-- Equivalent obstruction form: there is no local admissible start iff the tuple
occupies all residue classes modulo `q`. -/
theorem not_localTupleAdmissible_iff_modulus_le_obstruction
    (H : Finset (ZMod q)) [NeZero q] :
    ¬ LocalTupleAdmissible q H ↔ q ≤ H.card := by
  rw [localTupleAdmissible_iff_obstruction_lt]
  omega

/-- Since the obstruction count is bounded above by `q`, the obstructed case is
equivalent to exact residue-class coverage. -/
theorem not_localTupleAdmissible_iff_obstruction_eq_modulus
    (H : Finset (ZMod q)) [NeZero q] :
    ¬ LocalTupleAdmissible q H ↔ H.card = q := by
  rw [not_localTupleAdmissible_iff_modulus_le_obstruction]
  constructor
  · intro h
    exact le_antisymm (residueSet_card_le_modulus H) h
  · intro h
    rw [h]

@[simp] theorem localNu_eq_card_localResidueSet (q : ℕ) (G : Finset ℕ) :
    localNu q G = (localResidueSet q G).card := rfl

/-- Integer-tuple version of the finite local criterion:
an integer tuple has an admissible start modulo `q` iff its local `ν(q)` is `< q`. -/
theorem localIntegerTupleAdmissible_iff_localNu_lt
    (q : ℕ) [NeZero q] (G : Finset ℕ) :
    LocalIntegerTupleAdmissible q G ↔ localNu q G < q := by
  unfold LocalIntegerTupleAdmissible localNu
  exact localTupleAdmissible_iff_obstruction_lt (localResidueSet q G)

/-- The global prime-local condition is faithfully equivalent to requiring a
finite local admissible start at every prime modulus.  The remaining global step
in the full Hardy-Littlewood criterion is precisely this prime quantifier; this
theorem does not assert any prime-pair distribution. -/
theorem primeLocalAdmissible_iff_every_prime_has_local_start (G : Finset ℕ) :
    PrimeLocalAdmissible G ↔
      ∀ p : ℕ, ∀ hp : Nat.Prime p,
        letI : NeZero p := ⟨hp.ne_zero⟩
        LocalIntegerTupleAdmissible p G := by
  constructor
  · intro h p hp
    letI : NeZero p := ⟨hp.ne_zero⟩
    rw [localIntegerTupleAdmissible_iff_localNu_lt]
    exact h p hp
  · intro h p hp
    letI : NeZero p := ⟨hp.ne_zero⟩
    have hlocal : LocalIntegerTupleAdmissible p G := h p hp
    rwa [localIntegerTupleAdmissible_iff_localNu_lt] at hlocal

end Brockian.Admissibility.CriterionScaffold
