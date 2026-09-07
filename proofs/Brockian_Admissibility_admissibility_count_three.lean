/-
  Brockian/Admissibility.lean — the q−ν admissibility law.

  Canonical, citation-grade form of the intake ledger's run 74 / run 119 module 2:
  over `ZMod q`, the admissible start residues for a gap `g` are `univ \ {0, -g}`, and
  for `g ≠ 0` there are exactly `q - 2` of them. Corollaries q = 3 (twin-prime
  constraint: 1 residue) and q = 5 (the Brockian case: 3 residues).

  Verification (spec §2A triple verification):
    - local `lake build`  : pending (see PORT-QUEUE.md if not yet green)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0

  Ledger provenance: runs 74 (a0ce…, 71-line ZMod-native), 49, 105 (independent
  replications); quarantine-side per the run-119 register boundary.
-/
import Mathlib

open Finset

namespace Brockian.Admissibility

/-- Admissible residues mod `q` for a gap `g`: a start `a : ZMod q` is admissible
iff neither `a` nor `a + g` is `≡ 0`, i.e. `a ∉ {0, -g}`. -/
def admissibleResidues (q : ℕ) [NeZero q] (g : ZMod q) : Finset (ZMod q) :=
  (Finset.univ : Finset (ZMod q)) \ {0, -g}

/-- **The q−ν law (distinct-gap / k = 2 case).** For any modulus `q ≥ 1` and gap
`g ≠ 0`, exactly `q - 2` residues are admissible. For prime `q` this counts the
admissible prime-pair start residues; the arithmetic interpretation specializes at
`q = 3` and `q = 5` below. -/
theorem universal_admissibility_count (q : ℕ) [NeZero q]
    (g : ZMod q) (hg : g ≠ 0) :
    (admissibleResidues q g).card = q - 2 := by
  have hpair : ({0, -g} : Finset (ZMod q)).card = 2 :=
    Finset.card_pair (by
      intro h
      exact hg (neg_eq_zero.mp h.symm))
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by
    rw [Finset.card_univ, ZMod.card]
  rw [admissibleResidues, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.univ_inter, hcard, hpair]

/-- Corollary: the twin-prime constraint mod 3 leaves exactly one admissible residue. -/
theorem admissibility_count_three (g : ZMod 3) (hg : g ≠ 0) :
    (admissibleResidues 3 g).card = 1 := by
  simpa using universal_admissibility_count 3 g hg

/-- Corollary (**the Brockian case**): mod 5 leaves exactly three admissible residues. -/
theorem admissibility_count_five (g : ZMod 5) (hg : g ≠ 0) :
    (admissibleResidues 5 g).card = 3 := by
  simpa using universal_admissibility_count 5 g hg

end Brockian.Admissibility
