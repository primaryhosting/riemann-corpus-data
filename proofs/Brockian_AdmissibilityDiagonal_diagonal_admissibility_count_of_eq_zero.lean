/-
  Brockian/AdmissibilityDiagonal.lean — the divisible-case / diagonal law.

  Complements `Brockian.Admissibility.universal_admissibility_count`
  (which requires `g ≠ 0` and gives `|admissibleResidues q g| = q − 2`).
  When the gap is divisible by the modulus — i.e. `g = 0` in `ZMod q` —
  the two forbidden residues `{0, −g}` collapse to the singleton `{0}`,
  so exactly `q − 1` starts remain admissible.

  Together the two laws form the full dichotomy for the pair configuration
  count over any modulus `q ≥ 1`:

      |A_q(g)| = q − 1    if g ≡ 0 (mod q)
      |A_q(g)| = q − 2    if g ≢ 0 (mod q)

  Paper-audit target #4 (divisible-case diagonal law). Lane C #12.

  Verification (spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.Admissibility

open Finset
open Brockian.Admissibility

namespace Brockian.AdmissibilityDiagonal

/-- When the gap is `0`, the forbidden pair `{0, −g}` collapses to the singleton
`{0}`: the two coordinate hits coincide (diagonal / divisible case). -/
theorem admissibleResidues_zero_eq (q : ℕ) [NeZero q] :
    admissibleResidues q (0 : ZMod q) = (Finset.univ : Finset (ZMod q)) \ {0} := by
  unfold admissibleResidues
  simp only [neg_zero, insert_eq_of_mem (Finset.mem_singleton_self (0 : ZMod q))]

/-- **The divisible-case / diagonal law.** For any modulus `q ≥ 1` and gap
`g = 0` in `ZMod q` (equivalently `q ∣ g` in the integer lift), exactly
`q − 1` residues are admissible: only the zero class is forbidden. -/
theorem diagonal_admissibility_count (q : ℕ) [NeZero q] :
    (admissibleResidues q (0 : ZMod q)).card = q - 1 := by
  have hsing : ({0, -(0 : ZMod q)} : Finset (ZMod q)).card = 1 := by
    simp only [neg_zero, insert_eq_of_mem (Finset.mem_singleton_self (0 : ZMod q)),
      Finset.card_singleton]
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by
    rw [Finset.card_univ, ZMod.card]
  rw [admissibleResidues, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.univ_inter, hcard, hsing]

/-- Same law under an equality hypothesis `g = 0` (for rewriting under a
divisibility witness rather than at the literal zero gap). -/
theorem diagonal_admissibility_count_of_eq_zero (q : ℕ) [NeZero q]
    (g : ZMod q) (hg : g = 0) :
    (admissibleResidues q g).card = q - 1 := by
  subst hg
  exact diagonal_admissibility_count q

/-- **Full dichotomy for the pair configuration count.** Complements
`universal_admissibility_count` (`g ≠ 0` ⇒ `q − 2`) with the diagonal case
(`g = 0` ⇒ `q − 1`). Exactly one of the two branches holds. -/
theorem admissibility_count_dichotomy (q : ℕ) [NeZero q] (g : ZMod q) :
    (admissibleResidues q g).card = if g = 0 then q - 1 else q - 2 := by
  split_ifs with hg
  · exact diagonal_admissibility_count_of_eq_zero q g hg
  · exact universal_admissibility_count q g hg

/-- Corollary: mod 3, a zero gap leaves `3 − 1 = 2` admissible residues
(complement of the twin-prime non-zero count of 1). -/
theorem diagonal_count_three :
    (admissibleResidues 3 (0 : ZMod 3)).card = 2 := by
  simpa using diagonal_admissibility_count 3

/-- Corollary: mod 5, a zero gap leaves `5 − 1 = 4` admissible residues
(complement of the Brockian non-zero count of 3). -/
theorem diagonal_count_five :
    (admissibleResidues 5 (0 : ZMod 5)).card = 4 := by
  simpa using diagonal_admissibility_count 5

end Brockian.AdmissibilityDiagonal
