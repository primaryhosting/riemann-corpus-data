/-
  Brockian/AdmissibilityCRT.lean — the CRT composite-modulus admissibility count.

  Extends the verified prime-modulus law
  (`Brockian.Admissibility.universal_admissibility_count`, giving
  `|admissibleResidues q g| = q − 2` for `g ≠ 0`) to a COMPOSITE modulus `q1 · q2`
  with `q1, q2` coprime, via the Chinese Remainder ring isomorphism
  `ZMod.chineseRemainder : ZMod (q1 * q2) ≃+* ZMod q1 × ZMod q2`.

  KEY RESULT (`admissibleResidues_crt_card`): admissibility over `ZMod (q1 · q2)` is
  per-modulus-independent. A start `a` is admissible mod `q1 · q2` iff its residue
  mod `q1` is admissible for the gap `g1 = g mod q1` AND its residue mod `q2` is
  admissible for `g2 = g mod q2`. Under the CRT bijection this set is the CRT image of
  the product `admissibleResidues q1 g1 ×ˢ admissibleResidues q2 g2`, so the count is
  the PRODUCT of the per-modulus counts:

      |A_{q1·q2}(g)| = |A_{q1}(g1)| · |A_{q2}(g2)|

  with NO extra correction factor.

  ─────────────────────────────────────────────────────────────────────────────
  CORRECTION TO PAPER 1 (`Paper_BV_Final.pdf §6.1`) — SUSPECT FORMULA REFUTED.

  Paper 1 §6.1 asserts a composite count that carries an extra correction factor

      (q1·q2 − 1) / ((q1 − 1)(q2 − 1)).

  That factor is WRONG. The corollary `admissibleResidues_crt_card_two_primes` proves
  that for two DISTINCT primes `p, q` (with `p ∤ g`, `q ∤ g`) the correct count is
  exactly the clean product

      |A_{p·q}(g)| = (p − 2)·(q − 2),

  the CRT product of the two prime-modulus counts, with NO correction factor.

  Concrete refutation (p = 3, q = 5): the correct count is (3−2)·(5−2) = 1·3 = 3
  (anchored by kernel `decide` in `admissible_count_three_five` below). Paper 1's factor
  would multiply this by (15−1)/((3−1)(5−1)) = 14/8 = 1.75, yielding a NON-INTEGER
  "count" of 5.25 — impossible for a cardinality, exposing the formula as spurious.
  ─────────────────────────────────────────────────────────────────────────────

  Verification (spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.Admissibility

open Finset

namespace Brockian.Admissibility.CRT

/-- **CRT composite-modulus admissibility count.** For coprime moduli `q1, q2` and gaps
`g1 : ZMod q1`, `g2 : ZMod q2`, the number of starts `a : ZMod (q1 * q2)` whose CRT
residues `(a mod q1, a mod q2)` are BOTH admissible (for `g1` resp. `g2`) equals the
product of the per-modulus admissible counts. Admissibility factors across coprime
moduli — the count multiplies, with no extra correction factor. -/
theorem admissibleResidues_crt_card
    (q1 q2 : ℕ) [NeZero q1] [NeZero q2] (h : Nat.Coprime q1 q2)
    (g1 : ZMod q1) (g2 : ZMod q2) :
    (Finset.univ.filter (fun a : ZMod (q1 * q2) =>
        ((ZMod.chineseRemainder h) a).1 ∈ admissibleResidues q1 g1 ∧
        ((ZMod.chineseRemainder h) a).2 ∈ admissibleResidues q2 g2)).card
      = (admissibleResidues q1 g1).card * (admissibleResidues q2 g2).card := by
  classical
  set e := ZMod.chineseRemainder h with he
  set P : Finset (ZMod q1 × ZMod q2) :=
    admissibleResidues q1 g1 ×ˢ admissibleResidues q2 g2 with hP
  -- The filtered admissible set over the composite is the CRT image of the product set.
  have hset :
      (Finset.univ.filter (fun a : ZMod (q1 * q2) =>
          (e a).1 ∈ admissibleResidues q1 g1 ∧ (e a).2 ∈ admissibleResidues q2 g2))
        = P.image (fun p => e.symm p) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hP,
      Finset.mem_product]
    constructor
    · intro ha
      exact ⟨e a, ha, e.symm_apply_apply a⟩
    · rintro ⟨b, hb, hba⟩
      have hea : e a = b := by rw [← hba, e.apply_symm_apply]
      rw [hea]; exact hb
  rw [hset, Finset.card_image_of_injective _ e.symm.injective, hP, Finset.card_product]

/-- **Corollary — two distinct primes, and the correction of Paper 1 §6.1.** For two
distinct primes `p, q` and gaps not divisible by them (`g1 ≠ 0`, `g2 ≠ 0`), the composite
admissibility count is exactly the clean CRT product `(p − 2)·(q − 2)`.

This CONTRADICTS Paper 1 §6.1, which inserts a spurious correction factor
`(p·q − 1)/((p − 1)(q − 1))`. There is no such factor: admissibility is per-modulus
independent, so the count is simply the product of the prime-modulus counts. -/
theorem admissibleResidues_crt_card_two_primes
    (p q : ℕ) [NeZero p] [NeZero q] (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (g1 : ZMod p) (g2 : ZMod q) (hg1 : g1 ≠ 0) (hg2 : g2 ≠ 0) :
    (Finset.univ.filter (fun a : ZMod (p * q) =>
        ((ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq)) a).1
            ∈ admissibleResidues p g1 ∧
        ((ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq)) a).2
            ∈ admissibleResidues q g2)).card
      = (p - 2) * (q - 2) := by
  rw [admissibleResidues_crt_card p q ((Nat.coprime_primes hp hq).mpr hpq) g1 g2,
    universal_admissibility_count p g1 hg1, universal_admissibility_count q g2 hg2]

/-- **COMPUTATION (kernel `decide`, small moduli).** Concrete anchor for the correction:
mod 3 there is `3 − 2 = 1` admissible residue and mod 5 there are `5 − 2 = 3`, so the
composite count for `p = 3, q = 5` is `1 · 3 = 3` — a plain integer. Paper 1 §6.1's factor
`(15−1)/((3−1)(5−1)) = 14/8` would turn this into `5.25`, a non-integer, which no
cardinality can be. -/
theorem admissible_count_three_five :
    (admissibleResidues 3 (1 : ZMod 3)).card * (admissibleResidues 5 (1 : ZMod 5)).card = 3 := by
  decide

end Brockian.Admissibility.CRT
