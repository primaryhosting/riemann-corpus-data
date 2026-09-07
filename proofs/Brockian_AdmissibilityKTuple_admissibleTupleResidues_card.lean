/-
  Brockian/AdmissibilityKTuple.lean — the general admissible k-tuple configuration count.

  Roadmap #14. Generalizes `Brockian.Admissibility.universal_admissibility_count`
  (the single-gap / k = 2 case, giving `q − 2`) to an arbitrary k-tuple of coordinate
  offsets `H : Finset (ZMod q)`, and lifts the count across a composite modulus via CRT.

  SET-UP. A k-tuple pattern is a finite set of coordinate offsets `H ⊆ ZMod q`
  (for a pair with gap `g` this is `H = {0, g}`). A start residue `a : ZMod q` is
  *admissible for `H`* iff none of the shifted coordinates lands on `0`, i.e.
  `a + h ≠ 0` for every `h ∈ H`. Equivalently `a ∉ {−h : h ∈ H}`, so the admissible
  set is `univ \ H.image (· ↦ −·)`.

  ─────────────────────────────────────────────────────────────────────────────
  CORRECTION TO THE PAPER. The paper's superseded guess for the k-tuple
  configuration count over a prime modulus was `(q − 1)^(k−1)`. That is WRONG. The
  forbidden classes are the `k` negated offsets `{−h : h ∈ H}`; since negation is a
  bijection of `ZMod q`, the number of DISTINCT forbidden residues is exactly
  `ν := |H|` (the number of distinct offsets), and complement-counting gives the clean

      |A_q(H)| = q − |H|         (`admissibleTupleResidues_card`).

  There is no exponent and no `(q − 1)` base: the count is linear in `q`, not a power.
  Over a composite modulus `q1·q2` (coprime) the CRT bijection makes admissibility
  per-modulus independent, so the counts MULTIPLY:

      |A_{q1·q2}(H1, H2)| = (q1 − |H1|)·(q2 − |H2|)   (`admissibleTupleResidues_crt_card`).

  This subsumes the single-gap CRT law of `Brockian.Admissibility.CRT` (recovered by
  `admissibleTupleResidues_crt_card_pair`, which reuses that module's theorem).
  ─────────────────────────────────────────────────────────────────────────────

  ## What is proved (general, closed by reasoning — PROVED register)
  * `mem_admissibleTupleResidues` — the admissible set means exactly `∀ h ∈ H, a + h ≠ 0`
    (guards against a vacuous definition).
  * `admissibleTupleResidues_card` — over any `ZMod q`, the count is `q − |H|`
    for ANY finite offset set `H` (arbitrary k). No `native_decide`, no `decide`.
  * `admissibleTupleResidues_pair_eq` / `admissibleTupleResidues_card_pair` —
    specialization to the pair `H = {0, g}` recovers `univ \ {0, −g}` and the core's
    `q − 2` (reusing `universal_admissibility_count`).
  * `admissibleTupleResidues_card_triple` — the k = 3 count `q − 3` for a genuine
    triple `{0, g₁, g₂}` with `0, g₁, g₂` pairwise distinct.
  * `crt_filter_card` — a generic CRT product-count for arbitrary Finset predicates
    across coprime factors (generalizes `Brockian.Admissibility.CRT.admissibleResidues_crt_card`).
  * `admissibleTupleResidues_crt_card` — the composite-modulus k-tuple count
    `(q1 − |H1|)·(q2 − |H2|)`.
  * `admissibleTupleResidues_crt_card_pair` — bridge: the k-tuple CRT count for
    the pair case reproduces the single-gap CRT law of `Brockian.Admissibility.CRT`.

  ## What is proved (numeric, kernel `decide` — COMPUTATION register)
  * `admissible_ktuple_count_three` — mod 3, pattern `{0,1}`, count `1` (= 3 − 2).
  * `admissible_ktuple_count_five` — mod 5, triple `{0,1,3}`, count `2` (= 5 − 3).

  ## What is NOT proved
  * The Hardy–Littlewood *admissibility criterion* itself (a tuple is admissible iff
    for every prime `p` the offsets miss some residue, `ν(p) < p`) — only the
    per-modulus configuration COUNT `q − |H|` is proved here, not the sieve criterion.
  * Only a 2-factor CRT lift is given. The iterated lift to a product of arbitrarily
    many coprime prime powers (`∏ (pᵢ − νᵢ)`) is not formalized in this module.
  * No singular-series constant, density, or asymptotic conclusion is drawn from the
    count; this is exact finite counting only.

  Verification (spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean; the two
      `decide` lemmas are the only COMPUTATION-register facts and are flagged above)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.Admissibility
import Brockian.AdmissibilityCRT

open Finset
open Brockian.Admissibility

namespace Brockian.AdmissibilityKTuple

variable {q : ℕ} [NeZero q]

/-- Admissible start residues mod `q` for a k-tuple of coordinate offsets `H`:
a start `a : ZMod q` is admissible iff `a + h ≠ 0` for every offset `h ∈ H`, i.e.
`a` avoids every negated offset. The admissible set is `univ` minus the negated
offsets `{−h : h ∈ H}`. For `H = {0, g}` this is the pair set `univ \ {0, −g}`. -/
def admissibleTupleResidues (q : ℕ) [NeZero q] (H : Finset (ZMod q)) : Finset (ZMod q) :=
  (Finset.univ : Finset (ZMod q)) \ H.image (fun h => -h)

/-- The admissible set means exactly what it should: no shifted coordinate hits `0`.
This rules out any vacuous/degenerate reading of the definition. -/
theorem mem_admissibleTupleResidues (H : Finset (ZMod q)) (a : ZMod q) :
    a ∈ admissibleTupleResidues q H ↔ ∀ h ∈ H, a + h ≠ 0 := by
  rw [admissibleTupleResidues, Finset.mem_sdiff]
  constructor
  · rintro ⟨-, hna⟩ h hh hz
    exact hna (Finset.mem_image.mpr ⟨h, hh, (eq_neg_iff_add_eq_zero.mpr hz).symm⟩)
  · intro ha
    refine ⟨Finset.mem_univ _, fun hmem => ?_⟩
    obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp hmem
    exact ha h hh (eq_neg_iff_add_eq_zero.mp heq.symm)

/-- **The general admissible k-tuple configuration count.** For ANY finite offset set
`H : Finset (ZMod q)` (any k), the number of admissible start residues over `ZMod q` is
`q − |H|`. The negated offsets are `|H|` distinct forbidden classes (negation is a
bijection), so complement-counting is exact — refuting the paper's `(q − 1)^(k−1)`
guess: the count is linear in `q`, with no exponent. -/
theorem admissibleTupleResidues_card (H : Finset (ZMod q)) :
    (admissibleTupleResidues q H).card = q - H.card := by
  have himg : (H.image (fun h => -h)).card = H.card :=
    Finset.card_image_of_injective H neg_injective
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by
    rw [Finset.card_univ, ZMod.card]
  rw [admissibleTupleResidues, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.univ_inter, hcard, himg]

/-- The pair tuple `H = {0, g}` reproduces the core module's single-gap admissible set
`univ \ {0, −g}` verbatim. -/
theorem admissibleTupleResidues_pair_eq (g : ZMod q) :
    admissibleTupleResidues q ({0, g} : Finset (ZMod q)) = admissibleResidues q g := by
  unfold admissibleTupleResidues admissibleResidues
  congr 1
  rw [Finset.image_insert, Finset.image_singleton, neg_zero]

/-- Specialization to k = 2: the pair `{0, g}` with `g ≠ 0` gives the core `q − 2`,
recovering `Brockian.Admissibility.universal_admissibility_count` through the tuple form. -/
theorem admissibleTupleResidues_card_pair (g : ZMod q) (hg : g ≠ 0) :
    (admissibleTupleResidues q ({0, g} : Finset (ZMod q))).card = q - 2 := by
  rw [admissibleTupleResidues_pair_eq]
  exact universal_admissibility_count q g hg

/-- Specialization to k = 3: a genuine triple `{0, g₁, g₂}` with `0, g₁, g₂` pairwise
distinct has exactly `q − 3` admissible start residues. -/
theorem admissibleTupleResidues_card_triple (g₁ g₂ : ZMod q)
    (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) (h₁₂ : g₁ ≠ g₂) :
    (admissibleTupleResidues q ({0, g₁, g₂} : Finset (ZMod q))).card = q - 3 := by
  rw [admissibleTupleResidues_card]
  have hm1 : g₁ ∉ ({g₂} : Finset (ZMod q)) := by
    simp only [Finset.mem_singleton]; exact h₁₂
  have hm0 : (0 : ZMod q) ∉ ({g₁, g₂} : Finset (ZMod q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm h₁, Ne.symm h₂⟩
  have hc : ({0, g₁, g₂} : Finset (ZMod q)).card = 3 := by
    rw [Finset.card_insert_of_notMem hm0, Finset.card_insert_of_notMem hm1,
      Finset.card_singleton]
  rw [hc]

/-- **COMPUTATION (kernel `decide`).** Mod 3, the pair pattern `{0, 1}` leaves exactly
`1 = 3 − 2` admissible residue — the twin-prime constraint, in tuple form. -/
theorem admissible_ktuple_count_three :
    (admissibleTupleResidues 3 ({0, 1} : Finset (ZMod 3))).card = 1 := by decide

/-- **COMPUTATION (kernel `decide`).** Mod 5, the triple pattern `{0, 1, 3}` leaves
exactly `2 = 5 − 3` admissible residues (concrete k = 3 case; refutes any `(q−1)^(k−1)`
reading, which would give `4^2 = 16`). -/
theorem admissible_ktuple_count_five :
    (admissibleTupleResidues 5 ({0, 1, 3} : Finset (ZMod 5))).card = 2 := by decide

/-- **Generic CRT product-count.** For coprime moduli `q1, q2` and ARBITRARY residue
sets `S1 ⊆ ZMod q1`, `S2 ⊆ ZMod q2`, the number of `a : ZMod (q1·q2)` whose CRT
components lie in `S1` resp. `S2` is `|S1|·|S2|`. Generalizes
`Brockian.Admissibility.CRT.admissibleResidues_crt_card` (which fixes `S1, S2` to be
single-gap admissible sets) to arbitrary configuration sets, hence to k-tuples. -/
theorem crt_filter_card
    (q1 q2 : ℕ) [NeZero q1] [NeZero q2] (h : Nat.Coprime q1 q2)
    (S1 : Finset (ZMod q1)) (S2 : Finset (ZMod q2)) :
    (Finset.univ.filter (fun a : ZMod (q1 * q2) =>
        ((ZMod.chineseRemainder h) a).1 ∈ S1 ∧
        ((ZMod.chineseRemainder h) a).2 ∈ S2)).card
      = S1.card * S2.card := by
  classical
  set e := ZMod.chineseRemainder h with he
  set P : Finset (ZMod q1 × ZMod q2) := S1 ×ˢ S2 with hP
  have hset :
      (Finset.univ.filter (fun a : ZMod (q1 * q2) =>
          (e a).1 ∈ S1 ∧ (e a).2 ∈ S2))
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

/-- **CRT composite-modulus k-tuple count.** For coprime `q1, q2` and offset sets
`H1, H2`, the number of starts `a : ZMod (q1·q2)` admissible per-coordinate for both
patterns is the product `(q1 − |H1|)·(q2 − |H2|)` — no correction factor. This is the
k-tuple case the single-gap CRT module does not cover. -/
theorem admissibleTupleResidues_crt_card
    (q1 q2 : ℕ) [NeZero q1] [NeZero q2] (h : Nat.Coprime q1 q2)
    (H1 : Finset (ZMod q1)) (H2 : Finset (ZMod q2)) :
    (Finset.univ.filter (fun a : ZMod (q1 * q2) =>
        ((ZMod.chineseRemainder h) a).1 ∈ admissibleTupleResidues q1 H1 ∧
        ((ZMod.chineseRemainder h) a).2 ∈ admissibleTupleResidues q2 H2)).card
      = (q1 - H1.card) * (q2 - H2.card) := by
  rw [crt_filter_card q1 q2 h, admissibleTupleResidues_card, admissibleTupleResidues_card]

/-- **Bridge to `Brockian.Admissibility.CRT`.** For the pair patterns `{0, g1}`, `{0, g2}`
the k-tuple CRT count coincides with the single-gap CRT law
`admissibleResidues_crt_card`, reusing that module's theorem directly. This shows the
tuple framework subsumes the earlier single-gap CRT result rather than duplicating it. -/
theorem admissibleTupleResidues_crt_card_pair
    (q1 q2 : ℕ) [NeZero q1] [NeZero q2] (h : Nat.Coprime q1 q2)
    (g1 : ZMod q1) (g2 : ZMod q2) :
    (Finset.univ.filter (fun a : ZMod (q1 * q2) =>
        ((ZMod.chineseRemainder h) a).1 ∈ admissibleTupleResidues q1 ({0, g1} : Finset (ZMod q1)) ∧
        ((ZMod.chineseRemainder h) a).2 ∈ admissibleTupleResidues q2 ({0, g2} : Finset (ZMod q2)))).card
      = (admissibleResidues q1 g1).card * (admissibleResidues q2 g2).card := by
  simp only [admissibleTupleResidues_pair_eq]
  exact Brockian.Admissibility.CRT.admissibleResidues_crt_card q1 q2 h g1 g2

end Brockian.AdmissibilityKTuple
