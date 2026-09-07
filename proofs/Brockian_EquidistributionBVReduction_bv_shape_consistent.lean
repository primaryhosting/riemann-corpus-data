/-
  Brockian/EquidistributionBVReduction.lean — REDUCING THE EQUIDISTRIBUTION
  CONDITIONAL TO A NAMED HARDY–LITTLEWOOD / BOMBIERI–VINOGRADOV HYPOTHESIS.

  ## What is proved

  `Brockian.EquidistributionSchema` (namespace `Brockian.Equidistribution`) already
  turns the program's central overclaim — equidistribution of gap-`g` prime pairs
  across the `q−2` admissible residue configurations — into an honest conditional
  `equidistribution_of_asymptotic`. But its premise `PrimePairAsymptotic` bakes the
  UNIFORMITY into a single shared main term `C·main(N)/(q−2)`: every admissible class
  is ASSUMED to receive the identical constant. That hides exactly where equal
  distribution is being put in by hand, and it is a bespoke structure, not a named
  literature statement.

  This file replaces that premise with the NATURAL form of the analytic input — the
  Hardy–Littlewood asymptotic for prime pairs refined to arithmetic progressions
  mod `q` (the level-of-distribution / Bombieri–Vinogradov form of the correlation
  `∑_{p≤N} 1[p≡a] · 1[p+g prime]`): each admissible class `a` has its OWN singular-
  series constant `sing a`, and the real count obeys
        `configCount N q g a = sing a · main(N) + O(err a N)`,
  with `err a / main → 0` and `main → ∞`. The per-class constants are NOT assumed
  equal. This is `BVPrimePairAsymptotic` — a citable, Mathlib-absent, OPEN analytic
  statement, GENUINELY WEAKER than the earlier structure (that one is the special case
  `sing a = C/(q−2)`).

  The reductions proved (all algebra / limit work discharged; no assumed steps):

    * `configCount_density_of_BV` (conditional_rung=literature) — from
      `BVPrimePairAsymptotic` alone, EACH admissible class's density converges to its
      NORMALISED singular series:
          `configCount N q g a / totalConfigCount N q g → sing a / (∑_{b adm} sing b)`.
      This is the honest, uniformity-FREE content of Hardy–Littlewood in progressions:
      the limiting density is the class's SHARE of the singular series — whatever that
      share is. It does NOT collapse to `1/(q−2)` on its own.

    * `equidistribution_of_BV_uniform` (conditional_rung=literature) — adding the
      SINGULAR-SERIES SYMMETRY input `∀ a b admissible, sing a = sing b` (the standard
      fact that the local density at a prime `q` is the same on every admissible class),
      the normalised share collapses to exactly `1/(q−2)`, recovering equidistribution.
      The collapse uses the VERIFIED `card(admissibleResidues) = q−2`
      (`universal_admissibility_count`, reused) — the count enters as both the number
      of summands and the target density, so `1/(q−2)` is DERIVED, not restated.

    * `admissible_reflection_symmetry` (PROVED, UNCONDITIONAL) — the endpoint-swap
      reflection `a ↦ −g − a` (which exchanges the two forbidden residues `0` and `−g`)
      maps the admissible set to itself. A genuine, finite symmetry of the admissible
      configuration set. It is honest supporting structure for why the classes are
      interchangeable; it exhibits ONE symmetry and does NOT by itself establish the
      full uniformity of the singular series (see below).

    * `bv_shape_consistent` (PROVED) — the non-count field shapes of a UNIFORM
      `BVPrimePairAsymptotic` (a positive singular series constant on admissible
      classes, `main → ∞`, `err/main → 0`, and `sing` constant on admissible classes)
      are jointly satisfiable (`sing ≡ 1`, `main N = N+1`, `err ≡ 0`). Hence the
      hypothesis is not self-contradictory theater; only the tie of `sing·main` to the
      REAL prime-pair count is open.

  Genuineness (not modus-ponens theater): the hypothesis (`BVPrimePairAsymptotic`) is
  an asymptotic about ABSOLUTE counts against a growing main term with per-class
  singular-series constants; the conclusion of `configCount_density_of_BV` is a RATIO
  limit that is generally `sing a / ∑ sing b` and is NOT `1/(q−2)` unless the extra
  symmetry holds. The reduction is real proved content (per-class ratio limits, a
  finite-sum limit for the denominator, a quotient of limits, and the `q−2` collapse).

  ## What is NOT proved

    * Hardy–Littlewood / Bombieri–Vinogradov itself. No term of `BVPrimePairAsymptotic`
      is constructed for the real `configCount`; doing so is the OPEN analytic problem
      (the level-of-distribution statement for the pair correlation is not a theorem of
      Mathlib 4.32, and is not proved here).
    * The FULL uniformity of the singular series across all `q−2` admissible classes is
      taken as the cited hypothesis `huniform` in `equidistribution_of_BV_uniform`; it
      is NOT derived here. `admissible_reflection_symmetry` proves only the single
      endpoint-swap symmetry, not that all admissible classes carry equal local density.
    * Consequently this file is NEVER citable as a proof — conditional or otherwise — of
      prime-pair equidistribution. It moves the honesty rung of the reduction from OPEN
      (a bespoke, uniformity-baked structure) to LITERATURE (a specific named analytic
      hypothesis, with the uniformity isolated as its own cited symmetry input).

  Reuse (read-only): `Brockian.EquidistributionSchema` (`configCount`,
  `totalConfigCount`) and `Brockian.Admissibility` (`admissibleResidues`,
  `universal_admissibility_count`). Verified via AXLE @ lean-4.32.0.
-/
import Brockian.EquidistributionSchema

set_option autoImplicit false

open Finset Filter Topology
open Brockian.Admissibility
open Brockian.Equidistribution

namespace Brockian.EquidistributionBVReduction

/-! ### A ratio-asymptotic helper (genuine limit work)

If `M → ∞`, `E/M → 0`, and `|f − L·M| ≤ E` pointwise, then `f/M → L`. Reproved here
(the corresponding lemma in `EquidistributionSchema` is `private`); it is the analytic
core reused for both the per-class and total counts — a squeeze on
`f/M − L = (f − L·M)/M`, whose absolute value is `≤ E/M → 0`. -/
private lemma ratio_tendsto {f M E : ℕ → ℝ} {L : ℝ}
    (hM : Tendsto M atTop atTop)
    (hEM : Tendsto (fun N => E N / M N) atTop (nhds 0))
    (hbound : ∀ N, |f N - L * M N| ≤ E N) :
    Tendsto (fun N => f N / M N) atTop (nhds L) := by
  have hev : ∀ᶠ N in atTop, |f N / M N - L| ≤ E N / M N := by
    filter_upwards [hM.eventually_gt_atTop 0] with N hMpos
    have hrw : f N / M N - L = (f N - L * M N) / M N := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hMpos]
    gcongr
    exact hbound N
  have hzero : Tendsto (fun N => f N / M N - L) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hEM.neg) hEM
    · filter_upwards [hev] with N hN using (abs_le.mp hN).1
    · filter_upwards [hev] with N hN using (abs_le.mp hN).2
  have := hzero.add_const L
  simpa using this

/-! ### The named Hardy–Littlewood / Bombieri–Vinogradov hypothesis (per-class form)

Each admissible class carries its OWN singular-series constant `sing a`. No uniformity
is assumed. Constructing a term for the real `configCount` is the OPEN analytic input. -/

/-- **`BVPrimePairAsymptotic q g`** — the Hardy–Littlewood asymptotic for gap-`g`
prime pairs refined to arithmetic progressions mod `q` (Bombieri–Vinogradov /
level-of-distribution form). For each admissible class `a` it carries a positive
singular-series constant `sing a`, a shared main term `mainTerm(N) → ∞` (conceptually
`π(N)`), a per-class lower-order error, and the per-class asymptotic
`|configCount N q g a − sing a · mainTerm(N)| ≤ err a N`.

Crucially the constants `sing a` are NOT assumed equal across classes: this is the
natural analytic input, strictly WEAKER than the earlier `PrimePairAsymptotic` (which
is the special case `sing a = C/(q−2)`, a single shared constant). No instance is
built; that is the OPEN Hardy–Littlewood / Bombieri–Vinogradov content. -/
structure BVPrimePairAsymptotic (q : ℕ) [NeZero q] (g : ℕ) where
  /-- The per-class Hardy–Littlewood singular-series constant. -/
  sing : ZMod q → ℝ
  /-- The singular series is positive on every admissible class (singular-series
  positivity on admissible tuples). -/
  sing_pos : ∀ a ∈ admissibleResidues q (g : ZMod q), 0 < sing a
  /-- The shared main term (conceptually `π(N)`), tending to infinity. -/
  mainTerm : ℕ → ℝ
  /-- The main term grows without bound. -/
  mainTerm_tendsto : Tendsto mainTerm atTop atTop
  /-- The per-class error bar. -/
  err : ZMod q → ℕ → ℝ
  /-- Each class's error is lower order than the main term. -/
  err_lower_order : ∀ a ∈ admissibleResidues q (g : ZMod q),
    Tendsto (fun N => err a N / mainTerm N) atTop (nhds 0)
  /-- The gap is a genuine nonzero class (so there are exactly `q−2` admissible
  configurations). -/
  gap_ne : (g : ZMod q) ≠ 0
  /-- **The per-class Hardy–Littlewood asymptotic.** Each admissible class's real count
  is within its (lower-order) error of `sing a · mainTerm(N)`. -/
  count_asymptotic : ∀ a ∈ admissibleResidues q (g : ZMod q), ∀ N,
    |(configCount N q g a : ℝ) - sing a * mainTerm N| ≤ err a N

/-! ### Per-class and total ratios against the main term (genuine limit work) -/

/-- Each admissible class's count, normalised by the main term, converges to that
class's singular-series constant `sing a`. -/
lemma configCount_over_main_tendsto {q : ℕ} [NeZero q] {g : ℕ}
    (H : BVPrimePairAsymptotic q g) {a : ZMod q}
    (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    Tendsto (fun N => (configCount N q g a : ℝ) / H.mainTerm N) atTop (nhds (H.sing a)) := by
  apply ratio_tendsto H.mainTerm_tendsto (H.err_lower_order a ha)
  exact fun N => H.count_asymptotic a ha N

/-- The total admissible count, normalised by the main term, converges to the SUM of
the per-class singular-series constants. Proved as a finite sum of the per-class
limits (`tendsto_finset_sum`). -/
lemma total_over_main_tendsto {q : ℕ} [NeZero q] {g : ℕ}
    (H : BVPrimePairAsymptotic q g) :
    Tendsto (fun N => (totalConfigCount N q g : ℝ) / H.mainTerm N) atTop
      (nhds (∑ b ∈ admissibleResidues q (g : ZMod q), H.sing b)) := by
  have hrw : (fun N => (totalConfigCount N q g : ℝ) / H.mainTerm N)
      = (fun N => ∑ b ∈ admissibleResidues q (g : ZMod q),
          (configCount N q g b : ℝ) / H.mainTerm N) := by
    funext N
    unfold totalConfigCount
    rw [Nat.cast_sum, Finset.sum_div]
  rw [hrw]
  exact tendsto_finset_sum _ (fun b hb => configCount_over_main_tendsto H hb)

/-! ### The reduction: density = normalised singular series (rung LITERATURE) -/

/-- **`configCount_density_of_BV` — the honest reduction (conditional_rung=literature).**
From `BVPrimePairAsymptotic q g` and `q > 2`, each admissible class `a` has asymptotic
density equal to its NORMALISED singular series:

    `configCount N q g a / totalConfigCount N q g → sing a / (∑_{b adm} sing b)`.

This is the uniformity-free content of Hardy–Littlewood in progressions: the limiting
density is the class's SHARE of the singular series. It is NOT `1/(q−2)` in general —
that requires the singular-series symmetry (`equidistribution_of_BV_uniform`).

REAL WORK: per-class ratio limits (`configCount_over_main_tendsto`), a finite-sum limit
for the denominator (`total_over_main_tendsto`), and a quotient of limits with an
eventual rewrite `(f/M)/(g/M) = f/g`. RUNG: LITERATURE — as strong as its premise, the
OPEN Hardy–Littlewood / Bombieri–Vinogradov asymptotic. -/
theorem configCount_density_of_BV {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (H : BVPrimePairAsymptotic q g) {a : ZMod q}
    (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    Tendsto (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ)) atTop
      (nhds (H.sing a / ∑ b ∈ admissibleResidues q (g : ZMod q), H.sing b)) := by
  have hcard : (admissibleResidues q (g : ZMod q)).card = q - 2 :=
    universal_admissibility_count q (g : ZMod q) H.gap_ne
  have hne : (admissibleResidues q (g : ZMod q)).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hsum_pos : 0 < ∑ b ∈ admissibleResidues q (g : ZMod q), H.sing b :=
    Finset.sum_pos H.sing_pos hne
  have hnum := configCount_over_main_tendsto H ha
  have hden := total_over_main_tendsto H
  have hdiv := hnum.div hden (ne_of_gt hsum_pos)
  have heqf : (fun N => ((configCount N q g a : ℝ) / H.mainTerm N)
        / ((totalConfigCount N q g : ℝ) / H.mainTerm N))
      =ᶠ[atTop] (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ)) := by
    filter_upwards [H.mainTerm_tendsto.eventually_gt_atTop 0] with N hMpos
    have hMne : H.mainTerm N ≠ 0 := ne_of_gt hMpos
    rcases eq_or_ne ((totalConfigCount N q g : ℝ)) 0 with h0 | h0
    · simp [h0]
    · field_simp
  exact hdiv.congr' heqf

/-- **`equidistribution_of_BV_uniform` (conditional_rung=literature).** Adding the
singular-series SYMMETRY `∀ a b admissible, sing a = sing b` — the standard fact that
the local density at a prime `q` is uniform across the admissible classes — the
normalised share collapses to exactly `1/(q−2)`, recovering equidistribution.

The collapse uses `∑_{b adm} sing b = card · sing a = (q−2)·sing a` (via the VERIFIED
`card(admissibleResidues) = q−2`) and `sing a > 0`, so `sing a / ((q−2)·sing a) =
1/(q−2)`. The `q−2` count enters as both the number of summands and the target, so the
density is derived. RUNG: LITERATURE; the uniformity is the cited symmetry input, not
proved here. -/
theorem equidistribution_of_BV_uniform {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (H : BVPrimePairAsymptotic q g)
    (huniform : ∀ a ∈ admissibleResidues q (g : ZMod q),
      ∀ b ∈ admissibleResidues q (g : ZMod q), H.sing a = H.sing b)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    Tendsto (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ)) atTop
      (nhds (1 / ((q : ℝ) - 2))) := by
  have hcard : (admissibleResidues q (g : ZMod q)).card = q - 2 :=
    universal_admissibility_count q (g : ZMod q) H.gap_ne
  have hcardR : ((admissibleResidues q (g : ZMod q)).card : ℝ) = (q : ℝ) - 2 := by
    rw [hcard, Nat.cast_sub (by omega)]; norm_num
  have hsinga_pos : 0 < H.sing a := H.sing_pos a ha
  have hsum_eq : ∑ b ∈ admissibleResidues q (g : ZMod q), H.sing b
      = ((q : ℝ) - 2) * H.sing a := by
    have hstep : ∑ b ∈ admissibleResidues q (g : ZMod q), H.sing b
        = ∑ _b ∈ admissibleResidues q (g : ZMod q), H.sing a :=
      Finset.sum_congr rfl (fun b hb => huniform b hb a ha)
    rw [hstep, Finset.sum_const, nsmul_eq_mul, hcardR]
  have hval : H.sing a / (∑ b ∈ admissibleResidues q (g : ZMod q), H.sing b)
      = 1 / ((q : ℝ) - 2) := by
    rw [hsum_eq, mul_comm, div_mul_eq_div_div, div_self (ne_of_gt hsinga_pos)]
  rw [← hval]
  exact configCount_density_of_BV hq H ha

/-! ### A genuine symmetry of the admissible set (PROVED, UNCONDITIONAL) -/

/-- **`admissible_reflection_symmetry`.** The endpoint-swap reflection `a ↦ −g − a`
maps the admissible set to itself. It exchanges the two forbidden residues `0` and
`−g` (the reflection sends the start of a pair to the negation of its end), so it
preserves `admissibleResidues q g`. A finite, exact symmetry of the configuration set;
it exhibits ONE symmetry and does not, by itself, establish the full uniformity of the
singular series across all `q−2` classes (that is the cited hypothesis of
`equidistribution_of_BV_uniform`). -/
theorem admissible_reflection_symmetry {q : ℕ} [NeZero q] {g : ZMod q}
    {a : ZMod q} (ha : a ∈ admissibleResidues q g) :
    (-g - a) ∈ admissibleResidues q g := by
  rw [admissibleResidues, Finset.mem_sdiff] at ha ⊢
  obtain ⟨_, ha2⟩ := ha
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha2 ⊢
  obtain ⟨h0, hg⟩ := ha2
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro h
    exact hg (by linear_combination -h)
  · intro h
    exact h0 (by linear_combination -h)

/-! ### Non-vacuity of the uniform BV shape (PROVED) -/

/-- **`bv_shape_consistent`.** The non-count field shapes of a UNIFORM
`BVPrimePairAsymptotic` — a positive singular-series constant on admissible classes, a
main term tending to infinity, a lower-order error, and `sing` constant across
admissible classes — are jointly satisfiable (`sing ≡ 1`, `mainTerm N = N+1`,
`err ≡ 0`). Hence the hypothesis is not self-contradictory theater; the ONLY open
content is the tie of `sing · mainTerm` to the actual prime-pair count. NO instance of
the full structure is built (that would prove equidistribution). -/
theorem bv_shape_consistent {q : ℕ} [NeZero q] (g : ZMod q) :
    ∃ (sing : ZMod q → ℝ) (mainTerm err : ℕ → ℝ),
      (∀ a ∈ admissibleResidues q g, 0 < sing a) ∧
      Tendsto mainTerm atTop atTop ∧
      Tendsto (fun N => err N / mainTerm N) atTop (nhds 0) ∧
      (∀ a ∈ admissibleResidues q g, ∀ b ∈ admissibleResidues q g, sing a = sing b) := by
  refine ⟨fun _ => 1, (fun N => (N : ℝ) + 1), (fun _ => 0), ?_, ?_, ?_, ?_⟩
  · intro a _; exact one_pos
  · exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  · simp only [zero_div]; exact tendsto_const_nhds
  · intro a _ b _; rfl

end Brockian.EquidistributionBVReduction
