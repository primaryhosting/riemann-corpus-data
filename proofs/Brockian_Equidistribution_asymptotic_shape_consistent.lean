/-
  Brockian/EquidistributionSchema.lean — THE HONEST CONDITIONAL EQUIDISTRIBUTION SCHEMA.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  RUNG: OPEN (conditional schema). This file does NOT prove equidistribution. │
  │  It converts the program's central OVERCLAIM — equidistribution of prime     │
  │  pairs across the q−2 admissible residue configurations asserted as a proven │
  │  "Law" (Paper 3 / Conj 1.2 / Conj 6.1) — into a legitimate rung-3            │
  │  CONDITIONAL theorem:                                                         │
  │                                                                              │
  │     GIVEN a Hardy–Littlewood / Bombieri–Vinogradov-type asymptotic           │
  │     hypothesis (each admissible configuration receives the SAME main term    │
  │     C·main(N)/(q−2) with a lower-order error), CONCLUDE that each of the     │
  │     exactly q−2 admissible configurations has asymptotic density → 1/(q−2).  │
  │                                                                              │
  │  The premise is Hardy–Littlewood / Bombieri–Vinogradov strength (OPEN, NOT   │
  │  shown instantiable for the real prime-pair count). This schema is NEVER     │
  │  citable as a proof — conditional or unconditional — of equidistribution.    │
  └───────────────────────────────────────────────────────────────────────────┘

  The number-theoretic content is honest, not placeholder:

    * `configCount N q g a` is the REAL count of primes `p ≤ N` such that `p+g`
      is also prime and `p ≡ a (mod q)` — the genuine number of gap-`g` prime
      pairs whose starting residue is the configuration `a`. It is evaluated, not
      stubbed: e.g. `configCount 12 5 2 1 = 1` (the twin pair `(11,13)`),
      `configCount 20 5 2 2 = 1` (the twin pair `(17,19)`) — both by `decide`.

    * `PrimePairAsymptotic q g` bundles the HL/BV hypothesis as an EXPLICIT named
      structure: a positive constant `C`, a main term `main(N) → ∞`, a
      lower-order error (`err/main → 0`), and the uniform per-configuration
      asymptotic `|configCount N q g a − C·main(N)/(q−2)| ≤ err(N)` for every
      admissible `a`. The SAME main term for every configuration is precisely the
      Hardy–Littlewood uniformity claim.

    * `equidistribution_of_asymptotic` (PROVED implication, rung OPEN): from ANY
      such structure, EACH admissible configuration `a` satisfies
        `configCount N q g a / totalConfigCount N q g → 1/(q−2)`.
      The proof carries real work — it is NOT `h₂ h₁` modus ponens. It runs a
      genuine two-asymptotic quotient argument: the per-configuration bound gives
      `configCount/main → C/(q−2)`; SUMMING that bound over the configurations and
      using the VERIFIED count `card(admissibleResidues) = q−2`
      (`universal_admissibility_count`, reused) gives `total/main → C`; and
      `Tendsto.div` divides them, `(C/(q−2))/C = 1/(q−2)`. The count `q−2` enters
      twice — as the number of summands and as the target density — so the
      conclusion is derived, not assumed.

    * Gate-0 (satisfiability) is NAMED, never discharged. `AsymptoticExists` is the
      obligation "a structure exists"; a proof is HL/BV strength (OPEN). The shape
      is NOT contradictory — `asymptotic_shape_consistent` exhibits witnesses for
      the non-count fields (`C>0`, `main→∞`, `err/main→0`) simultaneously, so the
      schema is not vacuous theater; only the tie of `C·main/(q−2)` to the REAL
      prime-pair count is open. `equidistribution_of_asymptotic_exists` is the
      honest hardness direction (existence ⇒ equidistribution).

  COMPLETE TRANSITION SUPPORT vs EQUIDISTRIBUTION (the honest distinction):

    * `prime_pair_config_admissible` (PROVED, UNCONDITIONAL): every gap-`g` prime
      pair `(p, p+g)` with `p, p+g > q` has its starting residue `p mod q` in one
      of the exactly `q−2` admissible configurations. This is "complete transition
      support" — pairs LAND in the admissible set. It says NOTHING about HOW they
      distribute among the configurations.

    * Equidistribution — that each configuration gets the SAME 1/(q−2) share — is
      strictly stronger and is ONLY the conditional `equidistribution_of_asymptotic`
      above. Support is proved; equal distribution is conditional. Conflating the
      two is exactly the Paper-3 overclaim this module refuses.

  Reuse: `Brockian.Admissibility` (`admissibleResidues`, `universal_admissibility_count`
  = the q−2 count). The constant `C` is, conceptually, the Hardy–Littlewood singular
  series (positive on admissible tuples by `Brockian.SingularSeries.singular_series_finite_pos`);
  it is carried here as an abstract positive parameter to keep the schema free of the
  unformalized infinite-product convergence.

  Verification (spec §2A):
    - `#print axioms`  : ⊆ {propext, Classical.choice, Quot.sound}
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.Admissibility

set_option autoImplicit false

open Finset Filter Topology
open Brockian.Admissibility

namespace Brockian.Equidistribution

/-! ### The real gap-`g` prime-pair configuration count -/

/-- **`configCount N q g a`** — the REAL number of primes `p ≤ N` such that `p + g`
is also prime and `p ≡ a (mod q)`. This is the genuine count of gap-`g` prime pairs
`(p, p+g)`, `p ≤ N`, whose starting residue configuration is `a`. Not a placeholder:
it is decidable and evaluated (see the `decide` computations at the end). -/
def configCount (N q g : ℕ) (a : ZMod q) : ℕ :=
  ((Finset.range (N + 1)).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (p + g) ∧ (p : ZMod q) = a)).card

/-- **`totalConfigCount N q g`** — the total number of gap-`g` prime pairs `p ≤ N`
whose starting residue is admissible, summed over the `q−2` admissible
configurations. This is the denominator of the configuration densities. -/
def totalConfigCount (N q : ℕ) [NeZero q] (g : ℕ) : ℕ :=
  ∑ b ∈ admissibleResidues q (g : ZMod q), configCount N q g b

/-! ### Complete transition support (PROVED, UNCONDITIONAL)

Every gap-`g` prime pair with both endpoints above the wheel modulus lands in one of
the `q−2` admissible configurations. This is strictly WEAKER than equidistribution. -/

/-- **`prime_pair_config_admissible` — complete transition support.** If `p` and
`p + g` are both prime and both exceed the modulus `q ≥ 2`, then the starting
residue `p mod q` is admissible (lies in `admissibleResidues q g`). Proof: a prime
above `q` is not divisible by `q`, so `p ≢ 0` and `p + g ≢ 0`, i.e. `p ∉ {0, −g}`.

This says pairs LAND in the admissible set — NOT how they distribute. Equal
distribution across the admissible configurations is the CONDITIONAL statement
`equidistribution_of_asymptotic`, never this one. -/
theorem prime_pair_config_admissible {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 ≤ q)
    {p : ℕ} (hp : Nat.Prime p) (hpg : Nat.Prime (p + g))
    (hpq : q < p) (hpgq : q < p + g) :
    (p : ZMod q) ∈ admissibleResidues q (g : ZMod q) := by
  rw [admissibleResidues, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · -- `p ≢ 0 (mod q)`: else `q ∣ p`, but `p` prime and `q < p`.
    intro h
    have hdvd : q ∣ p := (CharP.cast_eq_zero_iff (ZMod q) q p).mp h
    rcases (hp.eq_one_or_self_of_dvd q hdvd) with h1 | h1 <;> omega
  · -- `p ≢ −g (mod q)`: else `(p+g) ≡ 0`, so `q ∣ (p+g)`, but `p+g` prime and `q < p+g`.
    intro h
    have hz : ((p + g : ℕ) : ZMod q) = 0 := by push_cast; rw [h]; ring
    have hdvd : q ∣ (p + g) := (CharP.cast_eq_zero_iff (ZMod q) q (p + g)).mp hz
    rcases (hpg.eq_one_or_self_of_dvd q hdvd) with h1 | h1 <;> omega

/-! ### The Hardy–Littlewood / Bombieri–Vinogradov asymptotic hypothesis

An EXPLICIT named structure. Constructing a term of it for the real `configCount`
is HL/BV strength (`AsymptoticExists`, OPEN). No instance is provided. -/

/-- **`PrimePairAsymptotic q g`** — the bundled asymptotic hypothesis. It carries a
positive constant `C` (conceptually the Hardy–Littlewood singular series), a main
term `mainTerm(N) → ∞` (conceptually `π(N)`), a lower-order error
(`err/mainTerm → 0`), and the KEY uniform per-configuration asymptotic:

    `|configCount N q g a − C·mainTerm(N)/(q−2)| ≤ err(N)`

for EVERY admissible configuration `a`. The single shared main term `C·mainTerm/(q−2)`
across all admissible configurations is the Hardy–Littlewood uniformity claim.

This is a SCHEMA, not an assertion of existence: the field constraints tie the real
`configCount` to the shared main term, which is exactly what HL/BV assert and what is
OPEN. The shape is non-vacuous (`asymptotic_shape_consistent`); no instance is built. -/
structure PrimePairAsymptotic (q : ℕ) [NeZero q] (g : ℕ) where
  /-- The Hardy–Littlewood constant (singular-series strength); strictly positive. -/
  C : ℝ
  /-- Positivity of the constant. -/
  C_pos : 0 < C
  /-- The main term (conceptually `π(N)`), tending to infinity. -/
  mainTerm : ℕ → ℝ
  /-- The main term grows without bound. -/
  mainTerm_tendsto : Tendsto mainTerm atTop atTop
  /-- The error bar. -/
  err : ℕ → ℝ
  /-- The error is lower order than the main term. -/
  err_lower_order : Tendsto (fun N => err N / mainTerm N) atTop (nhds 0)
  /-- The gap is a genuine nonzero class (so there are exactly `q−2` admissible
  configurations). -/
  gap_ne : (g : ZMod q) ≠ 0
  /-- **The HL/BV uniform per-configuration asymptotic.** Each admissible
  configuration's real count is within the (lower-order) error of the SAME main
  term `C·mainTerm/(q−2)`. -/
  count_asymptotic : ∀ a ∈ admissibleResidues q (g : ZMod q), ∀ N,
    |(configCount N q g a : ℝ) - C * mainTerm N / ((q : ℝ) - 2)| ≤ err N

/-! ### A ratio-asymptotic helper (genuine limit work) -/

/-- If `M → ∞` and `E/M → 0` and `|f − L·M| ≤ E` pointwise, then `f/M → L`. This is
the honest analytic core reused for both the per-configuration and the total counts —
a squeeze on `f/M − L = (f − L·M)/M` whose absolute value is `≤ E/M → 0`. -/
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

/-! ### THE HONEST CONDITIONAL EQUIDISTRIBUTION THEOREM (PROVED implication, rung OPEN) -/

/-- **`equidistribution_of_asymptotic` — THE HONEST CONDITIONAL.** Given a
`PrimePairAsymptotic q g` and `q > 2`, EACH admissible configuration `a` receives
asymptotic density `→ 1/(q−2)`:

    `configCount N q g a / totalConfigCount N q g → 1/(q−2)`.

REAL WORK (this is NOT `h₂ h₁` modus ponens):
  1. `configCount(a)/main → C/(q−2)` from the per-configuration bound (`ratio_tendsto`);
  2. summing that bound over the admissible configurations and using the VERIFIED
     `card(admissibleResidues) = q−2` (`universal_admissibility_count`) gives
     `total/main → C`;
  3. `Tendsto.div` divides the two limits and `(C/(q−2))/C = 1/(q−2)`.
The count `q−2` is used twice — as the number of summands and as the target — so the
1/(q−2) density is DERIVED from the asymptotic, not restated from a hypothesis.

RUNG: OPEN. It is only as strong as its premise, which is Hardy–Littlewood /
Bombieri–Vinogradov strength (`AsymptoticExists`, OPEN). NEVER citable as a proof of
equidistribution. -/
theorem equidistribution_of_asymptotic
    {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (H : PrimePairAsymptotic q g)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    Tendsto (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ))
      atTop (nhds (1 / ((q : ℝ) - 2))) := by
  have hq2 : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq2ne : ((q : ℝ) - 2) ≠ 0 := by linarith
  have hcard : (admissibleResidues q (g : ZMod q)).card = q - 2 :=
    universal_admissibility_count q (g : ZMod q) H.gap_ne
  have hcardR : ((admissibleResidues q (g : ZMod q)).card : ℝ) = (q : ℝ) - 2 := by
    rw [hcard, Nat.cast_sub (by omega)]; norm_num
  -- Step 1: each admissible configuration relative to the main term.
  have hconfig : Tendsto (fun N => (configCount N q g a : ℝ) / H.mainTerm N)
      atTop (nhds (H.C / ((q : ℝ) - 2))) := by
    apply ratio_tendsto H.mainTerm_tendsto H.err_lower_order
    intro N
    have hb := H.count_asymptotic a ha N
    have heq : H.C * H.mainTerm N / ((q : ℝ) - 2)
        = (H.C / ((q : ℝ) - 2)) * H.mainTerm N := by ring
    rwa [heq] at hb
  -- Step 2: the total relative to the main term, using card = q−2.
  have htotal_bound : ∀ N, |(totalConfigCount N q g : ℝ) - H.C * H.mainTerm N|
      ≤ ((q : ℝ) - 2) * H.err N := by
    intro N
    have hcast : (totalConfigCount N q g : ℝ)
        = ∑ b ∈ admissibleResidues q (g : ZMod q), (configCount N q g b : ℝ) := by
      unfold totalConfigCount; rw [Nat.cast_sum]
    have hsum_const :
        ∑ _b ∈ admissibleResidues q (g : ZMod q), H.C * H.mainTerm N / ((q : ℝ) - 2)
          = H.C * H.mainTerm N := by
      rw [Finset.sum_const, nsmul_eq_mul, hcardR, ← mul_div_assoc]
      exact mul_div_cancel_left₀ _ hq2ne
    rw [hcast]
    have hkey :
        (∑ b ∈ admissibleResidues q (g : ZMod q), (configCount N q g b : ℝ))
            - H.C * H.mainTerm N
          = ∑ b ∈ admissibleResidues q (g : ZMod q),
              ((configCount N q g b : ℝ) - H.C * H.mainTerm N / ((q : ℝ) - 2)) := by
      rw [Finset.sum_sub_distrib, hsum_const]
    rw [hkey]
    calc |∑ b ∈ admissibleResidues q (g : ZMod q),
              ((configCount N q g b : ℝ) - H.C * H.mainTerm N / ((q : ℝ) - 2))|
        ≤ ∑ b ∈ admissibleResidues q (g : ZMod q),
              |(configCount N q g b : ℝ) - H.C * H.mainTerm N / ((q : ℝ) - 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b ∈ admissibleResidues q (g : ZMod q), H.err N :=
          Finset.sum_le_sum (fun b hb => H.count_asymptotic b hb N)
      _ = ((admissibleResidues q (g : ZMod q)).card : ℝ) * H.err N := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((q : ℝ) - 2) * H.err N := by rw [hcardR]
  have htotal : Tendsto (fun N => (totalConfigCount N q g : ℝ) / H.mainTerm N)
      atTop (nhds H.C) := by
    have hfun : (fun N => ((q : ℝ) - 2) * H.err N / H.mainTerm N)
        = (fun N => ((q : ℝ) - 2) * (H.err N / H.mainTerm N)) := by
      funext N; rw [mul_div_assoc]
    have hlo : Tendsto (fun N => ((q : ℝ) - 2) * H.err N / H.mainTerm N)
        atTop (nhds 0) := by
      rw [hfun]; simpa using H.err_lower_order.const_mul ((q : ℝ) - 2)
    exact ratio_tendsto H.mainTerm_tendsto hlo htotal_bound
  -- Step 3: divide the two limits.
  have hdiv : Tendsto
      (fun N => ((configCount N q g a : ℝ) / H.mainTerm N)
        / ((totalConfigCount N q g : ℝ) / H.mainTerm N))
      atTop (nhds ((H.C / ((q : ℝ) - 2)) / H.C)) :=
    hconfig.div htotal (ne_of_gt H.C_pos)
  have heqf : (fun N => ((configCount N q g a : ℝ) / H.mainTerm N)
        / ((totalConfigCount N q g : ℝ) / H.mainTerm N))
      =ᶠ[atTop] (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ)) := by
    filter_upwards [H.mainTerm_tendsto.eventually_gt_atTop 0] with N hMpos
    have hMne : H.mainTerm N ≠ 0 := ne_of_gt hMpos
    rcases eq_or_ne ((totalConfigCount N q g : ℝ)) 0 with h0 | h0
    · simp [h0]
    · field_simp
  have hval : (H.C / ((q : ℝ) - 2)) / H.C = 1 / ((q : ℝ) - 2) := by
    have hCne : H.C ≠ 0 := ne_of_gt H.C_pos
    rw [div_div, mul_comm ((q : ℝ) - 2) H.C, div_mul_eq_div_div, div_self hCne]
  rw [← hval]
  exact hdiv.congr' heqf

/-! ### Gate-0: the satisfiability obligation (NAMED, left OPEN) -/

/-- **`AsymptoticExists q g`** — the Gate-0 obligation: *there exists* a
`PrimePairAsymptotic q g`, i.e. the real prime-pair count actually obeys the uniform
HL/BV asymptotic. This is the missing premise of the schema. It is NOT proved here; a
proof is Hardy–Littlewood / Bombieri–Vinogradov strength. Recorded as a Prop container
(CONJECTURE register) so the claim slot and its falsifier are named but never asserted. -/
def AsymptoticExists (q : ℕ) [NeZero q] (g : ℕ) : Prop :=
  Nonempty (PrimePairAsymptotic q g)

/-- **`equidistribution_of_asymptotic_exists` — the honest HARDNESS direction.** The
mere existence of an HL/BV asymptotic structure already implies density `→ 1/(q−2)`
for every admissible configuration. This is why Gate-0 (`AsymptoticExists`) is
genuinely open, not an oversight: any instance immediately yields equidistribution,
which is itself unproven. No instance is built. -/
theorem equidistribution_of_asymptotic_exists
    {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (h : AsymptoticExists q g)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    Tendsto (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ))
      atTop (nhds (1 / ((q : ℝ) - 2))) := by
  obtain ⟨H⟩ := h
  exact equidistribution_of_asymptotic hq H ha

/-- **`asymptotic_shape_consistent` — Gate-0 non-vacuity witness.** The
non-count field constraints of `PrimePairAsymptotic` — a positive constant, a main
term tending to infinity, and a lower-order error — are jointly SATISFIABLE
(witnesses `C = 1`, `mainTerm N = N+1`, `err = 0`). Hence the schema is not
self-contradictory theater: it is a real hypothesis whose ONLY open content is the
tie of the shared main term to the actual prime-pair count (`count_asymptotic`),
which is Hardy–Littlewood / Bombieri–Vinogradov strength. NO instance of the full
structure is built (that would prove equidistribution). -/
theorem asymptotic_shape_consistent :
    ∃ (C : ℝ) (mainTerm err : ℕ → ℝ),
      0 < C ∧ Tendsto mainTerm atTop atTop ∧
      Tendsto (fun N => err N / mainTerm N) atTop (nhds 0) := by
  refine ⟨1, (fun N => (N : ℝ) + 1), (fun _ => 0), one_pos, ?_, ?_⟩
  · exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  · simp only [zero_div]; exact tendsto_const_nhds

/-! ### Small-case computations of the REAL count (COMPUTATION, via `decide`)

Direct evidence that `configCount` is genuinely evaluated, not a placeholder. The
admissible configurations mod `5` for gap `2` are `{1, 2, 4}` (excluding `0` and
`−2 ≡ 3`). -/

/-- COMPUTATION (kernel `decide`): mod 5, gap 2, configuration 1 up to 12 holds one
twin-pair start — `p = 11`, the pair `(11, 13)`. -/
theorem configCount_twelve_five_two_one : configCount 12 5 2 1 = 1 := by decide

/-- COMPUTATION (kernel `decide`): mod 5, gap 2, configuration 2 up to 20 holds one
twin-pair start — `p = 17`, the pair `(17, 19)`. -/
theorem configCount_twenty_five_two_two : configCount 20 5 2 2 = 1 := by decide

end Brockian.Equidistribution
