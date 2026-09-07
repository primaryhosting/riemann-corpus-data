/-
  Brockian/EquidistributionUniformity.lean — ATTACKING THE SINGULAR-SERIES
  UNIFORMITY SYMMETRY `sing a = sing b` VIA THE ADMISSIBLE-CLASS SYMMETRY GROUP.

  `Brockian.EquidistributionBVReduction` reduced equidistribution (density 1/(q−2))
  to the Hardy–Littlewood / Bombieri–Vinogradov asymptotic PLUS the extra input
  `huniform : ∀ a b admissible, sing a = sing b` (the singular-series constants are
  class-independent). That uniformity was taken there as a bare cited hypothesis.

  This file attacks that hypothesis through the SYMMETRY GROUP of the admissible set.
  The admissible residues are `univ \ {0, −g}`; the endpoint-swap reflection
  `a ↦ −g − a` permutes this set (already `admissible_reflection_symmetry`). If a
  group of admissibility-preserving symmetries acts TRANSITIVELY on the admissible
  classes AND the singular series `sing` is INVARIANT under those symmetries, then
  `sing` is constant on the (single) orbit, i.e. `sing a = sing b`. The point is that
  this splits the one analytic fact `sing a = sing b` into two structurally DIFFERENT
  claims — (T) a purely GROUP-THEORETIC transitivity that mentions no `sing`, and
  (I) a per-symmetry INVARIANCE `sing (σ a) = sing a` — neither of which alone gives
  uniformity, so the reduction is genuine (not modus-ponens theater).

  ## What is proved

    * `reflect_involutive`, `reflect_affine`, `reflect_preserves_admissible`
      (PROVED, UNCONDITIONAL) — the reflection `reflect q g a = −g − a` is an
      involution, is the affine map `a ↦ (−1)·a + (−g)`, and maps the admissible set
      to itself (reusing `admissible_reflection_symmetry`). A genuine, exact, finite
      symmetry of the admissible configuration set.

    * `iterate_mem_admissible`, `sing_iterate` (PROVED) — the analytic core of the
      reduction: for an admissibility-preserving `σ` with `sing`-invariance, every
      iterate `σ^[n] a` stays admissible and `sing (σ^[n] a) = sing a` (induction along
      the orbit — this is where the per-generator invariance is genuinely CHAINED).

    * `sing_uniform_of_transitive` (REDUCTION, conditional_rung = literature) — if the
      cyclic action of a single admissibility-preserving `σ` is transitive on the
      admissible classes (`IterTransitive`, group-theoretic, NO `sing`) and `sing` is
      invariant under `σ` (`SingInvariant`, analytic), then `sing a = sing b` for all
      admissible `a, b`. Genuinely weaker than its conclusion: `IterTransitive` never
      mentions `sing`, and `SingInvariant` for a NON-transitive `σ` (e.g. the q = 5
      reflection below) does NOT give uniformity.

    * `equidistribution_of_transitive_symmetry` (conditional_rung = literature) — the
      capstone: BV asymptotic + a transitive `sing`-invariant symmetry ⟹ each
      admissible class has density → 1/(q−2). Chains `sing_uniform_of_transitive` into
      the reused `equidistribution_of_BV_uniform`.

    * `sing_uniform_three` (PROVED, UNCONDITIONAL) — **the q = 3 concrete win.** For the
      wheel modulus q = 3 there is EXACTLY ONE admissible class (`admissibility_count_three`),
      so any two admissible `a, b` are literally equal, hence `sing a = sing b` with NO
      symmetry or analytic hypothesis at all. `equidistribution_three` then gives, from
      any BV structure, density → 1/(3−2) = 1 for that single class.

    * `reflect_five_fixes_four`, `reflect_five_four_orbit`,
      `reflection_not_transitive_five` (PROVED) — **the honest q = 5 obstruction.** For
      q = 5, gap 2, the three admissible classes are `{1, 2, 4}`; the reflection swaps
      `1 ↔ 2` and FIXES `4`, so its cyclic orbit of `4` is `{4}` and it is NOT transitive.
      Hence reflection symmetry does NOT establish q = 5 uniformity — that case stays OPEN.

  ## What is NOT proved

    * q = 5 (and any q ≥ 5) uniformity. It is NOT reachable by the reflection (proved
      non-transitive above), and the whole affine stabilizer of the 2-element forbidden
      set `{0, −g}` has order ≤ 2 (identity and the reflection), so it cannot act
      transitively on the ≥ 3 admissible classes. No larger admissibility-preserving
      map with a claim to `sing`-invariance is available. So q ≥ 5 uniformity is reduced
      ONLY to the two named hypotheses `IterTransitive` + `SingInvariant`, neither of
      which is discharged for q ≥ 5 (the transitivity is combinatorially FALSE for the
      reflection; a genuinely transitive symmetry with a `sing`-invariance claim is not
      exhibited). In strength it remains equivalent to the analytic conjecture.

    * The `sing`-invariance hypothesis `SingInvariant` itself. `sing` is the abstract
      per-class constant of `BVPrimePairAsymptotic`; its invariance under a symmetry is
      a fact about the Hardy–Littlewood singular series' Euler-product definition, which
      is not formalized in Mathlib and is NOT proved here. It is carried as a cited
      hypothesis.

    * Hardy–Littlewood / Bombieri–Vinogradov itself (as in the imported modules).

  Reuse (read-only): `Brockian.EquidistributionBVReduction`
  (`BVPrimePairAsymptotic`, `equidistribution_of_BV_uniform`,
  `admissible_reflection_symmetry`), `Brockian.Equidistribution`
  (`configCount`, `totalConfigCount`), `Brockian.Admissibility`
  (`admissibleResidues`, `admissibility_count_three`). Verified via AXLE @ lean-4.32.0.
-/
import Brockian.EquidistributionBVReduction
import Brockian.Admissibility

set_option autoImplicit false

open Finset Filter Topology
open Brockian.Admissibility
open Brockian.Equidistribution
open Brockian.EquidistributionBVReduction

namespace Brockian.EquidistributionUniformity

/-! ### The endpoint-swap reflection as an explicit affine symmetry (PROVED) -/

/-- **`reflect q g a = −g − a`** — the endpoint-swap reflection: it negates a start
residue and shifts by `−g`, exchanging the two forbidden residues `0` and `−g`. -/
def reflect (q : ℕ) [NeZero q] (g a : ZMod q) : ZMod q := -g - a

/-- The reflection is an involution: applying it twice is the identity. -/
theorem reflect_involutive {q : ℕ} [NeZero q] (g a : ZMod q) :
    reflect q g (reflect q g a) = a := by
  unfold reflect; ring

/-- The reflection is the affine map `a ↦ (−1)·a + (−g)` (unit multiplier `−1`,
translation `−g`) — exhibiting it as a genuine affine symmetry. -/
theorem reflect_affine {q : ℕ} [NeZero q] (g a : ZMod q) :
    reflect q g a = (-1) * a + (-g) := by
  unfold reflect; ring

/-- The reflection maps the admissible set to itself (reusing the unconditional
`admissible_reflection_symmetry`). -/
theorem reflect_preserves_admissible {q : ℕ} [NeZero q] {g a : ZMod q}
    (ha : a ∈ admissibleResidues q g) : reflect q g a ∈ admissibleResidues q g := by
  unfold reflect; exact admissible_reflection_symmetry ha

/-! ### The abstract symmetry-reduction machinery

An admissibility-preserving map with a `sing`-invariance whose cyclic action is
transitive forces `sing` to be constant on the admissible set. The two hypotheses are
kept structurally separate: `PreservesAdmissible`/`IterTransitive` mention only the
admissible set (NO `sing`), while `SingInvariant` is the analytic input. -/

/-- `σ` maps the admissible set into itself. -/
def PreservesAdmissible {q : ℕ} [NeZero q] (g : ZMod q) (σ : ZMod q → ZMod q) : Prop :=
  ∀ a ∈ admissibleResidues q g, σ a ∈ admissibleResidues q g

/-- The per-class singular series is invariant under `σ` on the admissible set. This is
the ANALYTIC hypothesis (a fact about the Hardy–Littlewood singular product). -/
def SingInvariant {q : ℕ} [NeZero q] {g : ℕ} (H : BVPrimePairAsymptotic q g)
    (σ : ZMod q → ZMod q) : Prop :=
  ∀ a ∈ admissibleResidues q (g : ZMod q), H.sing (σ a) = H.sing a

/-- The cyclic action of `σ` is transitive on the admissible classes: any admissible
`b` is some iterate `σ^[n] a` of any admissible `a`. This is the GROUP-THEORETIC
hypothesis; it never mentions `sing`. -/
def IterTransitive {q : ℕ} [NeZero q] (g : ZMod q) (σ : ZMod q → ZMod q) : Prop :=
  ∀ a ∈ admissibleResidues q g, ∀ b ∈ admissibleResidues q g, ∃ n : ℕ, σ^[n] a = b

/-- Every iterate of an admissible class under an admissibility-preserving map stays
admissible. -/
lemma iterate_mem_admissible {q : ℕ} [NeZero q] {g : ℕ} {σ : ZMod q → ZMod q}
    (hpres : PreservesAdmissible (g : ZMod q) σ)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    ∀ n, σ^[n] a ∈ admissibleResidues q (g : ZMod q) := by
  intro n
  induction n with
  | zero => simpa using ha
  | succ k ih => rw [Function.iterate_succ_apply']; exact hpres _ ih

/-- The singular series is constant along the orbit of `σ`: `sing (σ^[n] a) = sing a`.
This is the genuine CHAINING of the per-generator invariance (induction on `n`). -/
lemma sing_iterate {q : ℕ} [NeZero q] {g : ℕ} (H : BVPrimePairAsymptotic q g)
    {σ : ZMod q → ZMod q} (hpres : PreservesAdmissible (g : ZMod q) σ)
    (hinv : SingInvariant H σ)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    ∀ n, H.sing (σ^[n] a) = H.sing a := by
  intro n
  induction n with
  | zero => simp only [Function.iterate_zero_apply]
  | succ k ih =>
      rw [Function.iterate_succ_apply', hinv _ (iterate_mem_admissible hpres ha k), ih]

/-- **`sing_uniform_of_transitive` — THE SYMMETRY REDUCTION (conditional_rung = literature).**
If a single admissibility-preserving symmetry `σ` acts transitively on the admissible
classes (`IterTransitive`, group-theoretic) and the singular series is invariant under it
(`SingInvariant`, analytic), then `sing a = sing b` for all admissible `a, b`.

GENUINE (not theater): `IterTransitive` mentions no `sing`; `SingInvariant` for a
non-transitive `σ` (see `reflection_not_transitive_five`) does not give uniformity.
Only the CONJUNCTION does, via the orbit chaining `sing_iterate`. -/
theorem sing_uniform_of_transitive {q : ℕ} [NeZero q] {g : ℕ}
    (H : BVPrimePairAsymptotic q g) {σ : ZMod q → ZMod q}
    (hpres : PreservesAdmissible (g : ZMod q) σ)
    (hinv : SingInvariant H σ)
    (htrans : IterTransitive (g : ZMod q) σ) :
    ∀ a ∈ admissibleResidues q (g : ZMod q),
      ∀ b ∈ admissibleResidues q (g : ZMod q), H.sing a = H.sing b := by
  intro a ha b hb
  obtain ⟨n, hn⟩ := htrans a ha b hb
  have hchain := sing_iterate H hpres hinv ha n
  rw [hn] at hchain
  exact hchain.symm

/-- The reflection is admissibility-preserving as a `PreservesAdmissible` witness. -/
theorem reflect_preservesAdmissible {q : ℕ} [NeZero q] (g : ZMod q) :
    PreservesAdmissible g (reflect q g) := fun _ ha => reflect_preserves_admissible ha

/-- **`equidistribution_of_transitive_symmetry` (conditional_rung = literature).** The
capstone: a BV asymptotic together with a transitive `sing`-invariant admissible-class
symmetry yields, for each admissible class, density → 1/(q−2). It discharges the
`huniform` premise of `equidistribution_of_BV_uniform` via the symmetry reduction. -/
theorem equidistribution_of_transitive_symmetry {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (H : BVPrimePairAsymptotic q g) {σ : ZMod q → ZMod q}
    (hpres : PreservesAdmissible (g : ZMod q) σ)
    (hinv : SingInvariant H σ)
    (htrans : IterTransitive (g : ZMod q) σ)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) :
    Tendsto (fun N => (configCount N q g a : ℝ) / (totalConfigCount N q g : ℝ)) atTop
      (nhds (1 / ((q : ℝ) - 2))) :=
  equidistribution_of_BV_uniform hq H (sing_uniform_of_transitive H hpres hinv htrans) ha

/-! ### q = 3: uniformity holds UNCONDITIONALLY (exactly one admissible class) -/

/-- **`sing_uniform_three` — the q = 3 concrete win (PROVED, UNCONDITIONAL).** For the
wheel modulus `q = 3` and any nonzero gap there is EXACTLY ONE admissible class
(`admissibility_count_three`), so any two admissible `a, b` are literally equal and
`sing a = sing b` holds with NO symmetry or analytic hypothesis whatsoever. -/
theorem sing_uniform_three {g : ℕ} (H : BVPrimePairAsymptotic 3 g) :
    ∀ a ∈ admissibleResidues 3 ((g : ℕ) : ZMod 3),
      ∀ b ∈ admissibleResidues 3 ((g : ℕ) : ZMod 3), H.sing a = H.sing b := by
  have hcard : (admissibleResidues 3 ((g : ℕ) : ZMod 3)).card = 1 :=
    admissibility_count_three ((g : ℕ) : ZMod 3) H.gap_ne
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  intro a ha b hb
  rw [hx, Finset.mem_singleton] at ha hb
  rw [ha, hb]

/-- **`equidistribution_three` (conditional_rung = literature, in BV only).** From ANY
BV asymptotic for q = 3, the single admissible class has density → 1/(3−2) = 1. The
uniformity input is discharged UNCONDITIONALLY by `sing_uniform_three`. -/
theorem equidistribution_three {g : ℕ} (H : BVPrimePairAsymptotic 3 g)
    {a : ZMod 3} (ha : a ∈ admissibleResidues 3 ((g : ℕ) : ZMod 3)) :
    Tendsto (fun N => (configCount N 3 g a : ℝ) / (totalConfigCount N 3 g : ℝ)) atTop
      (nhds (1 / ((3 : ℝ) - 2))) :=
  equidistribution_of_BV_uniform (by norm_num) H (sing_uniform_three H) ha

/-! ### q = 5: the reflection is NOT transitive — uniformity stays OPEN (PROVED) -/

/-- The q = 5, gap 2 reflection fixes the class `4` (self-paired: `4 ↦ −2 − 4 = 4`). -/
theorem reflect_five_fixes_four : reflect 5 (2 : ZMod 5) 4 = 4 := by decide

/-- The q = 5, gap 2 reflection swaps `1 ↦ 2`. -/
theorem reflect_five_swaps_one : reflect 5 (2 : ZMod 5) 1 = 2 := by decide

/-- The q = 5, gap 2 reflection swaps `2 ↦ 1`. -/
theorem reflect_five_swaps_two : reflect 5 (2 : ZMod 5) 2 = 1 := by decide

/-- Every iterate of `4` under the q = 5 reflection is again `4`: its cyclic orbit is
the singleton `{4}`. -/
theorem reflect_five_four_orbit (n : ℕ) : (reflect 5 (2 : ZMod 5))^[n] 4 = 4 :=
  Function.iterate_fixed reflect_five_fixes_four n

/-- **`reflection_not_transitive_five` — the honest q = 5 obstruction (PROVED).** The
cyclic action of the q = 5, gap 2 reflection is NOT transitive on the admissible classes
`{1, 2, 4}`: no iterate of `4` ever reaches `1` (its whole orbit is `{4}`). Hence
reflection symmetry does NOT discharge the transitivity hypothesis for q = 5, and q = 5
uniformity is NOT established by it — it remains OPEN. -/
theorem reflection_not_transitive_five :
    ¬ IterTransitive (2 : ZMod 5) (reflect 5 (2 : ZMod 5)) := by
  intro h
  obtain ⟨n, hn⟩ := h 4 (by decide) 1 (by decide)
  rw [reflect_five_four_orbit] at hn
  exact absurd hn (by decide)

end Brockian.EquidistributionUniformity
