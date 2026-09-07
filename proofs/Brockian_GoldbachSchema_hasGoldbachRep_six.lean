/-
  Brockian/GoldbachSchema.lean — THE HONEST GOLDBACH CONDITIONAL METATHEOREM.

  ┌───────────────────────────────────────────────────────────────────────┐
  │  RUNG: OPEN (conditional schema). This file does NOT prove Goldbach.    │
  │  It formalizes the genuinely-provable IMPLICATION                        │
  │       "a spectral/margin model for the real representation count        │
  │        ⇒ Goldbach beyond the model's threshold"                          │
  │  and NAMES (does not prove) the satisfiability obligation, which is     │
  │  itself open-problem-strength. NEVER citable as progress on Goldbach.   │
  └───────────────────────────────────────────────────────────────────────┘

  The number-theoretic content is honest:

    * `goldbachCount n` is the REAL count of prime pairs summing to `n`
      (`p ≤ n` prime with `n − p` prime). It is NOT a placeholder: e.g.
      `goldbachCount 4 = 1` (2+2), and `goldbachCount n = 0` exactly when
      `n` has no Goldbach representation.

    * A `SpectralModel` packages an approximation `|G(n) − Main(n)| ≤ Err(n)`
      of that real count together with a positive margin `Main(n) − Err(n) ≥ 1`
      for even `n` beyond a threshold `N₀`.

    * `goldbach_from_spectral_model` (PROVED implication): from ANY such model,
      every even `n > N₀` has a Goldbach representation. The proof is real
      inequality work — the margin plus the two-sided error bound force
      `G(n) ≥ Main(n) − Err(n) ≥ 1`, hence a witness pair exists. It is NOT a
      one-line modus ponens: the model does not contain the conclusion, it
      contains an analytic hypothesis about the real count.

    * Gate-0 satisfiability is DISCUSSED, never discharged. `SpectralModelBeyond`
      names the obligation "a model exists". We prove the honest *hardness*
      direction — a model's very existence IMPLIES Goldbach beyond its
      threshold (`goldbach_beyond_of_model`) — which is precisely why the
      schema is NOT non-vacuously instantiable here: any instance's `margin`
      field is Goldbach-beyond-N₀ in disguise. The obligation is left OPEN.

  Base layer (honest, self-standing): `hasGoldbachRep_four/_six/_eight` are the
  small even cases, proved by exhibiting the prime witnesses (2+2, 3+3, 3+5),
  independent of any model.

  Verification (spec §2A): AXLE independent — @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.GoldbachSchema

open Finset

/-! ### The real Goldbach representation count -/

/-- **`goldbachCount n`** — the REAL number of primes `p ≤ n` such that `n − p`
is also prime, i.e. the count of (ordered, over the first summand) prime-pair
representations `n = p + (n − p)`. This is the genuine Goldbach count, not a
placeholder: `goldbachCount n = 0` exactly when `n` admits no representation as
a sum of two primes. -/
def goldbachCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

/-- **`HasGoldbachRep n`** — `n` is a sum of two primes. This is exactly the
Goldbach conclusion for `n`. -/
def HasGoldbachRep (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- **Positivity of the real count extracts a representation.** If the honest
count is positive there is a genuine member `p` of the filtered set, whose
primality (and that of `n − p`, with `p ≤ n`) yields the witness pair. This is
where "count > 0" is unpacked into an existential — real extraction, not an
assumption. -/
theorem hasGoldbachRep_of_count_pos {n : ℕ} (h : 0 < goldbachCount n) :
    HasGoldbachRep n := by
  unfold goldbachCount at h
  rw [Finset.card_pos] at h
  obtain ⟨p, hp⟩ := h
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hlt, hpp, hqq⟩ := hp
  have hple : p ≤ n := Nat.lt_succ_iff.mp hlt
  exact ⟨p, n - p, hpp, hqq, Nat.add_sub_cancel' hple⟩

/-! ### The spectral/margin model (a CONDITIONAL SCHEMA — never a claim) -/

/-- **`SpectralModel`** — an analytic model of the real Goldbach count on the
even numbers beyond a threshold. `Main` is the (conjectural) main term, `Err`
the error bar; `approx` says the real count `goldbachCount` sits within `Err` of
`Main`, and `margin` says the guaranteed lower envelope `Main − Err` stays `≥ 1`
for even `n > N₀`.

This is a SCHEMA, not an assertion of existence: constructing a term of this
type for the real `goldbachCount` is open-problem-strength (its `margin` field
IS Goldbach beyond `N₀`, see `goldbach_beyond_of_model`). No non-trivial
instance is provided. -/
structure SpectralModel where
  /-- Threshold beyond which the margin holds. -/
  N₀ : ℕ
  /-- Conjectural main term for the representation count. -/
  Main : ℕ → ℝ
  /-- Error bar around the main term. -/
  Err : ℕ → ℝ
  /-- The model approximates the REAL count within `Err`. -/
  approx : ∀ n : ℕ, |(goldbachCount n : ℝ) - Main n| ≤ Err n
  /-- Beyond `N₀`, the guaranteed lower envelope on even `n` is at least one. -/
  margin : ∀ n : ℕ, N₀ < n → Even n → (1 : ℝ) ≤ Main n - Err n

/-! ### The honest conditional metatheorem (a PROVED implication) -/

/-- **`goldbach_from_spectral_model` — THE HONEST IMPLICATION.** From any
`SpectralModel`, every even `n` beyond its threshold has a Goldbach
representation.

Real content: `approx` gives `-(Err n) ≤ G(n) − Main n`, i.e.
`G(n) ≥ Main n − Err n`; `margin` gives `Main n − Err n ≥ 1`; chaining forces
the real count `G(n) ≥ 1`, and `hasGoldbachRep_of_count_pos` turns that into a
witness pair. The conclusion is NOT one of the hypotheses — it is derived by
inequality reasoning on the real count. This is a schema (rung OPEN): it is only
as strong as its unfulfilled premise. -/
theorem goldbach_from_spectral_model (M : SpectralModel) {n : ℕ}
    (hn : M.N₀ < n) (hev : Even n) : HasGoldbachRep n := by
  apply hasGoldbachRep_of_count_pos
  -- Push through the reals: the margin forces the real count to be ≥ 1.
  have hbnd := M.approx n
  have hmar := M.margin n hn hev
  rw [abs_le] at hbnd
  -- hbnd.1 : -(Err n) ≤ (G n : ℝ) - Main n  ⟹  (G n : ℝ) ≥ Main n - Err n
  have hge1 : (1 : ℝ) ≤ (goldbachCount n : ℝ) := by
    have hlow : M.Main n - M.Err n ≤ (goldbachCount n : ℝ) := by linarith [hbnd.1]
    linarith
  have hnat : 1 ≤ goldbachCount n := by exact_mod_cast hge1
  omega

/-! ### Gate-0: the satisfiability obligation (NAMED, left OPEN) -/

/-- **`SpectralModelBeyond N`** — the Gate-0 obligation: *there exists* a
`SpectralModel` whose threshold is `≤ N`. This is the missing premise of the
schema. It is NOT proved here; a proof would be open-problem-strength. It is
recorded as a Prop container (CONJECTURE register) so the claim slot and its
falsifier are named but never asserted. -/
def SpectralModelBeyond (N : ℕ) : Prop :=
  ∃ M : SpectralModel, M.N₀ ≤ N

/-- **`goldbach_beyond_of_model` — the honest HARDNESS direction (PROVED).**
The mere existence of a model with threshold `≤ N` already implies Goldbach for
every even `n > N`. This is why the schema cannot be non-trivially instantiated
here: any candidate instance's `margin` field is Goldbach-beyond-`N₀` in
disguise, so Gate-0 (`SpectralModelBeyond`) is genuinely open, not an oversight.
No instance is built. -/
theorem goldbach_beyond_of_model {N : ℕ} (h : SpectralModelBeyond N)
    {n : ℕ} (hn : N < n) (hev : Even n) : HasGoldbachRep n := by
  obtain ⟨M, hM⟩ := h
  exact goldbach_from_spectral_model M (lt_of_le_of_lt hM hn) hev

/-! ### Base layer — small even cases (honest, model-free witnesses) -/

/-- `4 = 2 + 2`. -/
theorem hasGoldbachRep_four : HasGoldbachRep 4 :=
  ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩

/-- `6 = 3 + 3`. -/
theorem hasGoldbachRep_six : HasGoldbachRep 6 :=
  ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩

/-- `8 = 3 + 5`. -/
theorem hasGoldbachRep_eight : HasGoldbachRep 8 :=
  ⟨3, 5, Nat.prime_three, by norm_num, rfl⟩

/-! ### Small-case computations of the REAL count (COMPUTATION, via `decide`) -/

/-- COMPUTATION (kernel `decide`): the real count at `4` is `1` — only `2 + 2`.
Direct evidence that `goldbachCount` is genuinely evaluated, not a placeholder. -/
theorem goldbachCount_four : goldbachCount 4 = 1 := by decide

/-- COMPUTATION (kernel `decide`): the real count at `10` is `3` —
`3 + 7`, `5 + 5`, `7 + 3`. -/
theorem goldbachCount_ten : goldbachCount 10 = 3 := by decide

end Brockian.GoldbachSchema
