/-
  Brockian/AdmissibilityCRTGeneral.lean — the ITERATED multi-factor CRT admissible count.

  Extends the 2-factor CRT laws of `Brockian.Admissibility.CRT` and
  `Brockian.AdmissibilityKTuple` to an ARBITRARY finite family of pairwise-coprime
  moduli. For a `Fintype`-indexed family `q : ι → ℕ` (each `q i ≠ 0`, pairwise coprime)
  with per-factor forbidden offset sets `H i : Finset (ZMod (q i))`, the number of start
  residues `a : ZMod (∏ i, q i)` whose CRT projection to every factor is admissible is the
  full product of the per-factor counts:

      |A_{∏ qᵢ}(H)| = ∏ᵢ (qᵢ − |Hᵢ|).

  This is the singular-series-style product `∏ (p − ν_p)` (the exact finite count that the
  Hardy–Littlewood constant is built from), here proved as an EXACT cardinality — with no
  correction factor and no exponent.

  ─────────────────────────────────────────────────────────────────────────────
  MECHANISM. Mathlib's elementary iterated CRT ring isomorphism
  `ZMod.prodEquivPi q hcop : ZMod (∏ i, q i) ≃+* Π i, ZMod (q i)` turns the composite
  modulus into the product of the factor rings. Under this bijection the admissible set
  over `ZMod (∏ qᵢ)` is the `e.symm`-image of the product configuration set
  `Fintype.piFinset (fun i => admissibleTupleResidues (q i) (H i))`, whose cardinality is
  `∏ i, |admissibleTupleResidues (q i) (H i)|` (`Fintype.card_piFinset`). Each per-factor
  cardinality is `q i − |H i|` by `AdmissibilityKTuple.admissibleTupleResidues_card`, so
  the counts multiply. The 2-factor law `admissibleTupleResidues_crt_card` is the `|ι| = 2`
  instance of the same phenomenon and is REUSED (not re-proved) for the concrete `mod 15`
  corollary.
  ─────────────────────────────────────────────────────────────────────────────

  ## What is proved (general, closed by reasoning — PROVED register)
  * `admissibleTuple_pi_card` — over the product configuration space `Π i, ZMod (q i)`
    (no coprimality needed), the count of admissible configs is `∏ i, (q i − |H i|)`.
    This is the pure product-of-counts fact; the CRT theorem transports it to `ZMod (∏)`.
  * `admissibleTupleResidues_prodCRT_card` — **the iterated multi-factor CRT count.**
    For a finite family of PAIRWISE-COPRIME moduli, the admissible-residue count over
    `ZMod (∏ i, q i)` is exactly `∏ i, (q i − |H i|)`. General k-tuple offsets per factor.
  * `pairwise_coprime_of_primes` — an injective family of primes is pairwise coprime.
  * `admissibleTupleResidues_prodCRT_primes_card` — **the singular-series product
    `∏ (pᵢ − |Hᵢ|)`** for a finite family of DISTINCT primes (specialization of the
    general theorem via `pairwise_coprime_of_primes`).
  * `admissible_crt_count_fifteen` — the concrete `q = 15 = 3·5` two-factor instance,
    reusing `AdmissibilityKTuple.admissibleTupleResidues_crt_card` (the base of the
    induction): pattern `{0,1}` mod 3 and `{0,1,3}` mod 5 leave `(3−2)·(5−3) = 2` starts.

  ## What is proved (numeric, kernel `decide` — COMPUTATION register)
  * `admissible_ktuple_count_fifteen_factors` — the factor arithmetic
    `(3 − |{0,1}|)·(5 − |{0,1,3}|) = 2` (evaluates the two per-factor Finset cardinalities).

  ## What is NOT proved
  * The Hardy–Littlewood *admissibility criterion* and the analytic *singular series*
    (the infinite product / its convergence, the density asymptotic). Only the EXACT
    finite configuration COUNT `∏ (qᵢ − |Hᵢ|)` over a composite modulus is proved here.
  * No claim is made about which offset sets `H i` arise from an actual admissible tuple;
    `H i` is an arbitrary finite set of coordinate offsets per factor.
  * The general theorem quantifies over any finite index type; it is not restricted to
    prime-power factors (though `admissibleTupleResidues_prodCRT_primes_card` specializes
    to primes, matching the singular-series index set).

  Verification (spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean; the one `decide`
      lemma `admissible_ktuple_count_fifteen_factors` is the only COMPUTATION-register fact)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.AdmissibilityKTuple
import Brockian.AdmissibilityCRT

open Finset
open scoped Function
open Brockian.AdmissibilityKTuple

namespace Brockian.AdmissibilityCRTGeneral

/-- A finite product of nonzero moduli is nonzero, so `ZMod (∏ i, q i)` is a `Fintype`.
Needed for `Finset.univ` over the composite modulus in the CRT count below. -/
instance neZero_prod {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, NeZero (q i)] :
    NeZero (∏ i, q i) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (q i)⟩

/-- **Product configuration count (no coprimality).** Over the product of the factor
residue rings `Π i, ZMod (q i)`, the number of admissible configurations — those whose
`i`-th coordinate is admissible for the offset set `H i` — is the product of the per-factor
counts `∏ i, (q i − |H i|)`. This is the counting core; the CRT theorem below transports it
to the single composite modulus `ZMod (∏ i, q i)`. -/
theorem admissibleTuple_pi_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (H : ∀ i, Finset (ZMod (q i))) :
    (Fintype.piFinset (fun i => admissibleTupleResidues (q i) (H i))).card
      = ∏ i, (q i - (H i).card) := by
  rw [Fintype.card_piFinset]
  exact Finset.prod_congr rfl (fun i _ => admissibleTupleResidues_card (H i))

/-- **The iterated multi-factor CRT admissible count.** For a `Fintype`-indexed family of
PAIRWISE-COPRIME moduli `q : ι → ℕ` (each `q i ≠ 0`) with per-factor forbidden offset sets
`H i`, the number of starts `a : ZMod (∏ i, q i)` whose CRT projection to every factor is
admissible equals the full product `∏ i, (q i − |H i|)`.

Admissibility factors across coprime moduli, so the counts multiply — no correction factor,
no exponent. This is the exact finite count underlying the singular-series product; the
2-factor law `AdmissibilityKTuple.admissibleTupleResidues_crt_card` is the `|ι| = 2` case. -/
theorem admissibleTupleResidues_prodCRT_card
    {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (Nat.Coprime on q)) (H : ∀ i, Finset (ZMod (q i))) :
    (Finset.univ.filter (fun a : ZMod (∏ i, q i) =>
        ∀ i, (ZMod.prodEquivPi q hcop a) i ∈ admissibleTupleResidues (q i) (H i))).card
      = ∏ i, (q i - (H i).card) := by
  classical
  set e := ZMod.prodEquivPi q hcop with he
  -- The admissible set over the composite modulus is the CRT `e.symm`-image of the
  -- product configuration set.
  have hset :
      (Finset.univ.filter (fun a : ZMod (∏ i, q i) =>
          ∀ i, (e a) i ∈ admissibleTupleResidues (q i) (H i)))
        = (Fintype.piFinset (fun i => admissibleTupleResidues (q i) (H i))).image
            (fun f => e.symm f) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fintype.mem_piFinset]
    constructor
    · intro ha
      exact ⟨e a, ha, e.symm_apply_apply a⟩
    · rintro ⟨b, hb, hba⟩
      have hea : e a = b := by rw [← hba]; exact e.apply_symm_apply b
      rw [hea]; exact hb
  rw [hset, Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset]
  exact Finset.prod_congr rfl (fun i _ => admissibleTupleResidues_card (H i))

/-- An injective family of primes is pairwise coprime: distinct primes are coprime. -/
theorem pairwise_coprime_of_primes {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Pairwise (Nat.Coprime on p) := by
  intro i j hij
  show Nat.Coprime (p i) (p j)
  exact (Nat.coprime_primes (hp i) (hp j)).mpr fun h => hij (hinj h)

/-- **The singular-series product `∏ (pᵢ − |Hᵢ|)`.** For a finite family of DISTINCT
primes `p : ι → ℕ` (injective, each prime) with per-prime forbidden offset sets `H i`, the
admissible-residue count over `ZMod (∏ i, p i)` is exactly `∏ i, (p i − |H i|)`. This is the
exact finite form of the singular-series product, obtained from the general iterated-CRT
theorem via `pairwise_coprime_of_primes`. -/
theorem admissibleTupleResidues_prodCRT_primes_card
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (H : ∀ i, Finset (ZMod (p i))) :
    (Finset.univ.filter (fun a : ZMod (∏ i, p i) =>
        ∀ i, (ZMod.prodEquivPi p (pairwise_coprime_of_primes p hp hinj) a) i
              ∈ admissibleTupleResidues (p i) (H i))).card
      = ∏ i, (p i - (H i).card) :=
  admissibleTupleResidues_prodCRT_card p (pairwise_coprime_of_primes p hp hinj) H

/-- **Concrete two-factor instance `q = 15 = 3·5`, reusing the induction base.** With the
pattern `{0,1}` mod 3 (a pair, `ν = 2`) and `{0,1,3}` mod 5 (a triple, `ν = 3`), the number
of starts `a : ZMod 15` admissible on both factors is `(3 − 2)·(5 − 3) = 1·2 = 2`. Proved by
reusing `AdmissibilityKTuple.admissibleTupleResidues_crt_card` — the 2-factor law that is the
base case of the iterated product — with the coprimality `Nat.Coprime 3 5` taken as input. -/
theorem admissible_crt_count_fifteen (h : Nat.Coprime 3 5) :
    (Finset.univ.filter (fun a : ZMod (3 * 5) =>
        ((ZMod.chineseRemainder h) a).1 ∈ admissibleTupleResidues 3 ({0, 1} : Finset (ZMod 3)) ∧
        ((ZMod.chineseRemainder h) a).2 ∈
            admissibleTupleResidues 5 ({0, 1, 3} : Finset (ZMod 5)))).card = 2 := by
  rw [admissibleTupleResidues_crt_card 3 5 h ({0, 1} : Finset (ZMod 3))
      ({0, 1, 3} : Finset (ZMod 5))]
  decide

/-- **COMPUTATION (kernel `decide`).** The per-factor arithmetic for `q = 15 = 3·5`:
`(3 − |{0,1}|)·(5 − |{0,1,3}|) = (3 − 2)·(5 − 3) = 2`. Evaluates the two concrete Finset
cardinalities and the Nat arithmetic; anchors `admissible_crt_count_fifteen`. -/
theorem admissible_ktuple_count_fifteen_factors :
    (3 - ({0, 1} : Finset (ZMod 3)).card) * (5 - ({0, 1, 3} : Finset (ZMod 5)).card) = 2 := by
  decide

end Brockian.AdmissibilityCRTGeneral
