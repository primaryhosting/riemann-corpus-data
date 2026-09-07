/-
  Brockian/AdmissibilityHLCriterion.lean — the Hardy–Littlewood admissibility criterion.

  Roadmap #11.  The core modules count, per modulus, the admissible start residues:
  `Brockian.Admissibility` (the single-gap `q − 2` law), `Brockian.AdmissibilityKTuple`
  (the general `q − |H|` law and its CRT lift), and the finite local wrapper in
  `Brockian.Admissibility.CriterionScaffold`.  Those are *local counts*.  This module
  proves the actual GLOBAL admissibility criterion for a finite integer tuple, in the
  standard Hardy–Littlewood form:

      a finite `H ⊆ ℤ` is admissible  ⟺  for every prime `p`, the image of `H` in
      `ZMod p` omits at least one residue class  ⟺  `ν_p(H) := |H mod p| < p`  for all `p`.

  The definition of admissibility taken here is the standard sieve one: `H` is admissible
  iff at no prime does its reduction cover *every* residue class (an uncovered class is a
  class the sieve can use).  Everything below is exact finite reasoning; no prime
  distribution, singular series, sieve asymptotic, or representation theorem is asserted.

  ## What is proved
  * `omitsResidue_iff_ne_univ` — omitting a residue class mod `p` = the image is not all
    of `ZMod p` (rules out any vacuous reading of "omits").
  * `omitsResidue_iff_nu_lt` — omitting a class mod `p` ⟺ `ν_p(H) < p` (for `p ≠ 0`),
    the finite-cardinality heart of the criterion.
  * `admissible_iff_nu_lt` / `admissible_iff_card_image_lt` — **the criterion**:
    `Admissible H ↔ ∀ p prime, ν_p(H) < p`, stated both via `ν` and verbatim as
    `∀ p prime, (H.image (· : ZMod p)).card < p`.
  * `admissible_iff_nu_lt_of_le_card` — **the finiteness reduction**: it suffices to
    check primes `p ≤ |H|` (for larger primes `ν_p(H) ≤ |H| < p` automatically), so
    admissibility is verifiable from finitely many local checks.
  * `admissible_iff_exists_avoiding_start` — connects to the per-modulus count: `H` is
    admissible ⟺ at every prime there is a start residue `a` with `a + h ≠ 0` for all
    occupied classes `h` (reusing the scaffold's `LocalTupleAdmissible`).
  * `admissible_iff_count_pos` — the count form: `H` is admissible ⟺ at every prime the
    `q − ν` admissible-residue count of `Brockian.AdmissibilityKTuple` is positive.
  * `admissible_zero_two` — `{0,2}` is admissible (COMPUTATION for the one local check).
  * `not_admissible_zero_two_four` — `{0,2,4}` is inadmissible: mod 3 it covers all
    residues (COMPUTATION for `ν_3 = 3`).

  ## What is NOT proved
  * No claim that admissible tuples are realized by primes infinitely often (that is the
    open Hardy–Littlewood conjecture, not the admissibility criterion). This module is the
    combinatorial criterion only.
  * No singular-series constant, density, or asymptotic count is derived.
  * The iterated multi-prime CRT product `∏ (pᵢ − νᵢ)` is in `AdmissibilityKTuple`
    (2-factor); it is not re-derived or extended here.

  Verification (spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean; the two example
      lemmas use kernel `decide` on small `ZMod` computations — COMPUTATION register)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.Admissibility
import Brockian.AdmissibilityKTuple
import Brockian.AdmissibilityCriterionScaffold

set_option autoImplicit false

open Finset
open Brockian.AdmissibilityKTuple
open Brockian.Admissibility.CriterionScaffold

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/
def residueImage (p : ℕ) (H : Finset ℤ) : Finset (ZMod p) :=
  H.image (fun n : ℤ => (n : ZMod p))

/-- `ν_p(H)`: the number of distinct residue classes mod `p` occupied by `H`. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- `H` *omits a residue class* mod `p`: some residue mod `p` is not occupied by `H`. -/
def OmitsResidue (p : ℕ) (H : Finset ℤ) : Prop :=
  ∃ r : ZMod p, r ∉ residueImage p H

/-- **Admissibility (Hardy–Littlewood).** A finite integer tuple `H` is admissible iff
for every prime `p` it omits at least one residue class mod `p` (equivalently, at no
prime does its reduction cover every residue class). -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

/-- Omitting a residue class mod `p` means exactly that the occupied image is not all of
`ZMod p`.  This pins down the intended meaning of "omits". -/
theorem omitsResidue_iff_ne_univ (p : ℕ) [NeZero p] (H : Finset ℤ) :
    OmitsResidue p H ↔ residueImage p H ≠ Finset.univ := by
  unfold OmitsResidue
  constructor
  · rintro ⟨r, hr⟩ hcov
    exact hr (hcov ▸ Finset.mem_univ r)
  · intro hne
    by_contra hc
    push_neg at hc
    exact hne (Finset.eq_univ_iff_forall.mpr hc)

/-- Omitting a residue class mod a nonzero modulus `p` is equivalent to the finite
inequality `ν_p(H) < p`. -/
theorem omitsResidue_iff_nu_lt (p : ℕ) [NeZero p] (H : Finset ℤ) :
    OmitsResidue p H ↔ nu p H < p := by
  rw [omitsResidue_iff_ne_univ]
  have h : (residueImage p H).card < Fintype.card (ZMod p)
      ↔ residueImage p H ≠ Finset.univ :=
    Finset.card_lt_iff_ne_univ _
  rw [ZMod.card] at h
  exact h.symm

/-- **The Hardy–Littlewood admissibility criterion (ν form).** A finite integer tuple is
admissible iff at every prime it occupies fewer than `p` residue classes. -/
theorem admissible_iff_nu_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu p H < p := by
  unfold Admissible
  constructor
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    exact (omitsResidue_iff_nu_lt p H).mp (h p hp)
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    exact (omitsResidue_iff_nu_lt p H).mpr (h p hp)

/-- **The criterion, verbatim.** `H` is admissible iff for every prime `p` the image of
`H` in `ZMod p` has fewer than `p` elements. -/
theorem admissible_iff_card_image_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → (H.image (fun n : ℤ => (n : ZMod p))).card < p :=
  admissible_iff_nu_lt H

/-- **The finiteness reduction.** Admissibility only needs checking at primes `p ≤ |H|`:
for a prime `p > |H|` we have `ν_p(H) ≤ |H| < p` automatically.  Hence admissibility is
decided by finitely many local checks. -/
theorem admissible_iff_nu_lt_of_le_card (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → nu p H < p := by
  rw [admissible_iff_nu_lt]
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    by_cases hle : p ≤ H.card
    · exact h p hp hle
    · push_neg at hle
      calc nu p H ≤ H.card := Finset.card_image_le
        _ < p := hle

/-- **Connection to the per-modulus count (existence form).** `H` is admissible iff at
every prime there is a start residue avoiding every occupied class — i.e. some `a` with
`a + h ≠ 0` for all `h` in the reduction of `H`.  This is exactly the local admissible
start of `Brockian.Admissibility.CriterionScaffold`. -/
theorem admissible_iff_exists_avoiding_start (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime →
      ∃ a : ZMod p, ∀ h ∈ residueImage p H, a + h ≠ 0 := by
  rw [admissible_iff_nu_lt]
  constructor
  · intro hcrit p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    have hla : LocalTupleAdmissible p (residueImage p H) := by
      rw [localTupleAdmissible_iff_obstruction_lt]
      exact hcrit p hp
    exact (localTupleAdmissible_iff_exists_avoids _).mp hla
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    have hla : LocalTupleAdmissible p (residueImage p H) :=
      (localTupleAdmissible_iff_exists_avoids _).mpr (h p hp)
    rw [localTupleAdmissible_iff_obstruction_lt] at hla
    exact hla

/-- **Connection to the `q − ν` count.** `H` is admissible iff at every prime the number
of admissible start residues (`p − ν_p(H)`, the count of `Brockian.AdmissibilityKTuple`)
is strictly positive. -/
theorem admissible_iff_count_pos (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, ∀ hp : p.Prime,
      letI : NeZero p := ⟨hp.pos.ne'⟩
      0 < (admissibleTupleResidues p (residueImage p H)).card := by
  rw [admissible_iff_nu_lt]
  have hnu : ∀ p, nu p H = (residueImage p H).card := fun _ => rfl
  constructor
  · intro hcrit p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    rw [admissibleTupleResidues_card]
    have := hcrit p hp
    have := hnu p
    omega
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    have hc := h p hp
    rw [admissibleTupleResidues_card] at hc
    have := hnu p
    omega

/-- **COMPUTATION.** `{0, 2}` is admissible.  By the finiteness reduction only the prime
`p = 2` needs checking, and mod 2 the tuple occupies a single class (`ν_2 = 1 < 2`). -/
theorem admissible_zero_two : Admissible ({0, 2} : Finset ℤ) := by
  rw [admissible_iff_nu_lt_of_le_card]
  intro p hp hle
  have hcard : ({0, 2} : Finset ℤ).card = 2 := by decide
  rw [hcard] at hle
  have hp2 : p = 2 := le_antisymm hle hp.two_le
  subst hp2
  decide

/-- **COMPUTATION.** `{0, 2, 4}` is inadmissible: modulo 3 it occupies all three residue
classes (`ν_3 = 3`), so it omits none. -/
theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℤ) := by
  intro h
  have h3 := (admissible_iff_nu_lt _).mp h 3 (by norm_num)
  have hnu3 : nu 3 ({0, 2, 4} : Finset ℤ) = 3 := by decide
  omega

end Brockian.AdmissibilityHLCriterion
