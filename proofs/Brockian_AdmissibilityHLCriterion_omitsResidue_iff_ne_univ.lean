import Mathlib

set_option autoImplicit false

open Finset

/-
  Context module `Brockian.AdmissibilityHLCriterion`.

  The two corpus lemmas `admissible_iff_exists_avoiding_start` and
  `admissible_iff_count_pos` are omitted here because they refer to the auxiliary
  modules `Brockian.AdmissibilityKTuple` / `Brockian.AdmissibilityCriterionScaffold`,
  which are not part of this project; nothing below uses them.
-/

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

/-- The nine-element offset set `{0, 1, 3, 5, 9, 11, 15, 17, 21}` is not admissible:
it covers both residue classes mod `2`. -/
theorem firstNinePrimeOffsets_not_admissible :
    ¬ Admissible ({0, 1, 3, 5, 9, 11, 15, 17, 21} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 2 Nat.prime_two
  revert hr
  revert r
  decide

theorem admissible_image_add_const (S : Finset ℤ) (c : ℤ)
    (h : Admissible S) : Admissible (S.image (· + c)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨r + (c : ZMod p), ?_⟩
  intro hmem
  apply hr
  simp only [residueImage, Finset.mem_image, Finset.image_image] at hmem ⊢
  obtain ⟨s, hs, hs2⟩ := hmem
  refine ⟨s, hs, ?_⟩
  simp only [Function.comp_apply, Int.cast_add] at hs2
  exact add_right_cancel hs2

theorem not_admissible_of_five_consecutive_mod_five :
    ¬ Admissible ({0, 1, 2, 3, 4} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 5 (by norm_num)
  revert hr
  revert r
  decide

/-- Negation acts as a bijection on residues mod every prime, so it preserves
admissibility. -/
theorem admissible_image_neg (S : Finset ℤ) (h : Admissible S) :
    Admissible (S.image (fun x => -x)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨-r, fun hmem => hr ?_⟩
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp] at hmem ⊢
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hx, by push_cast at hxe ⊢; linear_combination -hxe⟩

theorem residueImage_subset {S T : Finset ℤ} (p : ℕ) (hT : T ⊆ S) :
    residueImage p T ⊆ residueImage p S :=
  Finset.image_subset_image hT

theorem admissible_of_subset {S T : Finset ℤ} (h : Admissible S)
    (hT : T ⊆ S) : Admissible T := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  exact ⟨r, fun hmem => hr (residueImage_subset p hT hmem)⟩

theorem not_admissible_of_all_residues_mod_seven :
    ¬ Admissible ({0, 1, 9, 10, 11, 12, 20} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 7 (by norm_num)
  exact hr (by revert r; decide)

/-- Membership in the mod-`p` residue image of an affine image of `S`. -/
theorem mem_residueImage_image_affine (a b : ℤ) (S : Finset ℤ) (p : ℕ) (z : ZMod p) :
    z ∈ residueImage p (S.image (fun x => a * x + b)) ↔
      ∃ x ∈ S, (a : ZMod p) * (x : ZMod p) + (b : ZMod p) = z := by
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp_apply,
    Int.cast_add, Int.cast_mul]

/-- **Affine invariance of admissibility.** For any integers `a`, `b`, the affine image
`a • S + b` of an admissible set `S` is admissible.  If `p ∤ a` the map is a bijection of
`ZMod p`, so the omitted class is transported; if `p ∣ a` the image collapses to the
single class of `b`, which cannot exhaust `ZMod p` since `p ≥ 2`. -/
theorem admissible_image_affine (a b : ℤ) {S : Finset ℤ}
    (h : Admissible S) : Admissible (S.image (fun x => a * x + b)) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases ha : (a : ZMod p) = 0
  · refine ⟨(b : ZMod p) + 1, ?_⟩
    rw [mem_residueImage_image_affine]
    rintro ⟨x, -, hxe⟩
    rw [ha, zero_mul, zero_add] at hxe
    exact one_ne_zero (α := ZMod p) (by linear_combination -hxe)
  · obtain ⟨r, hr⟩ := h p hp
    refine ⟨(a : ZMod p) * r + (b : ZMod p), ?_⟩
    rw [mem_residueImage_image_affine]
    rintro ⟨x, hx, hxe⟩
    refine hr ?_
    have hrx : (x : ZMod p) = r := by
      have : (a : ZMod p) * ((x : ZMod p) - r) = 0 := by linear_combination hxe
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 ha
      · exact sub_eq_zero.mp h1
    rw [← hrx]
    exact Finset.mem_image_of_mem _ hx

end Brockian.AdmissibilityHLCriterion

