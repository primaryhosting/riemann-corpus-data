import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` (a *gap pattern*) is **admissible** when, for every prime `p`,
the reductions of the elements of `H` modulo `p` omit at least one residue class.  This is
exactly the condition under which the singular series attached to `H` is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- For a prime `p` exceeding the size of `H`, the residues of `H` cannot cover `ZMod p`. -/
theorem exists_residue_not_hit_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hval⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hval⟩
  have hle : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card] at hle
  omega

/-- **Reformulation of admissibility**: only the primes `p ≤ |H|` need to be tested. -/
theorem admissible_iff_small_primes (H : Finset ℤ) :
    Admissible H ↔
      ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    by_cases hle : p ≤ H.card
    · exact hH p hp hle
    · exact exists_residue_not_hit_of_card_lt H p hp (by omega)

/-- Singular Series Gaps 9098.

Two statements about admissible gap patterns:

1. admissibility of a pattern `H` only has to be checked at the primes `p ≤ |H|`;
2. consequently, the two-element pattern `{0, d}` is admissible exactly when the gap `d`
   is even — giving the full range of admissible gaps for pairs.
-/
theorem SingularSeriesGaps9098 :
    (∀ H : Finset ℤ, Admissible H ↔
        ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ∧
    (∀ d : ℤ, Admissible ({0, d} : Finset ℤ) ↔ Even d) := by
  refine ⟨admissible_iff_small_primes, fun d => ?_⟩
  constructor
  · intro hH
    obtain ⟨r, hr⟩ := hH 2 Nat.prime_two
    by_contra hodd
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hodd
    have hd : ((d : ZMod 2)) = 1 := by
      have hk2 : ((d : ZMod 2)) = 2 * (k : ZMod 2) + 1 := by
        rw [hk]; push_cast; ring
      have h20 : (2 : ZMod 2) = 0 := rfl
      rw [hk2, h20]; ring
    have h1 : ((0 : ℤ) : ZMod 2) = 0 := by norm_num
    have hr0 := hr 0 (by simp)
    have hr1 := hr d (by simp)
    rw [h1] at hr0
    rw [hd] at hr1
    clear hr hd hk h1 hodd
    revert r
    decide
  · intro hd
    have hcard : ({0, d} : Finset ℤ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    refine (admissible_iff_small_primes _).2 ?_
    intro p hp hple
    have hp2 : p = 2 := by
      have := hp.two_le
      omega
    subst hp2
    refine ⟨1, ?_⟩
    have hd0 : ((d : ZMod 2)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hd.two_dvd
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · norm_num
    · rw [hd0]; decide

end Brockian

