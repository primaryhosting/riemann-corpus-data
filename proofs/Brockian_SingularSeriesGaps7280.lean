import Mathlib
/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other piece of syntax,
-- including module doc comments, so the required header appears immediately after
-- the single `import Mathlib` line.

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

/-- A finite set of natural numbers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues of the
elements of `H` do not cover all of `ZMod p`.  Equivalently, the local factor of the
singular series attached to `H` at `p` is nonzero for every prime `p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- If the number of elements of `H` is smaller than the prime `p`, then the residues of `H`
cannot cover `ZMod p`. -/
theorem exists_residue_not_mem_of_card_lt {H : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℕ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hr⟩
  have h1 : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) Finset.card_image_le
  rw [Finset.card_univ, ZMod.card] at h1
  omega

/-- **Admissibility of prime gap ranges.**  For any window length `L` and any starting point
`N > L`, the set of primes lying in the interval `[N, N + L)` is an admissible tuple. -/
theorem admissible_primes_Ico (L N : ℕ) (hN : L < N) :
    Admissible ((Finset.Ico N (N + L)).filter Nat.Prime) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpL : p ≤ L
  · -- Small primes: no element of the window is divisible by `p`, so the class `0` is missed.
    refine ⟨0, ?_⟩
    intro h hh
    rw [Finset.mem_filter, Finset.mem_Ico] at hh
    obtain ⟨⟨hNh, _⟩, hhp⟩ := hh
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hph : p = h := (Nat.prime_dvd_prime_iff_eq hp hhp).1 hdvd
    omega
  · -- Large primes: the window is too short to cover all residue classes.
    push_neg at hpL
    refine exists_residue_not_mem_of_card_lt hp ?_
    have hle : ((Finset.Ico N (N + L)).filter Nat.Prime).card ≤ (Finset.Ico N (N + L)).card :=
      Finset.card_filter_le _ _
    rw [Nat.card_Ico] at hle
    omega

/-- **Singular Series Gaps 7280.**  Every window of length `7280` starting beyond `7280`
yields a new admissible tuple: the primes in `[N, N + 7280)` never occupy all residue classes
modulo any prime, so every local factor of the associated singular series is nonzero. -/
theorem SingularSeriesGaps7280 (N : ℕ) (hN : 7280 < N) :
    Admissible ((Finset.Ico N (N + 7280)).filter Nat.Prime) :=
  admissible_primes_Ico 7280 N hN

/-- The tuples produced by `SingularSeriesGaps7280` are not vacuously admissible: for
`N = 7281` the corresponding set of primes is nonempty. -/
theorem SingularSeriesGaps7280_nonempty :
    ((Finset.Ico 7281 (7281 + 7280)).filter Nat.Prime).Nonempty := by
  refine ⟨7283, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

end Brockian

