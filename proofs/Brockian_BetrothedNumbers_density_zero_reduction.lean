/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-!
# Betrothed (quasi-amicable) numbers: reduction of Pollack's density-zero theorem

Two distinct positive integers `m ≠ n` are *betrothed* (or *quasi-amicable*) when each is the
sum of the nontrivial proper divisors of the other, i.e. `σ m = σ n = m + n + 1`.
Pollack proved that the set of integers belonging to some betrothed pair has asymptotic
density zero.

This file develops the reusable infrastructure for that theorem and proves the *reduction step*:
the density-zero statement for all betrothed numbers follows from the density-zero statement for
the abundant member of each pair, the latter being described purely `σ`-arithmetically by
`lowBetrothedSet`.

## Dependency graph

```
                       counting_mono ──┐
                                       ├──► hasDensityZero_subset
hasDensityZero_of_counting_le_const_mul┘
                        ▲
                        │
counting_betrothed_le ──┼──────────────────────────► density_zero_reduction
   ▲                    │                                  ▲
   │                    │                                  │
   ├── lowBetrothedSet_subset ◄── mem_lowBetrothedSet_iff   │
   ├── partner_partner ◄── partner_eq, isBetrothedPair_symm │
   └── mem_lowBetrothedSet_iff                              │
                                                            │
        [OPEN ANALYTIC DEPENDENCY: HasDensityZero lowBetrothedSet]
                (Pollack's estimate; supplied as a hypothesis)
```

Everything above the dashed input is proved here unconditionally; the single remaining
analytic input is the density-zero statement for the abundant members, which is the weakest
hypothesis from which the full theorem follows (it is implied by, and here shown to imply,
the full statement).  The density-zero theorem itself is therefore *not* claimed.
-/

namespace Brockian.BetrothedNumbers

/-! ## Counting functions and asymptotic density zero -/

/-- `counting A x` is the number of elements of `A` that are `< x`. -/
noncomputable def counting (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => n ∈ A)).card

/-- A set of naturals has asymptotic density zero. -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Filter.Tendsto (fun x : ℕ => (counting A x : ℝ) / (x : ℝ)) Filter.atTop (nhds 0)

/-- Counting is monotone in the set. -/
theorem counting_mono {A B : Set ℕ} (h : A ⊆ B) (x : ℕ) : counting A x ≤ counting B x :=
  Finset.card_le_card (by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, h ha.2⟩)

/-- The counting function of a set is at most the length of the interval. -/
theorem counting_le (A : Set ℕ) (x : ℕ) : counting A x ≤ x := by
  simpa [counting] using Finset.card_filter_le (Finset.range x) (fun n => n ∈ A)

/-- If `A` is counted by a constant multiple of a density-zero set, then `A` has density zero. -/
theorem hasDensityZero_of_counting_le_const_mul {A B : Set ℕ} (c : ℕ)
    (h : ∀ x, counting A x ≤ c * counting B x) (hB : HasDensityZero B) :
    HasDensityZero A := by
  have hc : Filter.Tendsto (fun x : ℕ => (c : ℝ) * ((counting B x : ℝ) / (x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hB.const_mul (c : ℝ)
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) hc
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [mul_div_assoc']
    gcongr
    exact_mod_cast h x

/-- A subset of a density-zero set has density zero. -/
theorem hasDensityZero_subset {A B : Set ℕ} (h : A ⊆ B) (hB : HasDensityZero B) :
    HasDensityZero A :=
  hasDensityZero_of_counting_le_const_mul 1 (fun x => by simpa using counting_mono h x) hB

/-! ## Betrothed numbers -/

/-- `m` and `n` form a betrothed (quasi-amicable) pair: they are distinct positive integers,
each of which is the sum of the nontrivial proper divisors of the other, equivalently
`σ m = σ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- The set of betrothed numbers: those belonging to some betrothed pair. -/
def betrothedSet : Set ℕ := {n : ℕ | ∃ m : ℕ, IsBetrothedPair n m}

/-- The partner of a betrothed number `n`, namely `σ n - n - 1`. -/
noncomputable def partner (n : ℕ) : ℕ := σ 1 n - n - 1

/-- The "abundant side" of the betrothed pairs, described purely in terms of `σ`:
`n` is positive, satisfies `σ n > 2n + 1`, and `σ (σ n - n - 1) = σ n`. -/
def lowBetrothedSet : Set ℕ :=
  {n : ℕ | 0 < n ∧ 2 * n + 1 < σ 1 n ∧ σ 1 (σ 1 n - n - 1) = σ 1 n}

/-- The smallest betrothed pair: `(48, 75)`. This witnesses that the notion is not vacuous. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · simp only [ArithmeticFunction.sigma_one_apply]
      decide

/-- A second betrothed pair: `(140, 195)`. -/
theorem isBetrothedPair_140_195 : IsBetrothedPair 140 195 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · simp only [ArithmeticFunction.sigma_one_apply]
      decide

/-- The partner of a betrothed number is uniquely determined by `σ`. -/
theorem partner_eq {m n : ℕ} (h : IsBetrothedPair n m) : partner n = m := by
  obtain ⟨hn, hm, _, h1, _⟩ := h
  simp only [partner, h1]
  omega

/-- Being a betrothed pair is a symmetric relation. -/
theorem isBetrothedPair_symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  exact ⟨hn, hm, hne.symm, by omega, by omega⟩

/-- Membership in the abundant side of a betrothed pair, unfolded. -/
theorem mem_lowBetrothedSet_iff {n : ℕ} :
    n ∈ lowBetrothedSet ↔ ∃ m : ℕ, IsBetrothedPair n m ∧ n < m := by
  constructor
  · rintro ⟨hn, habund, hsig⟩
    exact ⟨σ 1 n - n - 1, ⟨hn, by omega, by omega, by omega, by omega⟩, by omega⟩
  · rintro ⟨m, ⟨hn, hm, hne, h1, h2⟩, hlt⟩
    refine ⟨hn, by omega, ?_⟩
    have hm' : σ 1 n - n - 1 = m := by omega
    rw [hm', h2, h1]

/-- The abundant members of betrothed pairs are betrothed numbers. -/
theorem lowBetrothedSet_subset : lowBetrothedSet ⊆ betrothedSet := by
  intro n hn
  obtain ⟨m, hpair, _⟩ := mem_lowBetrothedSet_iff.mp hn
  exact ⟨m, hpair⟩

/-- The partner map is an involution on the betrothed numbers. -/
theorem partner_partner {n : ℕ} (h : n ∈ betrothedSet) : partner (partner n) = n := by
  obtain ⟨m, hpair⟩ := h
  rw [partner_eq hpair]
  exact partner_eq (isBetrothedPair_symm hpair)

/-- The key counting inequality: since the partner map is an involution exchanging the two
members of a pair, at most half of the betrothed numbers below `x` are deficient members. -/
theorem counting_betrothed_le (x : ℕ) :
    counting betrothedSet x ≤ 2 * counting lowBetrothedSet x := by
  classical
  have hLF : (Finset.range x).filter (fun n => n ∈ lowBetrothedSet)
      ⊆ (Finset.range x).filter (fun n => n ∈ betrothedSet) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, lowBetrothedSet_subset ha.2⟩
  have hkey : (((Finset.range x).filter (fun n => n ∈ betrothedSet)) \
      ((Finset.range x).filter (fun n => n ∈ lowBetrothedSet))).card
      ≤ ((Finset.range x).filter (fun n => n ∈ lowBetrothedSet)).card := by
    apply Finset.card_le_card_of_injOn partner
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hn ⊢
      obtain ⟨⟨hx, m, hpair⟩, hnot⟩ := hn
      have hnl : ¬ (n < m) := fun hlt =>
        hnot ⟨hx, mem_lowBetrothedSet_iff.mpr ⟨m, hpair, hlt⟩⟩
      have hne : m ≠ n := (hpair.2.2.1).symm
      have hmn : m < n := by omega
      have hpe : partner n = m := partner_eq hpair
      rw [hpe]
      exact ⟨by omega, mem_lowBetrothedSet_iff.mpr ⟨n, isBetrothedPair_symm hpair, hmn⟩⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at ha hb
      rw [← partner_partner ha.1.2, ← partner_partner hb.1.2, hab]
  have hcard := Finset.card_sdiff_add_card_eq_card hLF
  simp only [counting]
  omega

/-- **Density zero reduction for betrothed numbers.**
Pollack's theorem that the betrothed (quasi-amicable) numbers have asymptotic density zero
follows from the corresponding statement for the abundant member of each pair, i.e. for the
purely `σ`-arithmetically defined set `lowBetrothedSet`. -/
theorem density_zero_reduction (hPollack : HasDensityZero lowBetrothedSet) :
    HasDensityZero betrothedSet :=
  hasDensityZero_of_counting_le_const_mul 2 counting_betrothed_le hPollack

/-- The reduction is lossless: the two density-zero statements are equivalent. -/
theorem hasDensityZero_betrothedSet_iff :
    HasDensityZero betrothedSet ↔ HasDensityZero lowBetrothedSet :=
  ⟨fun h => hasDensityZero_subset lowBetrothedSet_subset h, density_zero_reduction⟩

end Brockian.BetrothedNumbers

