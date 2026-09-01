/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the `import` line; the required
header is reproduced verbatim below as the module docstring.)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
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

set_option grind.warning false

namespace Frontier

open Finset Set

/-! ## Finite games in normal form -/

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles of a finite game: for each player `i` a probability
distribution on that player's (finite) pure strategy set `S i`. -/
def mixedProfiles (S : ι → Type) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  Set.univ.pi fun i => stdSimplex ℝ (S i)

/-- The expected payoff of player `i` when the players independently randomize
according to the mixed profile `x`. -/
noncomputable def expectedPayoff (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  ∑ p : (∀ i, S i), (∏ j, x j (p j)) * u i p

/-- A mixed profile `x` is a Nash equilibrium if it is a profile of probability distributions
and no player can strictly increase their expected payoff by a unilateral deviation. -/
def IsMixedNashEquilibrium (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : Prop :=
  x ∈ mixedProfiles S ∧
    ∀ i, ∀ y ∈ stdSimplex ℝ (S i),
      expectedPayoff u (Function.update x i y) i ≤ expectedPayoff u x i

end Defs

/-- Brouwer's fixed point theorem, stated as a property (it is not available in Mathlib):
every continuous self-map of a nonempty compact convex subset of a finite-dimensional real
normed space has a fixed point. -/
def BrouwerFixedPointProperty : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E), K.Nonempty → Convex ℝ K → IsCompact K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

section Nash

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
variable (u : ι → (∀ i, S i) → ℝ)

/-- A Dirac measure on a pure strategy is a mixed strategy. -/
lemma single_mem_stdSimplex {α : Type} [Fintype α] [DecidableEq α] (s : α) :
    (Pi.single s (1 : ℝ)) ∈ stdSimplex ℝ α := by
  refine ⟨fun t => ?_, ?_⟩
  · rw [Pi.single_apply]; split <;> norm_num
  · simp

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
lemma prod_update (x : ∀ i, S i → ℝ) (i : ι) (y : S i → ℝ) (p : ∀ i, S i) :
    (∏ j, Function.update x i y j (p j))
      = y (p i) * ∏ j ∈ Finset.univ \ {i}, x j (p j) := by
  have h : (fun j => Function.update x i y j (p j))
      = Function.update (fun j => x j (p j)) i (y (p i)) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [show (∏ j, Function.update x i y j (p j))
      = ∏ j, Function.update (fun j => x j (p j)) i (y (p i)) j from by rw [h]]
  exact Finset.prod_update_of_mem (Finset.mem_univ i) _ _

omit [∀ i, Nonempty (S i)] in
/-- The expected payoff is linear in the deviating player's own mixed strategy. -/
lemma expectedPayoff_update (x : ∀ i, S i → ℝ) (i : ι) (y : S i → ℝ) :
    expectedPayoff u (Function.update x i y) i
      = ∑ s, y s * expectedPayoff u (Function.update x i (Pi.single s 1)) i := by
  simp only [expectedPayoff, prod_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply, mul_assoc]

/-- The expected payoff of a mixed profile is the average of the payoffs of the pure
deviations of any given player. -/
lemma expectedPayoff_eq_sum (x : ∀ i, S i → ℝ) (i : ι) :
    expectedPayoff u x i
      = ∑ s, x i s * expectedPayoff u (Function.update x i (Pi.single s 1)) i := by
  have h := expectedPayoff_update u x i (x i)
  rwa [Function.update_eq_self] at h

omit [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
lemma continuous_expectedPayoff (i : ι) :
    Continuous fun x : (∀ i, S i → ℝ) => expectedPayoff u x i := by
  unfold expectedPayoff
  refine continuous_finset_sum _ fun p _ => Continuous.mul ?_ continuous_const
  exact continuous_finset_prod _ fun j _ => (continuous_apply (p j)).comp (continuous_apply j)

omit [Fintype ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
lemma continuous_update_const (i : ι) (c : S i → ℝ) :
    Continuous fun x : (∀ i, S i → ℝ) => Function.update x i c := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simpa using continuous_const
  · simpa only [Function.update_of_ne h] using continuous_apply j

/-- The gain player `i` would obtain by switching to the pure strategy `s`. -/
noncomputable def gain (x : ∀ i, S i → ℝ) (i : ι) (s : S i) : ℝ :=
  expectedPayoff u (Function.update x i (Pi.single s 1)) i - expectedPayoff u x i

/-- Nash's map: each player shifts weight towards their profitable deviations. -/
noncomputable def nashMap (x : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i s => (x i s + max 0 (gain u x i s)) / (1 + ∑ t, max 0 (gain u x i t))

omit [∀ i, Nonempty (S i)] in
lemma one_le_nashDen (x : ∀ i, S i → ℝ) (i : ι) :
    1 ≤ 1 + ∑ t, max 0 (gain u x i t) := by
  have : (0:ℝ) ≤ ∑ t, max 0 (gain u x i t) :=
    Finset.sum_nonneg fun t _ => le_max_left _ _
  linarith

lemma continuous_gain (i : ι) (s : S i) :
    Continuous fun x : (∀ i, S i → ℝ) => gain u x i s := by
  unfold gain
  exact ((continuous_expectedPayoff u i).comp
    (continuous_update_const i (Pi.single s 1))).sub (continuous_expectedPayoff u i)

lemma continuous_nashMap : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  refine Continuous.div ?_ ?_ ?_
  · exact ((continuous_apply s).comp (continuous_apply i)).add
      ((continuous_const (y := (0:ℝ))).max (continuous_gain u i s))
  · exact continuous_const.add
      (continuous_finset_sum _ fun t _ => (continuous_const (y := (0:ℝ))).max (continuous_gain u i t))
  · intro x
    have := one_le_nashDen u x i
    linarith

lemma mapsTo_nashMap : Set.MapsTo (nashMap u) (mixedProfiles S) (mixedProfiles S) := by
  intro x hx i _
  have hxi : x i ∈ stdSimplex ℝ (S i) := hx i (Set.mem_univ i)
  have hden : (0:ℝ) < 1 + ∑ t, max 0 (gain u x i t) := lt_of_lt_of_le one_pos (one_le_nashDen u x i)
  constructor
  · intro s
    have h1 : 0 ≤ x i s + max 0 (gain u x i s) :=
      add_nonneg (hxi.1 s) (le_max_left _ _)
    exact div_nonneg h1 hden.le
  · show ∑ s, nashMap u x i s = 1
    unfold nashMap
    rw [← Finset.sum_div, Finset.sum_add_distrib, hxi.2]
    field_simp

lemma isNash_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ mixedProfiles S)
    (hfix : nashMap u x = x) : IsMixedNashEquilibrium u x := by
  refine ⟨hx, ?_⟩
  intro i y hy
  have hxi : x i ∈ stdSimplex ℝ (S i) := hx i (Set.mem_univ i)
  set c : ℝ := ∑ t, max 0 (gain u x i t) with hc
  have hcnonneg : 0 ≤ c := Finset.sum_nonneg fun t _ => le_max_left _ _
  have hden : (0:ℝ) < 1 + c := by linarith
  have hkey : ∀ s, x i s * c = max 0 (gain u x i s) := by
    intro s
    have h := congrFun (congrFun hfix i) s
    unfold nashMap at h
    rw [← hc, div_eq_iff (ne_of_gt hden)] at h
    nlinarith [h]
  have hzero : ∑ s, x i s * gain u x i s = 0 := by
    simp only [gain, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hxi.2, one_mul,
      ← expectedPayoff_eq_sum, sub_self]
  have hc0 : c = 0 := by
    by_contra hne
    have hcpos : 0 < c := lt_of_le_of_ne hcnonneg (Ne.symm hne)
    have hterm : ∀ s ∈ Finset.univ, 0 ≤ x i s * gain u x i s := by
      intro s _
      rcases eq_or_lt_of_le (hxi.1 s) with h | h
      · rw [← h]; simp
      · have hm : 0 < max 0 (gain u x i s) := by
          rw [← hkey s]; positivity
        have : 0 < gain u x i s := by
          rcases max_cases 0 (gain u x i s) with ⟨he, _⟩ | ⟨he, hle⟩
          · rw [he] at hm; exact absurd hm (lt_irrefl 0)
          · rw [he] at hm; exact hm
        positivity
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hzero
    have hzeros : ∀ s, x i s = 0 := by
      intro s
      by_contra hs
      have hpos : 0 < x i s := lt_of_le_of_ne (hxi.1 s) (Ne.symm hs)
      have hg : gain u x i s = 0 := by
        have := hall s (Finset.mem_univ s)
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (ne_of_gt hpos)
        · exact h
      have hm : 0 < max 0 (gain u x i s) := by rw [← hkey s]; positivity
      rw [hg] at hm
      simp at hm
    have := hxi.2
    rw [Finset.sum_congr rfl fun s _ => hzeros s] at this
    simp at this
  have hgain : ∀ s, gain u x i s ≤ 0 := by
    intro s
    have := hkey s
    rw [hc0, mul_zero] at this
    have h2 : gain u x i s ≤ max 0 (gain u x i s) := le_max_right _ _
    linarith [this ▸ h2]
  rw [expectedPayoff_update]
  have hle : ∀ s ∈ Finset.univ,
      y s * expectedPayoff u (Function.update x i (Pi.single s 1)) i
        ≤ y s * expectedPayoff u x i := by
    intro s _
    have := hgain s
    unfold gain at this
    exact mul_le_mul_of_nonneg_left (by linarith) (hy.1 s)
  calc ∑ s, y s * expectedPayoff u (Function.update x i (Pi.single s 1)) i
      ≤ ∑ s, y s * expectedPayoff u x i := Finset.sum_le_sum hle
    _ = expectedPayoff u x i := by rw [← Finset.sum_mul, hy.2, one_mul]

/-- **Nash's theorem** (a Lean-checked reduction to Brouwer's fixed point theorem).
Every finite game in normal form — a finite set of players `ι`, a nonempty finite set of pure
strategies `S i` for each player, and an arbitrary real payoff function `u i` on pure strategy
profiles — has a mixed-strategy Nash equilibrium, given Brouwer's fixed point theorem. -/
theorem nash_equilibrium_exists (brouwer : BrouwerFixedPointProperty) :
    ∃ x, IsMixedNashEquilibrium u x := by
  have hne : (mixedProfiles S).Nonempty :=
    ⟨fun i => Pi.single (Classical.arbitrary (S i)) 1, fun i _ => single_mem_stdSimplex _⟩
  have hconv : Convex ℝ (mixedProfiles S) :=
    convex_pi fun i _ => convex_stdSimplex ℝ (S i)
  have hcomp : IsCompact (mixedProfiles S) :=
    isCompact_univ_pi fun i => isCompact_stdSimplex (S i)
  obtain ⟨x, hxK, hfix⟩ := brouwer ((i : ι) → S i → ℝ) (mixedProfiles S) hne hconv hcomp
    (nashMap u) (continuous_nashMap u).continuousOn (mapsTo_nashMap u)
  exact ⟨x, isNash_of_fixed u hxK hfix⟩

end Nash

end Frontier

