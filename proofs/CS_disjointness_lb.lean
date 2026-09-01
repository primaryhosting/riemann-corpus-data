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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Communication complexity of set disjointness

We set up the standard two-party communication model (protocol trees), prove the
rectangle property of transcripts, and deduce the fooling-set lower bound
`n ≤ depth` for any deterministic protocol computing set disjointness on subsets
of `Fin n`.  We then lift this to public-coin randomized protocols.

Scope of the randomized statement: `CS.disjointness_lb` shows that every
public-coin randomized protocol for set disjointness on `Fin n` whose per-input
error probability `ε` satisfies `ε * 4 ^ n < 1` needs at least `n` bits of
communication.  This covers in particular zero-error (Las Vegas) randomized
protocols.  The constant-error version of the bound (Kalyanasundaram–Schnitger,
Razborov), which needs the corruption/information-complexity machinery, is *not*
formalized here.
-/

namespace CS

universe u v

variable {X : Type u} {Y : Type v}

/-- A deterministic two-party communication protocol with Boolean output:
a binary tree whose internal nodes are labelled by the party that speaks
(`alice` sends a bit depending on her input `x`, `bob` on his input `y`). -/
inductive Protocol (X : Type u) (Y : Type v) where
  | leaf (o : Bool) : Protocol X Y
  | alice (f : X → Bool) (a b : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (a b : Protocol X Y) : Protocol X Y

namespace Protocol

/-- The communication cost (worst-case number of exchanged bits) of a protocol. -/
def depth : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ a b => 1 + max a.depth b.depth
  | bob _ a b => 1 + max a.depth b.depth

/-- The output of the protocol on a pair of inputs. -/
def run : Protocol X Y → X → Y → Bool
  | leaf o, _, _ => o
  | alice f a b, x, y => if f x then a.run x y else b.run x y
  | bob g a b, x, y => if g y then a.run x y else b.run x y

/-- The transcript (sequence of exchanged bits) of the protocol on a pair of inputs. -/
def transcript : Protocol X Y → X → Y → List Bool
  | leaf _, _, _ => []
  | alice f a b, x, y => f x :: (if f x then a.transcript x y else b.transcript x y)
  | bob g a b, x, y => g y :: (if g y then a.transcript x y else b.transcript x y)

/-- The (finite) set of all transcripts that a protocol can possibly produce. -/
def paths : Protocol X Y → Finset (List Bool)
  | leaf _ => {[]}
  | alice _ a b => a.paths.image (List.cons true) ∪ b.paths.image (List.cons false)
  | bob _ a b => a.paths.image (List.cons true) ∪ b.paths.image (List.cons false)

theorem transcript_mem_paths (p : Protocol X Y) (x : X) (y : Y) :
    p.transcript x y ∈ p.paths := by
  induction p with
  | leaf o => simp [transcript, paths]
  | alice f a b iha ihb =>
      by_cases h : f x = true <;> simp [transcript, paths, h, iha, ihb]
  | bob g a b iha ihb =>
      by_cases h : g y = true <;> simp [transcript, paths, h, iha, ihb]

theorem card_paths_le (p : Protocol X Y) : p.paths.card ≤ 2 ^ p.depth := by
  induction p with
  | leaf o => simp [paths, depth]
  | alice f a b iha ihb =>
      refine le_trans (Finset.card_union_le _ _) ?_
      refine le_trans (add_le_add (Finset.card_image_le) (Finset.card_image_le)) ?_
      have h1 : (2 : ℕ) ^ a.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ b.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hsum : a.paths.card + b.paths.card
          ≤ 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) :=
        add_le_add (iha.trans h1) (ihb.trans h2)
      have hpow : (2 : ℕ) ^ (1 + max a.depth b.depth)
          = 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) := by
        rw [pow_add]; ring
      simpa [depth, hpow] using hsum
  | bob g a b iha ihb =>
      refine le_trans (Finset.card_union_le _ _) ?_
      refine le_trans (add_le_add (Finset.card_image_le) (Finset.card_image_le)) ?_
      have h1 : (2 : ℕ) ^ a.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ b.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hsum : a.paths.card + b.paths.card
          ≤ 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) :=
        add_le_add (iha.trans h1) (ihb.trans h2)
      have hpow : (2 : ℕ) ^ (1 + max a.depth b.depth)
          = 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) := by
        rw [pow_add]; ring
      simpa [depth, hpow] using hsum

/-- The transcript determines the output. -/
theorem run_eq_of_transcript_eq (p : Protocol X Y) {x x' : X} {y y' : Y}
    (h : p.transcript x y = p.transcript x' y') : p.run x y = p.run x' y' := by
  induction p with
  | leaf o => rfl
  | alice f a b iha ihb =>
      simp only [transcript] at h
      have hhd : f x = f x' := (List.cons.inj h).1
      have htl := (List.cons.inj h).2
      by_cases hx : f x = true
      · have hx' : f x' = true := hhd ▸ hx
        simp only [hx, hx', if_true] at htl
        simp only [run, hx, hx', if_true]
        exact iha htl
      · have hx0 : f x = false := by simpa using hx
        have hx' : f x' = false := hhd ▸ hx0
        simp only [hx0, hx', Bool.false_eq_true, if_false] at htl
        simp only [run, hx0, hx', Bool.false_eq_true, if_false]
        exact ihb htl
  | bob g a b iha ihb =>
      simp only [transcript] at h
      have hhd : g y = g y' := (List.cons.inj h).1
      have htl := (List.cons.inj h).2
      by_cases hy : g y = true
      · have hy' : g y' = true := hhd ▸ hy
        simp only [hy, hy', if_true] at htl
        simp only [run, hy, hy', if_true]
        exact iha htl
      · have hy0 : g y = false := by simpa using hy
        have hy' : g y' = false := hhd ▸ hy0
        simp only [hy0, hy', Bool.false_eq_true, if_false] at htl
        simp only [run, hy0, hy', Bool.false_eq_true, if_false]
        exact ihb htl

/-- **Rectangle property**: the set of inputs producing a given transcript is a
combinatorial rectangle. -/
theorem transcript_rectangle (p : Protocol X Y) {x x' : X} {y y' : Y}
    (h : p.transcript x y = p.transcript x' y') : p.transcript x y' = p.transcript x y := by
  induction p with
  | leaf o => rfl
  | alice f a b iha ihb =>
      simp only [transcript] at h ⊢
      have hhd : f x = f x' := (List.cons.inj h).1
      have htl := (List.cons.inj h).2
      by_cases hx : f x = true
      · have hx' : f x' = true := hhd ▸ hx
        simp only [hx, hx', if_true] at htl ⊢
        exact congrArg _ (iha htl)
      · have hx0 : f x = false := by simpa using hx
        have hx' : f x' = false := hhd ▸ hx0
        simp only [hx0, hx', Bool.false_eq_true, if_false] at htl ⊢
        exact congrArg _ (ihb htl)
  | bob g a b iha ihb =>
      simp only [transcript] at h ⊢
      have hhd : g y = g y' := (List.cons.inj h).1
      have htl := (List.cons.inj h).2
      by_cases hy : g y = true
      · have hy' : g y' = true := hhd ▸ hy
        simp only [hy, hy', if_true] at htl ⊢
        exact congrArg _ (iha htl)
      · have hy0 : g y = false := by simpa using hy
        have hy' : g y' = false := hhd ▸ hy0
        simp only [hy0, hy', Bool.false_eq_true, if_false] at htl ⊢
        exact congrArg _ (ihb htl)

end Protocol

/-- A protocol *computes set disjointness* on `Fin n` if on every pair of subsets
it outputs whether they are disjoint. -/
def ComputesDisj (n : ℕ) (p : Protocol (Finset (Fin n)) (Finset (Fin n))) : Prop :=
  ∀ x y : Finset (Fin n), p.run x y = decide (Disjoint x y)

/-- The fooling set `{(x, xᶜ) : x ⊆ [n]}` has `2 ^ n` pairwise distinct transcripts. -/
theorem transcript_compl_injective {n : ℕ} {p : Protocol (Finset (Fin n)) (Finset (Fin n))}
    (hp : ComputesDisj n p) :
    Function.Injective (fun x : Finset (Fin n) => p.transcript x xᶜ) := by
  intro x x' h
  by_contra hne
  -- some element separates `x` from `x'`
  have hsep : (∃ i, i ∈ x ∧ i ∉ x') ∨ (∃ i, i ∈ x' ∧ i ∉ x) := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    exact hne (Finset.Subset.antisymm (fun i hi => h1 i hi) (fun i hi => h2 i hi))
  simp only at h
  have key : ∀ (u v : Finset (Fin n)), p.transcript u uᶜ = p.transcript v vᶜ →
      ∀ i, i ∈ u → i ∉ v → False := by
    intro u v huv i hiu hiv
    have hr : p.transcript u vᶜ = p.transcript u uᶜ := p.transcript_rectangle huv
    have hrun : p.run u vᶜ = p.run u uᶜ := p.run_eq_of_transcript_eq hr
    have h1 : p.run u uᶜ = true := by
      rw [hp u uᶜ]; exact decide_eq_true disjoint_compl_right
    have h2 : ¬ Disjoint u vᶜ := by
      intro hd
      have : i ∈ (∅ : Finset (Fin n)) := by
        have := Finset.disjoint_left.mp hd hiu
        exact absurd (Finset.mem_compl.mpr hiv) this
      simp at this
    have h3 : p.run u vᶜ = false := by
      rw [hp u vᶜ]; simpa using h2
    rw [h3, h1] at hrun
    exact Bool.false_ne_true hrun
  rcases hsep with ⟨i, hi1, hi2⟩ | ⟨i, hi1, hi2⟩
  · exact key x x' h i hi1 hi2
  · exact key x' x h.symm i hi1 hi2

/-- **Deterministic lower bound.** Every deterministic protocol computing set
disjointness on subsets of an `n`-element universe must communicate at least `n`
bits (fooling-set / rectangle argument). -/
theorem deterministic_disjointness_lb (n : ℕ) (p : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hp : ComputesDisj n p) : n ≤ p.depth := by
  have hcard : (2 : ℕ) ^ n ≤ p.paths.card := by
    have himg : (Finset.univ : Finset (Finset (Fin n))).card ≤ p.paths.card := by
      refine Finset.card_le_card_of_injOn (fun x => p.transcript x xᶜ) (fun x _ => ?_) ?_
      · exact p.transcript_mem_paths x xᶜ
      · intro a _ b _ hab
        exact transcript_compl_injective hp hab
    simpa [Finset.card_univ, Fintype.card_finset] using himg
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ p.depth := hcard.trans p.card_paths_le
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-!
### Randomized protocols

A public-coin randomized protocol is a probability distribution `w` over
deterministic protocols `p r`.  Its cost is the worst-case depth, and its error
on an input is the total weight of the coin values on which it errs.
-/

/-- **Randomized lower bound for set disjointness.**
Any public-coin randomized protocol which computes set disjointness on subsets of
`Fin n` with per-input error probability at most `ε`, where `ε` is small enough
that `ε · 4 ^ n < 1`, must have communication cost at least `n`.  In particular
this covers zero-error (Las Vegas) randomized protocols. -/
theorem disjointness_lb (n c : ℕ) {R : Type} [Fintype R] [DecidableEq R]
    (w : R → ℝ) (hw0 : ∀ r, 0 ≤ w r) (hw1 : ∑ r, w r = 1)
    (p : R → Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hdepth : ∀ r, (p r).depth ≤ c)
    (ε : ℝ)
    (herr : ∀ x y : Finset (Fin n),
      ∑ r ∈ Finset.univ.filter (fun r => (p r).run x y ≠ decide (Disjoint x y)), w r ≤ ε)
    (hsmall : ε * 4 ^ n < 1) : n ≤ c := by
  classical
  -- Some coin value gives a protocol correct on *all* inputs.
  have hex : ∃ r : R, ComputesDisj n (p r) := by
    by_contra hc
    push_neg at hc
    -- pick, for each `r`, a bad input pair
    have hbad : ∀ r : R, ∃ q : Finset (Fin n) × Finset (Fin n),
        (p r).run q.1 q.2 ≠ decide (Disjoint q.1 q.2) := by
      intro r
      obtain ⟨x, hx⟩ := not_forall.mp (hc r)
      obtain ⟨y, hy⟩ := not_forall.mp hx
      exact ⟨(x, y), hy⟩
    choose φ hφ using hbad
    set S : Finset (Finset (Fin n) × Finset (Fin n)) := Finset.univ with hS
    have hmaps : ∀ r ∈ (Finset.univ : Finset R), φ r ∈ S := by intro r _; simp [hS]
    have hsplit : ∑ r, w r
        = ∑ q ∈ S, ∑ r ∈ Finset.univ.filter (fun r => φ r = q), w r :=
      (Finset.sum_fiberwise_of_maps_to hmaps w).symm
    have hle : ∀ q ∈ S, ∑ r ∈ Finset.univ.filter (fun r => φ r = q), w r ≤ ε := by
      intro q _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hw0 i)) (herr q.1 q.2)
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      subst hr
      exact hφ r
    have hsum : (1 : ℝ) ≤ (S.card : ℝ) * ε := by
      calc (1 : ℝ) = ∑ r, w r := hw1.symm
        _ = ∑ q ∈ S, ∑ r ∈ Finset.univ.filter (fun r => φ r = q), w r := hsplit
        _ ≤ ∑ _q ∈ S, ε := Finset.sum_le_sum hle
        _ = (S.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℝ) = 4 ^ n := by
      have : S.card = 2 ^ n * 2 ^ n := by
        simp [hS, Finset.card_univ, Fintype.card_prod, Fintype.card_finset]
      rw [this]
      push_cast
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    rw [hcard] at hsum
    nlinarith [hsum, hsmall]
  obtain ⟨r, hr⟩ := hex
  exact (deterministic_disjointness_lb n (p r) hr).trans (hdepth r)

end CS

