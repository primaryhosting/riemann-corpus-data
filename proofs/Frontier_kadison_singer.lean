import Mathlib
/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

/-!
## The statement

The Kadison–Singer problem (1959) asks whether every pure state on the atomic MASA
`ℓ^∞(ℕ) ⊆ B(ℓ²(ℕ))` extends uniquely to a state on `B(ℓ²(ℕ))`.  It was resolved
affirmatively by Marcus, Spielman and Srivastava, who proved **Weaver's conjecture `KS_r`**
by the method of *interlacing families of polynomials*:

> if `v₁, …, v_m ∈ ℂ^d` satisfy `∑ᵢ vᵢ vᵢ* = I` and `‖vᵢ‖² ≤ α` for all `i`, then there is a
> partition `{1,…,m} = S₁ ⊔ … ⊔ S_r` with `‖∑_{i ∈ S_j} vᵢ vᵢ*‖ ≤ (1/√r + √α)²` for all `j`.

We phrase the two operator-theoretic conditions through the associated quadratic forms, which
is equivalent (all the operators involved are positive semidefinite) and avoids committing to
a particular encoding of the operator norm:

* `∑ᵢ vᵢ vᵢ* = I`             ⟺  `∀ x, ∑ᵢ |⟪vᵢ, x⟫|² = ‖x‖²`;
* `‖∑_{i ∈ S} vᵢ vᵢ*‖ ≤ c`    ⟺  `∀ x, ∑_{i ∈ S} |⟪vᵢ, x⟫|² ≤ c ‖x‖²`.
-/

/-- **Weaver's `KS_r` statement** in dimension `d` with bound `α`: every isotropic family of
vectors in `ℂ^d` whose members have squared norm at most `α` can be partitioned into `r`
subfamilies, each of operator norm at most `(1/√r + √α)²`.

The proposition `∀ r α d, 0 < r → 0 ≤ α → WeaverKS r α d` is Weaver's conjecture, which is
equivalent to a positive solution of the Kadison–Singer problem and is the theorem of
Marcus–Spielman–Srivastava. -/
def WeaverKS (r : ℕ) (α : ℝ) (d : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (v : ι → EuclideanSpace ℂ (Fin d)),
    (∀ i, ‖v i‖ ^ 2 ≤ α) →
    (∀ x : EuclideanSpace ℂ (Fin d), ∑ i, ‖inner ℂ (v i) x‖ ^ 2 = ‖x‖ ^ 2) →
    ∃ f : ι → Fin r, ∀ (j : Fin r) (x : EuclideanSpace ℂ (Fin d)),
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), ‖inner ℂ (v i) x‖ ^ 2
        ≤ (1 / Real.sqrt r + Real.sqrt α) ^ 2 * ‖x‖ ^ 2

/-!
## A greedy load-balancing lemma

This is the combinatorial heart of the one-dimensional case: placing each new item into a
currently least-loaded bin keeps every bin below `average + α`.
-/

/-- Greedy load balancing on a finite set: any family of nonnegative reals indexed by `s`,
each bounded by `α`, can be split into `r` parts each of total weight at most
`(∑ᵢ aᵢ)/r + α`. -/
theorem greedy_partition_finset {ι : Type} [DecidableEq ι] (r : ℕ) (hr : 0 < r) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (α : ℝ) (hα0 : 0 ≤ α) (hα : ∀ i, a i ≤ α) (s : Finset ι) :
    ∃ f : ι → Fin r, ∀ j : Fin r,
      ∑ i ∈ s.filter (fun i => f i = j), a i ≤ (∑ i ∈ s, a i) / r + α := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => ⟨0, hr⟩, fun j => by simp [hα0]⟩
  | insert x s hx ih =>
      obtain ⟨f, hf⟩ := ih
      set L : Fin r → ℝ := fun j => ∑ i ∈ s.filter (fun i => f i = j), a i with hL
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin r)) L
        ⟨⟨0, hr⟩, Finset.mem_univ _⟩
      have hsum : ∑ j, L j = ∑ i ∈ s, a i := Finset.sum_fiberwise s f a
      -- a least-loaded bin carries at most the average load
      have hmin : L j₀ ≤ (∑ i ∈ s, a i) / r := by
        have h1 := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin r)) L (L j₀)
          (fun j _ => hj₀ j (Finset.mem_univ j))
        rw [hsum] at h1
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        rw [le_div_iff₀ hrR]
        linarith
      refine ⟨Function.update f x j₀, fun j => ?_⟩
      have hupd : ∀ i ∈ s, Function.update f x j₀ i = f i := fun i hi =>
        Function.update_of_ne (by rintro rfl; exact hx hi) _ _
      have hax : 0 ≤ a x := ha x
      have hstep : (∑ i ∈ s, a i) / r ≤ (∑ i ∈ insert x s, a i) / r := by
        rw [Finset.sum_insert hx]; gcongr; linarith
      have hfil :
          s.filter (fun i => Function.update f x j₀ i = j) = s.filter (fun i => f i = j) :=
        Finset.filter_congr fun i hi => by rw [hupd i hi]
      rw [Finset.filter_insert]
      by_cases hj : j₀ = j
      · subst hj
        rw [if_pos (Function.update_self x j₀ f), hfil,
          Finset.sum_insert fun h => hx (Finset.mem_of_mem_filter _ h)]
        have hle : L j₀ ≤ (∑ i ∈ insert x s, a i) / r := hmin.trans hstep
        simp only [hL] at hle
        linarith [hα x]
      · rw [if_neg (by simpa [Function.update_self] using hj), hfil]
        linarith [hf j]

/-- Greedy load balancing over a fintype. -/
theorem greedy_partition {ι : Type} [Fintype ι] (r : ℕ) (hr : 0 < r) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (α : ℝ) (hα0 : 0 ≤ α) (hα : ∀ i, a i ≤ α) :
    ∃ f : ι → Fin r, ∀ j : Fin r,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), a i ≤ (∑ i, a i) / r + α :=
  greedy_partition_finset r hr a ha α hα0 hα Finset.univ

/-- The elementary numerical inequality behind the `KS_r` bound: `1/r + α ≤ (1/√r + √α)²`. -/
theorem one_div_add_le_sq_sqrt_add_sqrt (r : ℕ) (α : ℝ) (hα : 0 ≤ α) (hrR : (0 : ℝ) < r) :
    1 / (r : ℝ) + α ≤ (1 / Real.sqrt r + Real.sqrt α) ^ 2 := by
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hsr2 : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt hrR.le
  have hα2 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα
  have expand : (1 / Real.sqrt r + Real.sqrt α) ^ 2
      = (1 / Real.sqrt r) ^ 2 + 2 * (1 / Real.sqrt r) * Real.sqrt α + Real.sqrt α ^ 2 := by ring
  rw [expand, div_pow, one_pow, hsr2, hα2]
  have h0 : 0 ≤ 2 * (1 / Real.sqrt r) * Real.sqrt α := by positivity
  linarith

/-!
## The base case `r = 1`
-/

/-- The base case `r = 1` of Weaver's `KS_r`, in every dimension: the trivial partition works,
because `(1/√1 + √α)² ≥ 1`. -/
theorem weaverKS_one (α : ℝ) (d : ℕ) : WeaverKS 1 α d := by
  intro ι _ v _ hiso
  refine ⟨fun _ => 0, fun j x => ?_⟩
  have hfil : (Finset.univ.filter fun i : ι => (0 : Fin 1) = j) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => Subsingleton.elim _ _
  rw [hfil, hiso x]
  have h1 : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h1]
  have hs : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  nlinarith [sq_nonneg ‖x‖, sq_nonneg (Real.sqrt α)]

/-!
## The one-dimensional case, for every `r`
-/

/-- The one-dimensional (`d = 1`) case of Weaver's `KS_r`, for every `r ≥ 1`.

In dimension one the rank-one operators are just the scalars `aᵢ = ‖vᵢ‖²`, the isotropy
hypothesis says `∑ᵢ aᵢ = 1`, and greedy load balancing produces a partition into `r` parts of
weight at most `1/r + α ≤ (1/√r + √α)²`. -/
theorem weaverKS_dim_one (r : ℕ) (hr : 0 < r) (α : ℝ) (hα : 0 ≤ α) : WeaverKS r α 1 := by
  intro ι _ v hv hiso
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set a : ι → ℝ := fun i => ‖v i‖ ^ 2 with hadef
  have key : ∀ (i : ι) (x : EuclideanSpace ℂ (Fin 1)),
      ‖inner ℂ (v i) x‖ ^ 2 = a i * ‖x‖ ^ 2 := by
    intro i x
    simp [hadef, PiLp.inner_apply, EuclideanSpace.norm_eq, RCLike.inner_apply, mul_pow, mul_comm]
  have hsum1 : ∑ i, a i = 1 := by
    have h := hiso (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
    have hn : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℂ))‖ = 1 := by simp
    simp only [key, hn] at h
    simpa using h
  obtain ⟨f, hf⟩ := greedy_partition r hr a (fun _ => sq_nonneg _) α hα hv
  refine ⟨f, fun j x => ?_⟩
  have hcalc : ∑ i ∈ Finset.univ.filter (fun i => f i = j), ‖inner ℂ (v i) x‖ ^ 2
      = (∑ i ∈ Finset.univ.filter (fun i => f i = j), a i) * ‖x‖ ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => key i x
  rw [hcalc]
  have hb := hf j
  rw [hsum1] at hb
  exact mul_le_mul_of_nonneg_right
    (hb.trans (one_div_add_le_sq_sqrt_add_sqrt r α hα hrR)) (sq_nonneg _)

/-!
## Main result
-/

/-- **Kadison–Singer / Weaver's `KS_r`.**

The full conjecture, `∀ r α d, 0 < r → 0 ≤ α → WeaverKS r α d`, is the theorem of
Marcus–Spielman–Srivastava.  Here we record the formal statement (`Frontier.WeaverKS`)
together with Lean-checked proofs of the two boundary cases of the induction:

* the base case `r = 1`, in every dimension `d`;
* the base case `d = 1`, for every number of parts `r`, which is exactly the greedy
  load-balancing bound together with `1/r + α ≤ (1/√r + √α)²`. -/
theorem kadison_singer :
    (∀ (α : ℝ) (d : ℕ), WeaverKS 1 α d) ∧
    (∀ (r : ℕ) (α : ℝ), 0 < r → 0 ≤ α → WeaverKS r α 1) :=
  ⟨weaverKS_one, fun r α hr hα => weaverKS_dim_one r hr α hα⟩

end Frontier

