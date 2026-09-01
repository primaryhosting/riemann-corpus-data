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

namespace Frontier

/-- **Expander mixing lemma.**

Let `A` be a symmetric `d`-regular weighted adjacency matrix on a nonempty finite vertex
set `V` (each row sums to `d`), and suppose `lam ≥ 0` bounds the bilinear form of `A` on
vectors orthogonal to the all-ones vector:
`|xᵀ A y| ≤ lam ‖x‖ ‖y‖` whenever `∑ x = ∑ y = 0`.

Then for all sets of vertices `S`, `T` the number (weight) of edges between `S` and `T`
deviates from the "expected" value `d |S| |T| / |V|` by at most `lam √(|S| |T|)`. -/
theorem wigderson_expander_mixing
    {V : Type*} [Fintype V] (A : Matrix V V ℝ) (d lam : ℝ)
    (hn : 0 < Fintype.card V)
    (hlam0 : 0 ≤ lam)
    (hsym : ∀ i j, A i j = A j i)
    (hreg : ∀ i, ∑ j, A i j = d)
    (hlam : ∀ x y : V → ℝ, ∑ i, x i = 0 → ∑ i, y i = 0 →
      |∑ i, ∑ j, A i j * x i * y j| ≤ lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (S T : Finset V) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / Fintype.card V|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn' : (0:ℝ) < n := by
    rw [hn_def]; exact_mod_cast hn
  set s : ℝ := (S.card : ℝ) with hs_def
  set t : ℝ := (T.card : ℝ) with ht_def
  set x : V → ℝ := fun i => (if i ∈ S then (1:ℝ) else 0) - s / n with hx_def
  set y : V → ℝ := fun j => (if j ∈ T then (1:ℝ) else 0) - t / n with hy_def
  have hIS : ∑ i, (if i ∈ S then (1:ℝ) else 0) = s := by
    simp [hs_def, Finset.sum_ite_mem]
  have hIT : ∑ j, (if j ∈ T then (1:ℝ) else 0) = t := by
    simp [ht_def, Finset.sum_ite_mem]
  have hcard : ((Finset.univ : Finset V).card : ℝ) = n := by
    rw [hn_def]; rfl
  have hsx : ∑ i, x i = 0 := by
    rw [hx_def]
    rw [Finset.sum_sub_distrib, hIS, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hsy : ∑ j, y j = 0 := by
    rw [hy_def]
    rw [Finset.sum_sub_distrib, hIT, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hcol : ∀ j, ∑ i, A i j = d := by
    intro j
    have : ∑ i, A i j = ∑ i, A j i := by
      exact Finset.sum_congr rfl fun i _ => hsym i j
    rw [this, hreg j]
  -- the inner sum against `y`
  have hg : ∀ i, ∑ j, A i j * y j = (∑ j ∈ T, A i j) - t * d / n := by
    intro i
    have h1 : ∀ j, A i j * y j
        = A i j * (if j ∈ T then (1:ℝ) else 0) - (t / n) * A i j := by
      intro j; rw [hy_def]; ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib,
      ← Finset.mul_sum, hreg i]
    congr 1
    · simp [Finset.sum_ite_mem, mul_ite]
    · field_simp
  have hsum_g : ∑ i, (∑ j ∈ T, A i j) = t * d := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun j _ => hcol j), Finset.sum_const, nsmul_eq_mul, ht_def]
  have hxg : ∑ i, x i * (∑ j ∈ T, A i j)
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - (s / n) * (t * d) := by
    have h1 : ∀ i, x i * (∑ j ∈ T, A i j)
        = (if i ∈ S then (1:ℝ) else 0) * (∑ j ∈ T, A i j)
          - (s / n) * (∑ j ∈ T, A i j) := by
      intro i; rw [hx_def]; ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsum_g]
    congr 1
    simp [Finset.sum_ite_mem, ite_mul]
  have hmain : ∑ i, ∑ j, A i j * x i * y j
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - d * s * t / n := by
    have h1 : ∀ i, ∑ j, A i j * x i * y j = x i * ∑ j, A i j * y j := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    have h2 : ∀ i, x i * (∑ j, A i j * y j)
        = x i * (∑ j ∈ T, A i j) - (t * d / n) * x i := by
      intro i; rw [hg i]; ring
    rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsx, hxg]
    field_simp
    ring
  -- norms
  have hnormx : ∑ i, x i ^ 2 = s - s ^ 2 / n := by
    have h1 : ∀ i, x i ^ 2 = (if i ∈ S then (1:ℝ) else 0)
        - (2 * (s / n)) * (if i ∈ S then (1:ℝ) else 0) + (s / n) ^ 2 := by
      intro i; rw [hx_def]
      by_cases h : i ∈ S
      · simp [h]
        ring
      · simp [h]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hIS,
      Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hnormy : ∑ j, y j ^ 2 = t - t ^ 2 / n := by
    have h1 : ∀ j, y j ^ 2 = (if j ∈ T then (1:ℝ) else 0)
        - (2 * (t / n)) * (if j ∈ T then (1:ℝ) else 0) + (t / n) ^ 2 := by
      intro j; rw [hy_def]
      by_cases h : j ∈ T
      · simp [h]
        ring
      · simp [h]
    rw [Finset.sum_congr rfl (fun j _ => h1 j)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hIT,
      Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hs0 : (0:ℝ) ≤ s := by positivity
  have ht0 : (0:ℝ) ≤ t := by positivity
  have hxle : Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt s := by
    apply Real.sqrt_le_sqrt
    rw [hnormx]
    have : (0:ℝ) ≤ s ^ 2 / n := by positivity
    linarith
  have hyle : Real.sqrt (∑ j, y j ^ 2) ≤ Real.sqrt t := by
    apply Real.sqrt_le_sqrt
    rw [hnormy]
    have : (0:ℝ) ≤ t ^ 2 / n := by positivity
    linarith
  have key := hlam x y hsx hsy
  rw [hmain] at key
  refine key.trans ?_
  have h1 : lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ j, y j ^ 2)
      ≤ lam * Real.sqrt s * Real.sqrt t := by
    have hA : 0 ≤ lam * Real.sqrt (∑ i, x i ^ 2) := by positivity
    have hB : lam * Real.sqrt (∑ i, x i ^ 2) ≤ lam * Real.sqrt s :=
      mul_le_mul_of_nonneg_left hxle hlam0
    calc lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ j, y j ^ 2)
        ≤ lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hyle hA
      _ ≤ lam * Real.sqrt s * Real.sqrt t :=
          mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg _)
  refine h1.trans ?_
  rw [Real.sqrt_mul hs0, mul_assoc]

end Frontier

