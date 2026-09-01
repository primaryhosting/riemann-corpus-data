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

import Brockian.EquidistributionBVReduction

/-!
# Existence of an equidistributed sequence

This file exhibits an explicit sequence which is equidistributed mod one in the sense of
`Brockian.EquidistributionBVReduction.Equidistributed`, so that the hypotheses of
`Brockian.EquidistributionBVReduction.configCount_density_of_BV` are satisfiable.

The sequence is the concatenation of the uniform grids of odd sizes: the `k`-th block consists
of the `2k+1` points `0/(2k+1), 1/(2k+1), …, 2k/(2k+1)`, and it occupies the indices
`k² ≤ n < (k+1)²`.  Since `Nat.sqrt n = k` exactly on that range of indices, the sequence has the
closed form `gridSeq n = (n - (sqrt n)²) / (2 * sqrt n + 1)`.
-/

open scoped BigOperators
open scoped Classical
open Filter Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The concatenation of the uniform grids of odd sizes: the block of indices
`k² ≤ n < (k+1)²` runs through the `2k+1` points `j / (2k+1)`. -/
noncomputable def gridSeq (n : ℕ) : ℝ :=
  ((n - (Nat.sqrt n) ^ 2 : ℕ) : ℝ) / (2 * Nat.sqrt n + 1)

/-- The number of grid points `j / M`, `j < M`, that lie in the window `[a, b)`. -/
noncomputable def blockCount (a b : ℝ) (M : ℕ) : ℕ :=
  ((Finset.range M).filter (fun j : ℕ => ((j : ℝ) / M) ∈ Set.Ico a b)).card

lemma sqrt_block (K j : ℕ) (hj : j < 2 * K + 1) : Nat.sqrt (K ^ 2 + j) = K := by
  have h1 : K ≤ Nat.sqrt (K ^ 2 + j) := by rw [Nat.le_sqrt']; nlinarith
  have h2 : Nat.sqrt (K ^ 2 + j) < K + 1 := by rw [Nat.sqrt_lt']; nlinarith
  omega

lemma gridSeq_nonneg (n : ℕ) : 0 ≤ gridSeq n := by
  unfold gridSeq; positivity

lemma gridSeq_lt_one (n : ℕ) : gridSeq n < 1 := by
  have h : n - (Nat.sqrt n) ^ 2 < 2 * Nat.sqrt n + 1 := by
    have h1 : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
    have h2 : n < Nat.sqrt n ^ 2 + 2 * Nat.sqrt n + 1 := by
      have := Nat.lt_succ_sqrt' n; nlinarith
    omega
  have hM : (0 : ℝ) < 2 * Nat.sqrt n + 1 := by positivity
  rw [gridSeq, div_lt_one hM]
  exact_mod_cast h

lemma fract_gridSeq (n : ℕ) : Int.fract (gridSeq n) = gridSeq n :=
  Int.fract_eq_self.mpr ⟨gridSeq_nonneg n, gridSeq_lt_one n⟩

lemma gridSeq_block (K j : ℕ) (hj : j < 2 * K + 1) :
    gridSeq (K ^ 2 + j) = (j : ℝ) / (2 * K + 1) := by
  rw [gridSeq, sqrt_block K j hj]
  congr 1
  push_cast [Nat.add_sub_cancel_left]
  ring

/-- The grid of `M` equally spaced points meets a window `[a, b) ⊆ [0,1]` in `M * (b - a)`
points, up to an error of at most one point. -/
lemma abs_blockCount_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {M : ℕ}
    (hM : 0 < M) : |(blockCount a b M : ℝ) - M * (b - a)| ≤ 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hfil : ((Finset.range M).filter (fun j : ℕ => ((j : ℝ) / M) ∈ Set.Ico a b))
      = Finset.Ico ⌈(M : ℝ) * a⌉₊ ⌈(M : ℝ) * b⌉₊ := by
    have hbM : ⌈(M : ℝ) * b⌉₊ ≤ M := by
      rw [Nat.ceil_le]; nlinarith
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨_, h1, h2⟩
      refine ⟨Nat.ceil_le.mpr ?_, Nat.lt_ceil.mpr ?_⟩
      · rw [le_div_iff₀ hM'] at h1; linarith
      · rw [div_lt_iff₀ hM'] at h2; linarith
    · rintro ⟨h1, h2⟩
      have h1' : (M : ℝ) * a ≤ j := Nat.ceil_le.mp h1
      have h2' : (j : ℝ) < (M : ℝ) * b := Nat.lt_ceil.mp h2
      refine ⟨lt_of_lt_of_le h2 hbM, ?_, ?_⟩
      · rw [le_div_iff₀ hM']; linarith
      · rw [div_lt_iff₀ hM']; linarith
  have hmono : ⌈(M : ℝ) * a⌉₊ ≤ ⌈(M : ℝ) * b⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  rw [blockCount, hfil, Nat.card_Ico, Nat.cast_sub hmono]
  have h1 := Nat.le_ceil ((M : ℝ) * a)
  have h2 := Nat.le_ceil ((M : ℝ) * b)
  have h3 := Nat.ceil_lt_add_one (a := (M : ℝ) * a) (by positivity)
  have h4 := Nat.ceil_lt_add_one (a := (M : ℝ) * b) (by nlinarith)
  rw [abs_le]
  constructor <;> nlinarith

/-- The count over a full range of blocks is the sum of the block counts. -/
lemma windowCount_gridSeq_sq (a b : ℝ) (K : ℕ) :
    windowCount gridSeq a b (K ^ 2) = ∑ k ∈ Finset.range K, blockCount a b (2 * k + 1) := by
  have hcard : ∀ (N : ℕ), windowCount gridSeq a b N
      = ∑ n ∈ Finset.range N, if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0 := by
    intro N; rw [windowCount, Finset.card_filter]
  induction K with
  | zero => simp [windowCount, blockCount]
  | succ K ih =>
    have hle : K ^ 2 ≤ (K + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ K) 2
    have hlen : (K + 1) ^ 2 - K ^ 2 = 2 * K + 1 := by ring_nf; omega
    have hsplit : ∑ n ∈ Finset.range ((K + 1) ^ 2),
          (if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0)
        = (∑ n ∈ Finset.range (K ^ 2), if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0)
          + ∑ n ∈ Finset.Ico (K ^ 2) ((K + 1) ^ 2),
              if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0 := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle]
    rw [Finset.sum_range_succ, ← ih, hcard, hcard, hsplit]
    congr 1
    rw [blockCount, Finset.card_filter, Finset.sum_Ico_eq_sum_range, hlen]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < 2 * K + 1 := Finset.mem_range.mp hj
    rw [fract_gridSeq, gridSeq_block K j hj']
    push_cast
    ring_nf

/-- Over the first `K²` terms the window count is `K² (b-a)` up to an error `K`. -/
lemma abs_windowCount_sq_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (K : ℕ) :
    |(windowCount gridSeq a b (K ^ 2) : ℝ) - (K : ℝ) ^ 2 * (b - a)| ≤ K := by
  have hsum : ∀ J : ℕ, ∑ k ∈ Finset.range J, ((2 * k + 1 : ℕ) : ℝ) = (J : ℝ) ^ 2 := by
    intro J
    induction J with
    | zero => simp
    | succ J ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [windowCount_gridSeq_sq]
  push_cast
  have hrw : (∑ k ∈ Finset.range K, (blockCount a b (2 * k + 1) : ℝ)) - (K : ℝ) ^ 2 * (b - a)
      = ∑ k ∈ Finset.range K,
          ((blockCount a b (2 * k + 1) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) * (b - a)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  rw [hrw]
  calc |∑ k ∈ Finset.range K,
          ((blockCount a b (2 * k + 1) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) * (b - a))|
      ≤ ∑ k ∈ Finset.range K,
          |(blockCount a b (2 * k + 1) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) * (b - a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => abs_blockCount_sub_le ha hab hb (Nat.succ_pos _))
    _ = K := by simp

lemma windowCount_mono (x : ℕ → ℝ) (a b : ℝ) {N N' : ℕ} (h : N ≤ N') :
    windowCount x a b N ≤ windowCount x a b N' := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact fun y hy => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hy) h)

/-- The window count of the first `N` terms is `N (b-a)` up to an error `3√N + 2`. -/
lemma abs_windowCount_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N : ℕ) :
    |(windowCount gridSeq a b N : ℝ) - N * (b - a)| ≤ 3 * Nat.sqrt N + 2 := by
  set K := Nat.sqrt N
  have hd0 : 0 ≤ b - a := by linarith
  have hd1 : b - a ≤ 1 := by linarith
  have hKN : K ^ 2 ≤ N := Nat.sqrt_le' N
  have hNK : N < (K + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hKN' : ((K : ℝ)) ^ 2 ≤ N := by exact_mod_cast hKN
  have hNK' : (N : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := by
    have : (N : ℝ) < ((K + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hNK
    push_cast at this
    linarith
  have hlow : (windowCount gridSeq a b (K ^ 2) : ℝ) ≤ (windowCount gridSeq a b N : ℝ) := by
    exact_mod_cast windowCount_mono gridSeq a b hKN
  have hupp : (windowCount gridSeq a b N : ℝ) ≤ (windowCount gridSeq a b ((K + 1) ^ 2) : ℝ) := by
    exact_mod_cast windowCount_mono gridSeq a b hNK.le
  have h1 := abs_le.mp (abs_windowCount_sq_sub_le ha hab hb K)
  have h2 := abs_le.mp (abs_windowCount_sq_sub_le ha hab hb (K + 1))
  have hcast : (((K + 1 : ℕ)) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h2
  have hKnn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The explicit sequence `gridSeq` is equidistributed mod one. -/
theorem equidistributed_gridSeq : Equidistributed gridSeq := by
  intro a b ha hab hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (6 / ε)
  refine ⟨(K₀ + 1) ^ 2, fun N hN => ?_⟩
  set K := Nat.sqrt N
  have hK1 : K₀ + 1 ≤ K := Nat.le_sqrt'.mpr hN
  have hKpos : 0 < K := by omega
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have hK0R : 6 / ε < (K : ℝ) := by
    refine lt_of_lt_of_le hK₀ ?_
    exact_mod_cast (by omega : K₀ ≤ K)
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hKN' : ((K : ℝ)) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hbound := abs_windowCount_sub_le ha hab hb N
  rw [Real.dist_eq]
  have heq : (windowCount gridSeq a b N : ℝ) / N - (b - a)
      = ((windowCount gridSeq a b N : ℝ) - N * (b - a)) / N := by field_simp
  rw [heq, abs_div, abs_of_pos hNR, div_lt_iff₀ hNR]
  have h6 : 6 < ε * K := by
    rw [div_lt_iff₀ hε] at hK0R; linarith
  have hεK : 6 * (K : ℝ) < ε * (K : ℝ) ^ 2 := by nlinarith
  have hεN : ε * (K : ℝ) ^ 2 ≤ ε * N := by nlinarith
  linarith

/-- Equidistributed sequences exist, so the hypothesis of `configCount_density_of_BV`
is satisfiable. -/
theorem exists_equidistributed : ∃ x : ℕ → ℝ, Equidistributed x :=
  ⟨gridSeq, equidistributed_gridSeq⟩

/-- The bounded-variation reduction, instantiated at the explicit sequence `gridSeq`: for every
weight of bounded variation on `[0,1]` the weighted configuration counts of `gridSeq` have
density `∫₀¹ w`. -/
theorem configCount_gridSeq_density_of_BV {w : ℝ → ℝ}
    (hw : BoundedVariationOn w (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => configCount w gridSeq N / N) atTop (nhds (∫ t in (0:ℝ)..1, w t)) :=
  configCount_density_of_BV equidistributed_gridSeq hw

end EquidistributionBVReduction
end Brockian

import Mathlib

/-!
# Equidistribution: reduction to functions of bounded variation

Let `x : ℕ → ℝ` be a sequence.  We say `x` is *equidistributed* (mod one) when, for every
window `[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms whose fractional part lies in
the window converges to the length `b - a` of the window.

The main result of this file, `Brockian.EquidistributionBVReduction.configCount_density_of_BV`,
upgrades this defining property from windows to arbitrary weights of bounded variation:
if `x` is equidistributed and `w : ℝ → ℝ` has bounded variation on `[0, 1]`, then the weighted
configuration counts `∑_{n < N} w (fract (x n))` have density `∫₀¹ w`.

The proof is the classical one: a function of bounded variation is a difference of two monotone
functions, and a monotone function is squeezed between the two step functions attached to a
uniform partition of `[0,1]`, whose averages are controlled directly by equidistribution.
-/

open scoped BigOperators
open scoped Classical
open Filter Set MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in the
window `[a, b)`. -/
noncomputable def windowCount (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card

/-- A sequence is equidistributed mod one when the proportion of its first `N` terms landing
in a window `[a, b) ⊆ [0, 1]` tends to the length `b - a` of that window. -/
def Equidistributed (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (windowCount x a b N : ℝ) / N) atTop (nhds (b - a))

/-- The weighted count of the first `N` configurations of the sequence `x`, the weight of a
configuration `n` being `w (fract (x n))`.  For `w` the indicator of a window this is the
plain number of configurations landing in that window. -/
noncomputable def configCount (w : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, w (Int.fract (x n))

section Partition

variable {x : ℕ → ℝ} {m : ℕ}

/-- The index of the cell of the uniform partition of `[0,1)` into `m` cells that contains
`fract (x n)`. -/
noncomputable def cellIdx (x : ℕ → ℝ) (m : ℕ) (n : ℕ) : ℕ := ⌊(m : ℝ) * Int.fract (x n)⌋₊

lemma cellIdx_lt (hm : 0 < m) (n : ℕ) : cellIdx x m n < m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (m : ℝ) * Int.fract (x n) < m := by
    have := Int.fract_lt_one (x n)
    nlinarith
  have h2 : (cellIdx x m n : ℝ) ≤ (m : ℝ) * Int.fract (x n) :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg _))
  exact_mod_cast lt_of_le_of_lt h2 h1

lemma cellIdx_eq_iff (hm : 0 < m) (n i : ℕ) :
    cellIdx x m n = i ↔ Int.fract (x n) ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : (0 : ℝ) ≤ (m : ℝ) * Int.fract (x n) :=
    mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg _)
  rw [cellIdx, Nat.floor_eq_iff hpos, Set.mem_Ico, div_le_iff₀ hm', lt_div_iff₀ hm']
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- The `i`-th fiber of `cellIdx` inside `range N` is exactly the set counted by
`windowCount` for the `i`-th cell. -/
lemma filter_cellIdx_eq (hm : 0 < m) (N i : ℕ) :
    ((Finset.range N).filter (fun n => cellIdx x m n = i)).card
      = windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N := by
  rw [windowCount]
  congr 1
  apply Finset.filter_congr
  intro n _
  simp [cellIdx_eq_iff hm n i]

/-- Both endpoints of the `i`-th cell of the uniform partition lie in `[0,1]`. -/
lemma node_mem (hm : 0 < m) {i : ℕ} (hi : i ∈ Finset.range m) :
    ((i : ℝ) / m) ∈ Set.Icc (0 : ℝ) 1 ∧ (((i : ℝ) + 1) / m) ∈ Set.Icc (0 : ℝ) 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hi
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩ <;> rw [div_le_one hm'] <;> linarith

end Partition

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- Lower step-function bound for the configuration count of a monotone weight. -/
lemma sum_lower_le_configCount (hg : MonotoneOn g (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
      ≤ configCount g x N := by
  have hmaps : ∀ n ∈ Finset.range N, cellIdx x m n ∈ Finset.range m :=
    fun n _ => Finset.mem_range.mpr (cellIdx_lt hm n)
  rw [configCount, ← Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (Int.fract (x n)))]
  apply Finset.sum_le_sum
  intro i hi
  rw [← filter_cellIdx_eq (x := x) hm N i]
  have hle : ∑ _n ∈ (Finset.range N).filter (fun n => cellIdx x m n = i), g ((i : ℝ) / m)
      ≤ ∑ n ∈ (Finset.range N).filter (fun n => cellIdx x m n = i), g (Int.fract (x n)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hmem := (cellIdx_eq_iff hm n i).mp (Finset.mem_filter.mp hn).2
    exact hg (node_mem hm hi).1 ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ hmem.1
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hle

/-- Upper step-function bound for the configuration count of a monotone weight. -/
lemma configCount_le_sum_upper (hg : MonotoneOn g (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    configCount g x N ≤ ∑ i ∈ Finset.range m,
      g (((i : ℝ) + 1) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) := by
  have hmaps : ∀ n ∈ Finset.range N, cellIdx x m n ∈ Finset.range m :=
    fun n _ => Finset.mem_range.mpr (cellIdx_lt hm n)
  rw [configCount, ← Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (Int.fract (x n)))]
  apply Finset.sum_le_sum
  intro i hi
  rw [← filter_cellIdx_eq (x := x) hm N i]
  have hle : ∑ n ∈ (Finset.range N).filter (fun n => cellIdx x m n = i), g (Int.fract (x n))
      ≤ ∑ _n ∈ (Finset.range N).filter (fun n => cellIdx x m n = i), g (((i : ℝ) + 1) / m) := by
    apply Finset.sum_le_sum
    intro n hn
    have hmem := (cellIdx_eq_iff hm n i).mp (Finset.mem_filter.mp hn).2
    exact hg ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ (node_mem hm hi).2 hmem.2.le
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hle

section RiemannSums

variable {m : ℕ}

private lemma partition_mono (hm : 0 < m) : Monotone (fun i : ℕ => (i : ℝ) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  intro i j hij
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  show (i : ℝ) / m ≤ (j : ℝ) / m
  gcongr

private lemma partition_sub (hm : 0 < m) {k : ℕ} (hk : k < m) :
    Set.Icc ((k : ℝ) / m) (((k + 1 : ℕ) : ℝ) / m) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  intro t ht
  have hk' : ((k : ℝ) + 1) ≤ m := by exact_mod_cast hk
  refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
  push_cast
  rw [div_le_one hm']
  linarith

private lemma partition_integrable (hg : MonotoneOn g (Set.Icc 0 1)) (hm : 0 < m) :
    ∀ k < m, IntervalIntegrable g volume ((k : ℝ) / m) (((k + 1 : ℕ) : ℝ) / m) := by
  intro k hk
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le (partition_mono hm (Nat.le_succ k))]
  exact hg.mono (partition_sub hm hk)

/-- Lower Riemann sums underestimate the integral of a monotone function. -/
lemma lower_sum_le_integral (hg : MonotoneOn g (Set.Icc 0 1)) (hm : 0 < m) :
    ∑ i ∈ Finset.range m, g ((i : ℝ) / m) / m ≤ ∫ t in (0:ℝ)..1, g t := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hint := partition_integrable hg hm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / m) (f := g) (μ := volume) hint
  simp only [Nat.cast_zero, zero_div, div_self hm'.ne'] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i hi
  have him := Finset.mem_range.mp hi
  have hik : (i : ℝ) / m ≤ ((i + 1 : ℕ) : ℝ) / m := partition_mono hm (Nat.le_succ i)
  have key := intervalIntegral.integral_mono_on (μ := volume) hik
    (intervalIntegrable_const (c := g ((i : ℝ) / m))) (hint i him)
    (fun t ht => hg (partition_sub hm him ⟨le_refl _, hik⟩) (partition_sub hm him ht) ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at key
  have hlen : ((i + 1 : ℕ) : ℝ) / m - (i : ℝ) / m = 1 / m := by push_cast; field_simp; ring
  rw [hlen] at key
  calc g ((i : ℝ) / m) / m = 1 / m * g ((i : ℝ) / m) := by ring
    _ ≤ _ := key

/-- Upper Riemann sums overestimate the integral of a monotone function. -/
lemma integral_le_upper_sum (hg : MonotoneOn g (Set.Icc 0 1)) (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hint := partition_integrable hg hm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / m) (f := g) (μ := volume) hint
  simp only [Nat.cast_zero, zero_div, div_self hm'.ne'] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i hi
  have him := Finset.mem_range.mp hi
  have hik : (i : ℝ) / m ≤ ((i + 1 : ℕ) : ℝ) / m := partition_mono hm (Nat.le_succ i)
  have key := intervalIntegral.integral_mono_on (μ := volume) hik (hint i him)
    (intervalIntegrable_const (c := g (((i + 1 : ℕ) : ℝ) / m)))
    (fun t ht => hg (partition_sub hm him ht) (partition_sub hm him ⟨hik, le_refl _⟩) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at key
  have hlen : ((i + 1 : ℕ) : ℝ) / m - (i : ℝ) / m = 1 / m := by push_cast; field_simp; ring
  have hcast : ((i + 1 : ℕ) : ℝ) / m = ((i : ℝ) + 1) / m := by push_cast; ring
  rw [hlen, hcast,
    show (1 : ℝ) / m * g (((i : ℝ) + 1) / m) = g (((i : ℝ) + 1) / m) / m from by ring] at key
  rw [hcast]
  exact key

/-- The gap between the upper and the lower Riemann sum telescopes. -/
lemma upper_sub_lower (g : ℝ → ℝ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) / m)
      - (∑ i ∈ Finset.range m, g ((i : ℝ) / m) / m) = (g 1 - g 0) / m := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [← Finset.sum_sub_distrib]
  have key : ∀ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) / m - g ((i : ℝ) / m) / m
      = (fun j : ℕ => g ((j : ℝ) / m) / m) (i + 1) - (fun j : ℕ => g ((j : ℝ) / m) / m) i := by
    intro i _; push_cast; ring_nf
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub (fun j : ℕ => g ((j : ℝ) / m) / m) m]
  field_simp
  norm_num

end RiemannSums

/-- Equidistribution controls the average of a step function. -/
lemma tendsto_step_average (hx : Equidistributed x) (c : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range m, c i * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N)
      atTop (nhds (∑ i ∈ Finset.range m, c i / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp_rw [Finset.sum_div, mul_div_assoc]
  apply tendsto_finset_sum
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hi
  have h := hx ((i : ℝ) / m) (((i : ℝ) + 1) / m) (by positivity)
    (by apply div_le_div_of_nonneg_right <;> linarith)
    (by rw [div_le_one hm']; linarith)
  have hval : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
  rw [hval] at h
  rw [show c i / m = c i * (1 / m) by ring]
  exact h.const_mul (c i)

/-- The BV reduction for a monotone weight: the configuration counts of an equidistributed
sequence weighted by a monotone function have density the integral of that function. -/
theorem configCount_density_of_monotoneOn (hx : Equidistributed x)
    (hg : MonotoneOn g (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => configCount g x N / N) atTop (nhds (∫ t in (0:ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m0, hm0⟩ := exists_nat_gt ((g 1 - g 0) * 2 / ε)
  set m : ℕ := m0 + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos m0
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmgt : (g 1 - g 0) * 2 / ε < m := by
    refine lt_of_lt_of_le hm0 ?_
    rw [hmdef]
    push_cast
    linarith
  have hgap : (g 1 - g 0) / m < ε / 2 := by
    rw [div_lt_div_iff₀ hm' (by norm_num)]
    rw [div_lt_iff₀ hε] at hmgt
    linarith
  set Lo : ℝ := ∑ i ∈ Finset.range m, g ((i : ℝ) / m) / m
  set Hi : ℝ := ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) / m
  have hLoI : Lo ≤ ∫ t in (0:ℝ)..1, g t := lower_sum_le_integral hg hm
  have hIHi : (∫ t in (0:ℝ)..1, g t) ≤ Hi := integral_le_upper_sum hg hm
  have hHL : Hi - Lo = (g 1 - g 0) / m := upper_sub_lower g hm
  have hA := tendsto_step_average (x := x) hx (fun i => g ((i : ℝ) / m)) hm
  have hB := tendsto_step_average (x := x) hx (fun i => g (((i : ℝ) + 1) / m)) hm
  rw [Metric.tendsto_atTop] at hA hB
  obtain ⟨N1, hN1⟩ := hA (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := hB (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hA' := hN1 N (le_trans (le_max_left _ _) hN)
  have hB' := hN2 N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hA' hB'
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow : (∑ i ∈ Finset.range m,
      g ((i : ℝ) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N
      ≤ configCount g x N / N := by
    gcongr
    exact sum_lower_le_configCount hg hm N
  have hupp : configCount g x N / N ≤ (∑ i ∈ Finset.range m,
      g (((i : ℝ) + 1) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N := by
    gcongr
    exact configCount_le_sum_upper hg hm N
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Monotone

/-- **Bounded-variation reduction for equidistributed sequences.**
If `x` is equidistributed mod one and the weight `w` has bounded variation on `[0, 1]`, then
the weighted configuration counts `∑_{n < N} w (fract (x n))` have density `∫₀¹ w`. -/
theorem configCount_density_of_BV {x : ℕ → ℝ} {w : ℝ → ℝ}
    (hx : Equidistributed x) (hw : BoundedVariationOn w (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => configCount w x N / N) atTop (nhds (∫ t in (0:ℝ)..1, w t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hw.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one' ℝ)]
  have hqi : IntervalIntegrable q volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one' ℝ)]
  have hI : (∫ t in (0:ℝ)..1, w t)
      = (∫ t in (0:ℝ)..1, p t) - (∫ t in (0:ℝ)..1, q t) := by
    rw [← intervalIntegral.integral_sub hpi hqi]
    exact intervalIntegral.integral_congr (fun t _ => by rw [hpq]; rfl)
  have hcc : ∀ N : ℕ, configCount w x N / N
      = configCount p x N / N - configCount q x N / N := by
    intro N
    rw [← sub_div]
    congr 1
    simp only [configCount, hpq, Pi.sub_apply, Finset.sum_sub_distrib]
  simp only [hcc, hI]
  exact (configCount_density_of_monotoneOn hx hp).sub (configCount_density_of_monotoneOn hx hq)

end EquidistributionBVReduction
end Brockian

