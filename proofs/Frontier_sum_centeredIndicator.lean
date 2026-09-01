import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/
noncomputable def centeredIndicator (S : Finset V) (i : V) : ℝ :=
  (if i ∈ S then (1 : ℝ) else 0) - S.card / (Fintype.card V)

/-- The centered indicator has zero sum, i.e. it is orthogonal to the all-ones vector. -/
lemma sum_centeredIndicator (hV : (Fintype.card V) ≠ 0) (S : Finset V) :
    ∑ i, centeredIndicator S i = 0 := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hV
  simp only [centeredIndicator, Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ]
  field_simp
  ring

/-- The squared norm of the centered indicator is `|S| - |S|²/n ≤ |S|`. -/
lemma sum_sq_centeredIndicator (hV : (Fintype.card V) ≠ 0) (S : Finset V) :
    ∑ i, (centeredIndicator S i) ^ 2
      = S.card - (S.card : ℝ) ^ 2 / (Fintype.card V) := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hV
  have hpt : ∀ i : V, (centeredIndicator S i) ^ 2
      = (if i ∈ S then (1:ℝ) else 0)
        - 2 * ((S.card : ℝ) / (Fintype.card V)) * (if i ∈ S then (1:ℝ) else 0)
        + ((S.card : ℝ) / (Fintype.card V)) ^ 2 := by
    intro i
    by_cases h : i ∈ S
    · simp only [centeredIndicator, h, if_true]; ring
    · simp only [centeredIndicator, h, if_false]; ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.card_univ]
  field_simp
  ring

lemma sum_sq_centeredIndicator_le (hV : (Fintype.card V) ≠ 0) (S : Finset V) :
    ∑ i, (centeredIndicator S i) ^ 2 ≤ (S.card : ℝ) := by
  rw [sum_sq_centeredIndicator hV S]
  have hn : (0:ℝ) < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
    exact_mod_cast this
  have : (0:ℝ) ≤ (S.card : ℝ) ^ 2 / (Fintype.card V) := by positivity
  linarith

/-- Expansion of the bilinear form of `A` on the centered indicators of `S` and `T`,
for a matrix with all row sums and all column sums equal to `d`. -/
lemma bilinear_centeredIndicator (hV : (Fintype.card V) ≠ 0)
    (A : Matrix V V ℝ) (d : ℝ)
    (hrow : ∀ i, ∑ j, A i j = d) (hcol : ∀ j, ∑ i, A i j = d)
    (S T : Finset V) :
    ∑ i, ∑ j, centeredIndicator S i * A i j * centeredIndicator T j
      = (∑ i ∈ S, ∑ j ∈ T, A i j)
        - d * S.card * T.card / (Fintype.card V) := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hV
  -- inner sum over `j`
  have hinner : ∀ i : V, ∑ j, A i j * centeredIndicator T j
      = (∑ j ∈ T, A i j) - ((T.card : ℝ) / (Fintype.card V)) * d := by
    intro i
    simp only [centeredIndicator, mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_mem]
    · rw [← Finset.sum_mul, hrow i]; ring
  have hstep : ∑ i, ∑ j, centeredIndicator S i * A i j * centeredIndicator T j
      = ∑ i, centeredIndicator S i *
          ((∑ j ∈ T, A i j) - ((T.card : ℝ) / (Fintype.card V)) * d) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hinner i, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hstep]
  -- split off the constant part
  have hsplit : ∑ i, centeredIndicator S i *
      ((∑ j ∈ T, A i j) - ((T.card : ℝ) / (Fintype.card V)) * d)
      = (∑ i, centeredIndicator S i * (∑ j ∈ T, A i j))
        - (((T.card : ℝ) / (Fintype.card V)) * d) * (∑ i, centeredIndicator S i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, sum_centeredIndicator hV S, mul_zero, sub_zero]
  -- total sum of the column-restricted row sums
  have htot : ∑ i, (∑ j ∈ T, A i j) = (T.card : ℝ) * d := by
    rw [Finset.sum_comm]
    simp [hcol, mul_comm]
  have : ∑ i, centeredIndicator S i * (∑ j ∈ T, A i j)
      = (∑ i ∈ S, ∑ j ∈ T, A i j)
        - ((S.card : ℝ) / (Fintype.card V)) * ((T.card : ℝ) * d) := by
    simp only [centeredIndicator, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_mem]
    · rw [← Finset.mul_sum, htot]
  rw [this]
  field_simp

/--
**Expander mixing lemma** (Alon–Chung; see Hoory–Linial–Wigderson, *Expander graphs and their
applications*, Lemma 2.5).

Let `A` be the adjacency matrix (or any real matrix) on a finite vertex set `V` with
`n = |V| > 0`, all of whose row sums and column sums equal `d` (i.e. `A` is `d`-regular, so the
all-ones vector is an eigenvector with eigenvalue `d`).  Suppose `A` has spectral gap `lam ≥ 0`,
expressed as the bound `|xᵀ A y| ≤ lam ‖x‖ ‖y‖` for all vectors `x, y` orthogonal to the
all-ones vector (this is exactly the statement that the second largest eigenvalue in absolute
value is at most `lam`).

Then for all sets of vertices `S, T`, the number of edges between them, `e(S,T) = ∑_{i∈S,j∈T} Aᵢⱼ`,
deviates from its "expected" value `d|S||T|/n` by at most `lam √(|S||T|)`.
-/
theorem wigderson_expander_mixing [Nonempty V]
    (A : Matrix V V ℝ) (d lam : ℝ) (hlam : 0 ≤ lam)
    (hrow : ∀ i, ∑ j, A i j = d) (hcol : ∀ j, ∑ i, A i j = d)
    (hspec : ∀ x y : V → ℝ, (∑ i, x i) = 0 → (∑ i, y i) = 0 →
      |∑ i, ∑ j, x i * A i j * y j| ≤
        lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (S T : Finset V) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / (Fintype.card V)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hV : (Fintype.card V) ≠ 0 := Fintype.card_ne_zero
  have hbil := bilinear_centeredIndicator hV A d hrow hcol S T
  have hb := hspec (centeredIndicator S) (centeredIndicator T)
      (sum_centeredIndicator hV S) (sum_centeredIndicator hV T)
  rw [hbil] at hb
  refine hb.trans ?_
  have h1 : Real.sqrt (∑ i, (centeredIndicator S i) ^ 2) ≤ Real.sqrt (S.card : ℝ) :=
    Real.sqrt_le_sqrt (sum_sq_centeredIndicator_le hV S)
  have h2 : Real.sqrt (∑ i, (centeredIndicator T i) ^ 2) ≤ Real.sqrt (T.card : ℝ) :=
    Real.sqrt_le_sqrt (sum_sq_centeredIndicator_le hV T)
  have hsq : Real.sqrt ((S.card : ℝ) * (T.card : ℝ))
      = Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
    Real.sqrt_mul (by positivity) _
  rw [hsq]
  have hnn1 : (0:ℝ) ≤ Real.sqrt (∑ i, (centeredIndicator S i) ^ 2) := Real.sqrt_nonneg _
  have hnn2 : (0:ℝ) ≤ Real.sqrt (∑ i, (centeredIndicator T i) ^ 2) := Real.sqrt_nonneg _
  have hs : (0:ℝ) ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  calc lam * Real.sqrt (∑ i, (centeredIndicator S i) ^ 2)
        * Real.sqrt (∑ i, (centeredIndicator T i) ^ 2)
      ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ i, (centeredIndicator T i) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlam) hnn2
    _ ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = lam * (Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ)) := by ring

/-- Sanity check: the hypotheses of `wigderson_expander_mixing` are satisfiable nondegenerately.
The "flat" matrix `A i j = d / n` is `d`-regular and annihilates every vector orthogonal to the
all-ones vector, so it satisfies the spectral hypothesis with `lam = 0`; the lemma then says that
the edge count between any two sets is *exactly* `d |S| |T| / n`. -/
example [Nonempty V] (d : ℝ) (S T : Finset V) :
    |(∑ _i ∈ S, ∑ _j ∈ T, d / (Fintype.card V))
        - d * S.card * T.card / (Fintype.card V)| ≤ 0 * Real.sqrt (S.card * T.card) := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  refine wigderson_expander_mixing (Matrix.of fun _ _ => d / (Fintype.card V)) d 0 le_rfl
    (fun _ => ?_) (fun _ => ?_) (fun x y hx _hy => ?_) S T
  · simp [Finset.card_univ]
    field_simp
  · simp [Finset.card_univ]
    field_simp
  · have : ∑ i, ∑ j, x i * (d / (Fintype.card V)) * y j
        = (d / (Fintype.card V)) * ((∑ i, x i) * (∑ j, y j)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp [Matrix.of_apply, this, hx]

end Frontier

