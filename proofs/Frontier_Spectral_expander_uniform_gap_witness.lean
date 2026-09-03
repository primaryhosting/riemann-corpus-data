/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

namespace Frontier.Spectral

/-- Vertices of the `k`-dimensional hypercube graph `Q k`: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → Bool

/-- Flip the `i`-th coordinate of a vertex: the neighbours of `x` in `Q k` are the
`flipAt x i` for `i : Fin k`. -/
def flipAt {k : ℕ} (x : Cube k) (i : Fin k) : Cube k := Function.update x i (!x i)

/-- The graph Laplacian of the hypercube `Q k`, acting on real functions on vertices.
Since `Q k` is `k`-regular, `L = k • I - A`. -/
def lap {k : ℕ} (v : Cube k → ℝ) (x : Cube k) : ℝ := k * v x - ∑ i, v (flipAt x i)

/-- `μ` is a Laplacian eigenvalue of the hypercube `Q k`. -/
def IsLapEigenvalue (k : ℕ) (μ : ℝ) : Prop :=
  ∃ v : Cube k → ℝ, v ≠ 0 ∧ ∀ x, lap v x = μ * v x

/-- The character (Walsh function) indexed by `s`, evaluated at `x`: `(-1)^⟨s,x⟩`. -/
def chi {k : ℕ} (s x : Cube k) : ℝ := ∏ i, (if s i && x i then (-1 : ℝ) else 1)

/-- The Hamming weight of `s`, i.e. the number of `1` bits. -/
def wt {k : ℕ} (s : Cube k) : ℕ := (Finset.univ.filter fun i => s i = true).card

lemma chi_comm {k : ℕ} (s x : Cube k) : chi s x = chi x s := by
  unfold chi
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Bool.and_comm]

lemma chi_mul_self {k : ℕ} (s x : Cube k) : chi s x * chi s x = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : s i && x i <;> simp [h]

lemma chi_ne_zero {k : ℕ} (s x : Cube k) : chi s x ≠ 0 := by
  intro h
  have := chi_mul_self s x
  rw [h] at this
  norm_num at this

lemma flipAt_involutive {k : ℕ} (i : Fin k) : Function.Involutive (fun x : Cube k => flipAt x i) := by
  intro x
  funext j
  by_cases h : j = i <;> simp [flipAt, Function.update, h]

lemma chi_flipAt {k : ℕ} (s x : Cube k) (i : Fin k) :
    chi s (flipAt x i) = (if s i then -chi s x else chi s x) := by
  have hpe : ∀ j ∈ Finset.univ.erase i,
      (if s j && (flipAt x i) j then (-1 : ℝ) else 1) = (if s j && x j then (-1 : ℝ) else 1) := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [flipAt, Function.update, hji]
  have e1 : chi s (flipAt x i)
      = (if s i && (flipAt x i) i then (-1 : ℝ) else 1)
        * ∏ j ∈ Finset.univ.erase i, (if s j && (flipAt x i) j then (-1 : ℝ) else 1) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have e2 : chi s x = (if s i && x i then (-1 : ℝ) else 1)
        * ∏ j ∈ Finset.univ.erase i, (if s j && x j then (-1 : ℝ) else 1) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [e1, e2, Finset.prod_congr rfl hpe]
  have hfi : (flipAt x i) i = !x i := by simp [flipAt]
  rw [hfi]
  rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (x i) with hx | hx <;>
      simp [hs, hx]

/-- The characters are eigenvectors: `L χ_s = 2 |s| χ_s`. -/
lemma lap_chi {k : ℕ} (s : Cube k) (x : Cube k) :
    lap (chi s) x = (2 * wt s : ℝ) * chi s x := by
  unfold lap
  have hsum : ∑ i, chi s (flipAt x i)
      = ∑ i, (if s i = true then -chi s x else chi s x) := by
    simp only [chi_flipAt]
  rw [hsum]
  rw [Finset.sum_ite (f := fun _ => -chi s x) (g := fun _ => chi s x)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun i => ¬ (s i = true)).card = k - wt s := by
    have : (Finset.univ.filter fun i => s i = true).card
        + (Finset.univ.filter fun i => ¬ (s i = true)).card = k := by
      simpa using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin k))) (p := fun i => s i = true)
    unfold wt
    omega
  have hle : wt s ≤ k := by
    unfold wt
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun i => s i = true)
  rw [hcard]
  have : ((k - wt s : ℕ) : ℝ) = (k : ℝ) - (wt s : ℝ) := by
    push_cast [Nat.cast_sub hle]; ring
  rw [this]
  unfold wt
  push_cast
  ring

/-- Orthogonality of characters. -/
lemma chi_orthogonal {k : ℕ} (s t : Cube k) :
    ∑ x : Cube k, chi s x * chi t x = if s = t then (2 : ℝ) ^ k else 0 := by
  have key : ∀ x : Cube k, chi s x * chi t x
      = ∏ i, ((if s i && x i then (-1 : ℝ) else 1) * (if t i && x i then (-1 : ℝ) else 1)) := by
    intro x
    unfold chi
    rw [Finset.prod_mul_distrib]
  simp_rw [key]
  rw [← Fintype.prod_sum (f := fun (i : Fin k) (b : Bool) =>
    (if s i && b then (-1 : ℝ) else 1) * (if t i && b then (-1 : ℝ) else 1))]
  have hfac : ∀ i : Fin k, (∑ b : Bool, ((if s i && b then (-1 : ℝ) else 1)
      * (if t i && b then (-1 : ℝ) else 1))) = if s i = t i then (2 : ℝ) else 0 := by
    intro i
    rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t i) with ht | ht <;>
        simp [hs, ht]
  simp_rw [hfac]
  by_cases hst : s = t
  · subst hst
    simp
  · rw [if_neg hst]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
      by_contra h
      exact hst (funext fun i => not_not.mp (fun hh => h ⟨i, hh⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])

/-- Completeness of the character system: a function orthogonal to all characters is zero. -/
lemma fourier_complete {k : ℕ} (v : Cube k → ℝ) (h : ∀ s : Cube k, ∑ x, v x * chi s x = 0) :
    v = 0 := by
  funext y
  have h1 : ∑ s : Cube k, (∑ x, v x * chi s x) * chi s y = 0 := by
    simp [h]
  have h2 : ∑ s : Cube k, (∑ x, v x * chi s x) * chi s y
      = ∑ x : Cube k, v x * (∑ s : Cube k, chi s x * chi s y) := by
    calc ∑ s : Cube k, (∑ x, v x * chi s x) * chi s y
        = ∑ s : Cube k, ∑ x : Cube k, (v x * chi s x) * chi s y := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ x : Cube k, ∑ s : Cube k, (v x * chi s x) * chi s y := Finset.sum_comm
      _ = ∑ x : Cube k, v x * (∑ s : Cube k, chi s x * chi s y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
  have h3 : ∀ x : Cube k, (∑ s : Cube k, chi s x * chi s y)
      = if x = y then (2 : ℝ) ^ k else 0 := by
    intro x
    have : ∀ s : Cube k, chi s x * chi s y = chi x s * chi y s := by
      intro s; rw [chi_comm s x, chi_comm s y]
    simp_rw [this]
    exact chi_orthogonal x y
  rw [h2] at h1
  simp_rw [h3] at h1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  have h2k : ((2:ℝ) ^ k) ≠ 0 := by positivity
  rcases mul_eq_zero.mp h1 with h' | h'
  · simpa using h'
  · exact absurd h' h2k

/-- The Laplacian is symmetric with respect to the standard bilinear form. -/
lemma lap_symm {k : ℕ} (v w : Cube k → ℝ) :
    ∑ x, lap v x * w x = ∑ x, v x * lap w x := by
  have key : ∑ x : Cube k, (∑ i, v (flipAt x i)) * w x
      = ∑ x : Cube k, v x * ∑ i, w (flipAt x i) := by
    have l1 : ∑ x : Cube k, (∑ i, v (flipAt x i)) * w x
        = ∑ i : Fin k, ∑ x : Cube k, v (flipAt x i) * w x := by
      rw [← Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
    have l2 : ∑ x : Cube k, v x * (∑ i, w (flipAt x i))
        = ∑ i : Fin k, ∑ x : Cube k, v x * w (flipAt x i) := by
      rw [← Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
    rw [l1, l2]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Fintype.sum_equiv ((flipAt_involutive i).toPerm _) _ _ ?_
    intro x
    simp only [Function.Involutive.coe_toPerm]
    have hinv : flipAt (flipAt x i) i = x := flipAt_involutive i x
    rw [hinv]
  unfold lap
  simp only [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, key]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Every Laplacian eigenvalue of `Q k` is of the form `2 * (Hamming weight)`. -/
lemma eigenvalue_eq_two_mul_wt {k : ℕ} {μ : ℝ} (h : IsLapEigenvalue k μ) :
    ∃ s : Cube k, μ = 2 * wt s := by
  obtain ⟨v, hv0, hv⟩ := h
  obtain ⟨s, hs⟩ : ∃ s : Cube k, ∑ x, v x * chi s x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv0 (fourier_complete v hcon)
  refine ⟨s, ?_⟩
  have h1 : ∑ x, lap v x * chi s x = μ * ∑ x, v x * chi s x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hv x]; ring
  have h2 : ∑ x, v x * lap (chi s) x = (2 * wt s : ℝ) * ∑ x, v x * chi s x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lap_chi]; ring
  rw [lap_symm v (chi s), h2] at h1
  exact (mul_right_cancel₀ hs h1).symm

/-- `2` is a Laplacian eigenvalue of `Q k` whenever `k ≥ 1`. -/
lemma two_isLapEigenvalue {k : ℕ} (hk : 1 ≤ k) : IsLapEigenvalue k 2 := by
  refine ⟨chi (fun i => decide (i = ⟨0, hk⟩)), ?_, ?_⟩
  · intro hc
    exact chi_ne_zero (k := k) (fun i => decide (i = ⟨0, hk⟩)) (fun _ => false)
      (by rw [hc]; rfl)
  · intro x
    rw [lap_chi]
    congr 1
    have : wt (k := k) (fun i => decide (i = ⟨0, hk⟩)) = 1 := by
      unfold wt
      have : (Finset.univ.filter fun i : Fin k => (decide (i = ⟨0, hk⟩)) = true)
          = {(⟨0, hk⟩ : Fin k)} := by
        ext i
        simp
      rw [this]
      simp
    rw [this]
    norm_num

/-- **Uniform spectral gap of the hypercube family.**
For every `k ≥ 1`, the smallest nonzero Laplacian eigenvalue of the hypercube graph `Q k`
(on `2 ^ k` vertices) is exactly `2`.  In particular the family `(Q k)` has a spectral gap
bounded below by `2`, uniformly in `k`. -/
theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k →
      IsLeast {μ : ℝ | IsLapEigenvalue k μ ∧ μ ≠ 0} 2 ∧
        ∀ μ : ℝ, IsLapEigenvalue k μ → μ ≠ 0 → 2 ≤ μ := by
  intro k hk
  have lower : ∀ μ : ℝ, IsLapEigenvalue k μ → μ ≠ 0 → 2 ≤ μ := by
    intro μ hμ hμ0
    obtain ⟨s, hs⟩ := eigenvalue_eq_two_mul_wt hμ
    have hw : wt s ≠ 0 := by
      intro h
      apply hμ0
      rw [hs, h]
      norm_num
    have : (1 : ℝ) ≤ (wt s : ℝ) := by
      have : 1 ≤ wt s := Nat.one_le_iff_ne_zero.mpr hw
      exact_mod_cast this
    rw [hs]
    nlinarith
  exact ⟨⟨⟨two_isLapEigenvalue hk, by norm_num⟩, fun μ hμ => lower μ hμ.1 hμ.2⟩, lower⟩

end Frontier.Spectral

