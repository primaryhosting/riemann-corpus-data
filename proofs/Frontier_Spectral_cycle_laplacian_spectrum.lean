import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Complex

/-- The graph Laplacian `L(C n)` of the cycle graph on `n` vertices: the `n × n` circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/
def cycleLaplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then -1 else 0

section Aux

variable {n : ℕ} [NeZero n]

lemma val_one (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)]

lemma val_add_one (hn : 2 ≤ n) (i : Fin n) : ((i + 1 : Fin n) : ℕ) = (i.val + 1) % n := by
  rw [Fin.val_add, val_one hn]

omit [NeZero n] in
/-- If `z ^ n = 1` then the exponent of `z` may be reduced mod `n`. -/
lemma pow_mod_eq {z : ℂ} (hz : z ^ n = 1) (m : ℕ) : z ^ (m % n) = z ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

omit [NeZero n] in
/-- If `z ^ n = 1` then `k ↦ z ^ k` factors through `Fin n`. -/
lemma pow_val_add {z : ℂ} (hz : z ^ n = 1) (a b : Fin n) :
    z ^ ((a + b : Fin n) : ℕ) = z ^ (a : ℕ) * z ^ (b : ℕ) := by
  rw [Fin.val_add, pow_mod_eq hz, pow_add]

lemma cycleLaplacian_row (hn : 3 ≤ n) (f : Fin n → ℂ) (i : Fin n) :
    ∑ j, cycleLaplacian n i j * f j = 2 * f i - f (i + 1) - f (i - 1) := by
  have hone : ((1 : Fin n) : ℕ) = 1 := val_one (by omega)
  have hsucc : ∀ a : Fin n, ((a + 1 : Fin n) : ℕ) = (a.val + 1) % n :=
    fun a => val_add_one (by omega) a
  have hne1 : (1 : Fin n) ≠ 0 := by
    intro h; have h' := congrArg Fin.val h; simp at h'; omega
  have h11 : ((1 : Fin n) + 1) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [hsucc 1, hone, Nat.mod_eq_of_lt (by omega : 1 + 1 < n)] at h'
    simp at h'
  have hii1 : i ≠ i + 1 := by
    intro h
    have h' : i + 0 = i + 1 := by simpa using h
    exact hne1 (add_left_cancel h').symm
  have hii2 : i ≠ i - 1 := fun h => hne1 (sub_eq_self.1 h.symm)
  have h12 : (i + 1 : Fin n) ≠ i - 1 := by
    intro h
    refine h11 (add_left_cancel (a := i) ?_)
    rw [← add_assoc, h]
    simp
  have key : ∀ j : Fin n, cycleLaplacian n i j
      = 2 * (if j = i then 1 else 0) - (if j = i + 1 then 1 else 0)
        - (if j = i - 1 then 1 else 0) := by
    intro j
    have ha : ((i.val + 1) % n = j.val) ↔ j = i + 1 := by
      rw [← hsucc i]
      exact ⟨fun h => (Fin.val_eq_val _ _).1 h.symm, fun h => by rw [h]⟩
    have hb : ((j.val + 1) % n = i.val) ↔ j = i - 1 := by
      rw [← hsucc j, eq_sub_iff_add_eq]
      exact ⟨fun h => (Fin.val_eq_val _ _).1 h, fun h => (Fin.val_eq_val _ _).2 h⟩
    simp only [cycleLaplacian, Matrix.of_apply, ha, hb]
    rcases eq_or_ne j i with hj | hj
    · subst hj
      rw [if_neg hii1, if_neg hii2]
      simp
    · rw [if_neg (Ne.symm hj), if_neg hj]
      rcases eq_or_ne j (i + 1) with hj1 | hj1
      · subst hj1
        rw [if_neg h12]
        simp
      · rcases eq_or_ne j (i - 1) with hj2 | hj2
        · subst hj2
          rw [if_neg (Ne.symm h12)]
          simp
        · simp [hj1, hj2]
  rw [Finset.sum_congr rfl (fun j _ => by rw [key j])]
  simp [sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq']

end Aux

/-- **Spectrum of the cycle Laplacian.**  For `n ≥ 3` the eigenvalues of the graph Laplacian
of the cycle `C n` are exactly the numbers `2 - 2 cos (2 π k / n)`, `k = 0, …, n-1`. -/
theorem cycle_laplacian_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      {μ : ℂ | ∃ k ∈ Finset.range n, μ = 2 - 2 * (Real.cos (2 * Real.pi * k / n) : ℂ)} := by
  haveI : NeZero n := ⟨by omega⟩
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hω
  have hprim : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n (by omega)
  set d : Fin n → ℂ := fun k => 2 - 2 * (Real.cos (2 * Real.pi * (k : ℕ) / n) : ℂ) with hd
  set F : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde (fun i : Fin n => ω ^ (i : ℕ)) with hF
  have hFdet : F.det ≠ 0 := by
    rw [hF, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    exact Fin.ext (hprim.pow_inj a.isLt b.isLt hab)
  obtain ⟨u, hu⟩ : IsUnit F :=
    (Matrix.isUnit_iff_isUnit_det F).2 (isUnit_iff_ne_zero.2 hFdet)
  have hmul : cycleLaplacian n * F = F * Matrix.diagonal d := by
    ext i k
    set z : ℂ := ω ^ (k : ℕ) with hzdef
    have hzn : z ^ n = 1 := by
      rw [hzdef, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    have hzexp : z = Complex.exp ((2 * Real.pi * (k : ℕ) / n : ℝ) * Complex.I) := by
      rw [hzdef, hω, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hz0 : z ≠ 0 := by
      rw [hzexp]; exact Complex.exp_ne_zero _
    have hFcol : ∀ j : Fin n, F j k = z ^ (j : ℕ) := by
      intro j
      rw [hF, Matrix.vandermonde_apply, hzdef, ← pow_mul, ← pow_mul, mul_comm]
    have hcos : z + z⁻¹ = 2 * (Real.cos (2 * Real.pi * (k : ℕ) / n) : ℂ) := by
      rw [hzexp, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos, neg_mul]
    rw [Matrix.mul_apply]
    have hrow := cycleLaplacian_row hn (fun j => F j k) i
    simp only at hrow
    rw [hrow, hFcol i, hFcol (i + 1), hFcol (i - 1)]
    have h1 : z ^ ((i + 1 : Fin n) : ℕ) = z ^ (i : ℕ) * z := by
      rw [pow_val_add hzn, val_one (by omega : 2 ≤ n), pow_one]
    have h2 : z ^ ((i - 1 : Fin n) : ℕ) * z = z ^ (i : ℕ) := by
      have := pow_val_add hzn (i - 1) 1
      rw [sub_add_cancel, val_one (by omega : 2 ≤ n), pow_one] at this
      exact this.symm
    have h2' : z ^ ((i - 1 : Fin n) : ℕ) = z ^ (i : ℕ) * z⁻¹ := by
      rw [← h2, mul_inv_cancel_right₀ hz0]
    rw [h1, h2', Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, hFcol i, hd]
      linear_combination (-(z ^ (i : ℕ))) * hcos
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hconj : cycleLaplacian n
      = (u : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal d * ((u⁻¹ : _) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Units.eq_mul_inv_iff_mul_eq, hu]
    exact hmul
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  ext μ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ℕ), Finset.mem_range.2 k.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, Finset.mem_range.1 hk⟩, rfl⟩

end Frontier.Spectral

