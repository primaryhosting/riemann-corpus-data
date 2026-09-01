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

import Mathlib

/-!
# Basic notions for the Hadwiger–Nelson problem

We identify the Euclidean plane with `ℂ`.  A *proper* 4-colouring is a map
`c : ℂ → Fin 4` such that no two points at distance exactly `1` receive the
same colour.  We phrase the distance condition with `Complex.normSq` (the
squared modulus) so that all verifications stay polynomial.
-/

namespace CNP

open Complex

/-- A proper 4-colouring of the plane. -/
def Proper (c : ℂ → Fin 4) : Prop :=
  ∀ z w : ℂ, normSq (z - w) = 1 → c z ≠ c w

/-- No equilateral triangle with side `√3` is monochromatic. -/
def NoMonoTri (c : ℂ → Fin 4) : Prop :=
  ∀ p q r : ℂ, normSq (p - q) = 3 → normSq (q - r) = 3 → normSq (p - r) = 3 →
    ¬ (c p = c q ∧ c q = c r)

/-- Composing a proper colouring with a colour permutation gives a proper colouring. -/
theorem Proper.perm {c : ℂ → Fin 4} (hc : Proper c) (σ : Equiv.Perm (Fin 4)) :
    Proper fun z => σ (c z) := by
  intro z w h hzw
  exact hc z w h (σ.injective hzw)

theorem NoMonoTri.perm {c : ℂ → Fin 4} (hc : NoMonoTri c) (σ : Equiv.Perm (Fin 4)) :
    NoMonoTri fun z => σ (c z) := by
  rintro p q r h1 h2 h3 ⟨e1, e2⟩
  exact hc p q r h1 h2 h3 ⟨σ.injective e1, σ.injective e2⟩

/-- Precomposing a proper colouring with a direct isometry `z ↦ u * z + v` (with `|u| = 1`)
gives a proper colouring. -/
theorem Proper.affine {c : ℂ → Fin 4} (hc : Proper c) {u v : ℂ} (hu : normSq u = 1) :
    Proper fun z => c (u * z + v) := by
  intro z w h
  refine hc _ _ ?_
  have e : u * z + v - (u * w + v) = u * (z - w) := by ring
  rw [e, normSq_mul, hu, one_mul, h]

theorem NoMonoTri.affine {c : ℂ → Fin 4} (hc : NoMonoTri c) {u v : ℂ} (hu : normSq u = 1) :
    NoMonoTri fun z => c (u * z + v) := by
  intro p q r h1 h2 h3
  have e1 : u * p + v - (u * q + v) = u * (p - q) := by ring
  have e2 : u * q + v - (u * r + v) = u * (q - r) := by ring
  have e3 : u * p + v - (u * r + v) = u * (p - r) := by ring
  refine hc _ _ _ ?_ ?_ ?_
  · rw [e1, normSq_mul, hu, one_mul, h1]
  · rw [e2, normSq_mul, hu, one_mul, h2]
  · rw [e3, normSq_mul, hu, one_mul, h3]

/-- Planar algebra: two vectors orthogonal to a common nonzero vector and of equal length
are equal or opposite. -/
theorem perp_eq_or_neg {a1 a2 b1 b2 d1 d2 : ℝ}
    (ha : a1 * d1 + a2 * d2 = 0) (hb : b1 * d1 + b2 * d2 = 0)
    (hn : a1 ^ 2 + a2 ^ 2 = b1 ^ 2 + b2 ^ 2) (hd : d1 ^ 2 + d2 ^ 2 ≠ 0) :
    (a1 = b1 ∧ a2 = b2) ∨ (a1 = -b1 ∧ a2 = -b2) := by
  have hdet : a1 * b2 - a2 * b1 = 0 := by
    rcases eq_or_ne d1 0 with h1 | h1
    · have h2 : d2 ≠ 0 := fun h2 => hd (by rw [h1, h2]; ring)
      have ea : a2 * d2 = 0 := by rw [h1] at ha; linarith
      have eb : b2 * d2 = 0 := by rw [h1] at hb; linarith
      have hz : d2 * (a1 * b2 - a2 * b1) = 0 := by linear_combination a1 * eb - b1 * ea
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h h2
      · exact h
    · have hz : d1 * (a1 * b2 - a2 * b1) = 0 := by linear_combination b2 * ha - a2 * hb
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h h1
      · exact h
  have key : ((a1 - b1) ^ 2 + (a2 - b2) ^ 2) * ((a1 + b1) ^ 2 + (a2 + b2) ^ 2) = 0 := by
    linear_combination ((a1 ^ 2 + a2 ^ 2) - (b1 ^ 2 + b2 ^ 2)) * hn +
      (4 * (a1 * b2 - a2 * b1)) * hdet
  rcases mul_eq_zero.1 key with h | h
  · left
    have h1 : (a1 - b1) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 - b1), sq_nonneg (a2 - b2)]
    have h2 : (a2 - b2) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 - b1), sq_nonneg (a2 - b2)]
    constructor
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1; linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2; linarith
  · right
    have h1 : (a1 + b1) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 + b1), sq_nonneg (a2 + b2)]
    have h2 : (a2 + b2) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 + b1), sq_nonneg (a2 + b2)]
    constructor
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1; linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2; linarith

/-- Given a segment `p q` of squared length 3, there are at most two points at squared
distance 3 from both endpoints, and they are reflections of one another. -/
theorem apex_unique {p q r s : ℂ} (hpq : normSq (p - q) = 3)
    (hr1 : normSq (p - r) = 3) (hr2 : normSq (q - r) = 3)
    (hs1 : normSq (p - s) = 3) (hs2 : normSq (q - s) = 3) :
    r = s ∨ r = p + q - s := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im] at hpq hr1 hr2 hs1 hs2
  have hA : (r.re - (p.re + q.re) / 2) * ((q.re - p.re) / 2) +
      (r.im - (p.im + q.im) / 2) * ((q.im - p.im) / 2) = 0 := by
    linear_combination hr1 / 4 - hr2 / 4
  have hB : (s.re - (p.re + q.re) / 2) * ((q.re - p.re) / 2) +
      (s.im - (p.im + q.im) / 2) * ((q.im - p.im) / 2) = 0 := by
    linear_combination hs1 / 4 - hs2 / 4
  have hN : (r.re - (p.re + q.re) / 2) ^ 2 + (r.im - (p.im + q.im) / 2) ^ 2 =
      (s.re - (p.re + q.re) / 2) ^ 2 + (s.im - (p.im + q.im) / 2) ^ 2 := by
    linear_combination hr1 / 2 + hr2 / 2 - hs1 / 2 - hs2 / 2
  have hD : ((q.re - p.re) / 2) ^ 2 + ((q.im - p.im) / 2) ^ 2 ≠ 0 := by
    have h : ((q.re - p.re) / 2) ^ 2 + ((q.im - p.im) / 2) ^ 2 = 3 / 4 := by
      linear_combination hpq / 4
    rw [h]; norm_num
  rcases perp_eq_or_neg hA hB hN hD with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    exact Complex.ext (by linarith) (by linarith)
  · right
    refine Complex.ext ?_ ?_
    · simp only [Complex.add_re, Complex.sub_re]; linarith
    · simp only [Complex.add_im, Complex.sub_im]; linarith

end CNP

