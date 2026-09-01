import Mathlib
/-!
# The quantum Fourier transform on ℤ/d is unitary (up to the normalization d).
Bare `import Mathlib`; may use Mathlib's ZMod additive-character / Gauss-sum machinery. TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- The **quantum Fourier transform** matrix on `ZMod d`: `W j k = ω^{jk}`, `ω = exp(2πi/d)`. -/
noncomputable def qft : Matrix (ZMod d) (ZMod d) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * ((j.val * k.val : ℕ) : ℂ) / d)

/-- The QFT is unitary up to normalization: `W * Wᴴ = d • 1`
(character orthogonality `∑_{k} ω^{(j−l)k} = d·[j = l]`). -/
theorem qft_mul_conjTranspose :
    qft d * (qft d)ᴴ = (d : ℂ) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  classical
  -- The entries of `qft` are the values of the standard additive character of `ZMod d`.
  have hq : ∀ a b : ZMod d, qft d a b = ZMod.stdAddChar (a * b) := by
    intro a b
    have h : ((a * b : ZMod d)) = (((a.val * b.val : ℕ) : ℤ) : ZMod d) := by
      push_cast
      simp [ZMod.natCast_val]
    rw [h, ZMod.stdAddChar_coe]
    simp [qft]
  -- Character values lie on the unit circle, so conjugation is negation of the argument.
  have hconj : ∀ x : ZMod d, star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
    simp [← Circle.coe_inv_eq_conj]
  ext j l
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hq, hconj, ← AddChar.map_add_eq_mul]
  have hr : ∀ k : ZMod d, j * k + -(l * k) = (j - l) * k := by intro k; ring
  simp only [hr]
  by_cases hjl : j = l
  · -- Diagonal: every term is `1`, and there are `d` of them.
    subst hjl
    simp [Matrix.one_apply_eq, ZMod.card]
  · -- Off-diagonal: the shifted character is nontrivial, so its sum vanishes.
    have hsum : ∑ k : ZMod d, ZMod.stdAddChar ((j - l) * k) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d (sub_ne_zero.mpr hjl))
    rw [hsum]
    simp [Matrix.one_apply_ne hjl]

end BrockianQuantum

