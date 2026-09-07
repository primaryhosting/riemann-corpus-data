/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

variable {n : ℕ}

/-- The standard symplectic vector space `ℝ^(2n+2)`, realised as the Euclidean space with
index set `Fin (n+1) ⊕ Fin (n+1)`: the `Sum.inl` coordinates are the positions `q₀,…,qₙ`
and the `Sum.inr` coordinates are the conjugate momenta `p₀,…,pₙ`. -/
abbrev SymplecticSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin (n + 1))

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (x_{qᵢ} y_{pᵢ} - x_{pᵢ} y_{qᵢ})`. -/
def omegaForm (x y : SymplecticSpace n) : ℝ :=
  ∑ i : Fin (n + 1), (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i))

/-- The standard complex structure `J(q, p) = (p, -q)`; it relates the symplectic form and the
Euclidean inner product via `ω(x, y) = ⟪x, J y⟫`. -/
noncomputable def Jmap (p : SymplecticSpace n) : SymplecticSpace n :=
  WithLp.toLp 2 (fun j => Sum.elim (fun i => p (Sum.inr i)) (fun i => -p (Sum.inl i)) j)

@[simp] lemma Jmap_inl (p : SymplecticSpace n) (i : Fin (n + 1)) :
    Jmap p (Sum.inl i) = p (Sum.inr i) := by simp [Jmap]

@[simp] lemma Jmap_inr (p : SymplecticSpace n) (i : Fin (n + 1)) :
    Jmap p (Sum.inr i) = -p (Sum.inl i) := by simp [Jmap]

lemma norm_Jmap (p : SymplecticSpace n) : ‖Jmap p‖ = ‖p‖ := by
  simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  ring_nf

lemma omegaForm_eq_inner (x y : SymplecticSpace n) : omegaForm x y = ⟪x, Jmap y⟫ := by
  rw [PiLp.inner_apply]
  simp [omegaForm, Fintype.sum_sum_type, RCLike.inner_apply, Finset.sum_sub_distrib, mul_comm]
  ring

/-- Cauchy–Schwarz for the symplectic form: `|ω(x, y)| ≤ ‖x‖ ‖y‖`. -/
lemma abs_omegaForm_le (x y : SymplecticSpace n) : |omegaForm x y| ≤ ‖x‖ * ‖y‖ := by
  rw [omegaForm_eq_inner, ← norm_Jmap y]
  exact abs_real_inner_le_norm x (Jmap y)

/-- **Key intermediate lemma.**  If the linear functional `z ↦ ω(z, p)` is bounded in absolute
value by `R` on the open ball of radius `r`, then `r ‖p‖ ≤ R`.  This is the sharp bound, obtained
by evaluating the functional along the direction that is Euclidean-dual to `p`. -/
lemma norm_le_of_omegaForm_bound {r R : ℝ} (hr : 0 < r) (p : SymplecticSpace n)
    (h : ∀ z : SymplecticSpace n, ‖z‖ < r → |omegaForm z p| < R) : r * ‖p‖ ≤ R := by
  have hR : 0 < R := by
    have := h 0 (by simpa using hr)
    simpa [omegaForm] using this
  rcases eq_or_ne p 0 with rfl | hp
  · simp
    positivity
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  by_contra hcon
  push_neg at hcon
  have h1 : R / ‖p‖ < r := by rw [div_lt_iff₀ hpn]; linarith
  set t := (R / ‖p‖ + r) / 2 with ht
  have hRp : 0 < R / ‖p‖ := by positivity
  have ht1 : t < r := by rw [ht]; linarith
  have ht0 : 0 < t := by rw [ht]; linarith
  have htR : R / ‖p‖ < t := by rw [ht]; linarith
  set z : SymplecticSpace n := (t / ‖p‖) • Jmap p with hz
  have hzn : ‖z‖ = t := by
    rw [hz, norm_smul, norm_Jmap, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hval : omegaForm z p = t * ‖p‖ := by
    rw [omegaForm_eq_inner, hz, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_Jmap]
    field_simp
  have hlt := h z (by rw [hzn]; exact ht1)
  rw [hval, abs_of_pos (by positivity)] at hlt
  have := (div_lt_iff₀ hpn).mp htR
  linarith

lemma omegaForm_antisymm (x y : SymplecticSpace n) : omegaForm x y = -omegaForm y x := by
  unfold omegaForm
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (by intros; ring)

/-- The standard basis vector `e_{q₀}` (first position coordinate). -/
noncomputable def eq0 (n : ℕ) : SymplecticSpace n := EuclideanSpace.single (Sum.inl 0) 1

/-- The standard basis vector `e_{p₀}` (first momentum coordinate). -/
noncomputable def ep0 (n : ℕ) : SymplecticSpace n := EuclideanSpace.single (Sum.inr 0) 1

lemma omegaForm_eq0_ep0 : omegaForm (eq0 n) (ep0 n) = 1 := by
  simp [omegaForm, eq0, ep0, EuclideanSpace.single_apply]

lemma coord_inl_eq (z : SymplecticSpace n) : z (Sum.inl 0) = omegaForm z (ep0 n) := by
  simp [omegaForm, ep0, EuclideanSpace.single_apply]

lemma coord_inr_eq (z : SymplecticSpace n) : z (Sum.inr 0) = -omegaForm z (eq0 n) := by
  simp [omegaForm, eq0, EuclideanSpace.single_apply]

lemma Jmap_neg_Jmap (x : SymplecticSpace n) : Jmap (-(Jmap x)) = x := by
  ext j
  rcases j with i | i <;> simp

/-- The standard symplectic form is nondegenerate. -/
lemma eq_zero_of_omegaForm_eq_zero {x : SymplecticSpace n} (h : ∀ y, omegaForm x y = 0) :
    x = 0 := by
  have hx := h (-(Jmap x))
  rw [omegaForm_eq_inner, Jmap_neg_Jmap, real_inner_self_eq_norm_sq] at hx
  have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  simpa using this

/-- A linear map preserving the symplectic form is bijective (in finite dimensions). -/
lemma surjective_of_preserves_omegaForm (Ψ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n)
    (hsymp : ∀ x y : SymplecticSpace n, omegaForm (Ψ x) (Ψ y) = omegaForm x y) :
    Function.Surjective Ψ := by
  refine LinearMap.injective_iff_surjective.mp ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_omegaForm_eq_zero (fun y => ?_)
  rw [← hsymp x y, hx]
  simp [omegaForm]

/-- **Gromov's nonsqueezing theorem (linear symplectic case).**

If a linear symplectomorphism `Ψ` of the standard symplectic vector space `ℝ^{2n+2}` maps the
open ball of radius `r` into the symplectic cylinder
`Z(R) = {z | z_{q₀}² + z_{p₀}² < R²}`, then necessarily `r ≤ R`.

In other words, a ball can never be symplectically squeezed into a thinner cylinder whose
cross-section is spanned by a conjugate pair of coordinates. -/
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (Ψ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n)
    (hsymp : ∀ x y : SymplecticSpace n, omegaForm (Ψ x) (Ψ y) = omegaForm x y)
    (hsqueeze : ∀ z : SymplecticSpace n, ‖z‖ < r →
      (Ψ z (Sum.inl 0)) ^ 2 + (Ψ z (Sum.inr 0)) ^ 2 < R ^ 2) :
    r ≤ R := by
  obtain ⟨p, hΨp⟩ := surjective_of_preserves_omegaForm Ψ hsymp (ep0 n)
  obtain ⟨q, hΨq⟩ := surjective_of_preserves_omegaForm Ψ hsymp (eq0 n)
  -- the squeezing hypothesis, rewritten in terms of the symplectic form
  have key : ∀ z : SymplecticSpace n, ‖z‖ < r →
      (omegaForm z p) ^ 2 + (omegaForm z q) ^ 2 < R ^ 2 := by
    intro z hz
    have h1 : Ψ z (Sum.inl 0) = omegaForm z p := by
      rw [coord_inl_eq, ← hΨp, hsymp]
    have h2 : Ψ z (Sum.inr 0) = -omegaForm z q := by
      rw [coord_inr_eq, ← hΨq, hsymp]
    have h3 := hsqueeze z hz
    rw [h1, h2] at h3
    simpa using h3
  have hp : r * ‖p‖ ≤ R := by
    refine norm_le_of_omegaForm_bound hr p ?_
    intro z hz
    have h3 := key z hz
    have h4 : (omegaForm z p) ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (omegaForm z q)]
    nlinarith [abs_nonneg (omegaForm z p), sq_abs (omegaForm z p)]
  have hq : r * ‖q‖ ≤ R := by
    refine norm_le_of_omegaForm_bound hr q ?_
    intro z hz
    have h3 := key z hz
    have h4 : (omegaForm z q) ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (omegaForm z p)]
    nlinarith [abs_nonneg (omegaForm z q), sq_abs (omegaForm z q)]
  -- the two dual directions are symplectically conjugate, hence cannot both be short
  have hpq : omegaForm p q = -1 := by
    have h := hsymp p q
    rw [hΨp, hΨq] at h
    rw [← h, omegaForm_antisymm, omegaForm_eq0_ep0]
  have hone : (1 : ℝ) ≤ ‖p‖ * ‖q‖ := by
    have := abs_omegaForm_le p q
    rw [hpq] at this
    simpa using this
  nlinarith [norm_nonneg p, norm_nonneg q, mul_le_mul hp hq (by positivity) hR.le]

end Math2

