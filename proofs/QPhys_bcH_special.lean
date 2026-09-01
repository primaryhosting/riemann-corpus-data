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

namespace QPhys

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- In a Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_of_commute' (Commute.neg_right (Commute.refl x))]
  simp

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  simpa using exp_mul_exp_neg (-x)

/-- If the commutator `C = AB - BA` is central, then `e^{tA} B e^{-tA} = B + t C`. -/
theorem exp_conj_of_central (A B C : 𝔸) (hC : A * B - B * A = C)
    (hcentral : ∀ x : 𝔸, Commute C x) (t : ℝ) :
    exp (t • A) * B * exp (-(t • A)) = B + t • C := by
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • A) * B * exp (-(u • A)) - u • C) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have h2 : HasDerivAt (fun u : ℝ => exp (-(u • A))) (exp (-(s • A)) * (-A)) s := by
      have := hasDerivAt_exp_smul_const (-A) s
      simpa [smul_neg] using this
    have h5 := ((h1.mul_const B).mul h2).sub
      (by simpa using (hasDerivAt_id s).smul_const C :
        HasDerivAt (fun u : ℝ => u • C) C s)
    have hcomm : Commute A (exp (-(s • A))) :=
      (((Commute.refl A).smul_right s).neg_right).exp_right
    have e1 : exp (-(s • A)) * (-A) = (-A) * exp (-(s • A)) := by
      have h := hcomm.symm
      simp only [Commute, SemiconjBy] at h
      simp [mul_neg, neg_mul, h]
    have hXY : exp (s • A) * exp (-(s • A)) = 1 := exp_mul_exp_neg _
    have hzero : exp (s • A) * A * B * exp (-(s • A))
        + exp (s • A) * B * (exp (-(s • A)) * -A) - C = 0 := by
      rw [e1]
      have h6 : exp (s • A) * A * B * exp (-(s • A)) + exp (s • A) * B * (-A * exp (-(s • A)))
           = exp (s • A) * (C * exp (-(s • A))) := by
        rw [← hC]; noncomm_ring
      rw [h6, (hcentral (exp (-(s • A)))).eq, ← mul_assoc, hXY, one_mul, sub_self]
    rw [hzero] at h5
    exact h5
  have hdiff : Differentiable ℝ (fun u : ℝ => exp (u • A) * B * exp (-(u • A)) - u • C) :=
    fun s => (key s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (key s).deriv) t 0
  simp only [zero_smul, sub_zero, NormedSpace.exp_zero, one_mul, mul_one,
    neg_zero] at hconst
  have := hconst
  rw [sub_eq_iff_eq_add] at this
  simpa [add_comm] using this

/-- Commutation rule: `e^{tA} B = (B + t C) e^{tA}` when `C = [A,B]` is central. -/
theorem exp_mul_of_central (A B C : 𝔸) (hC : A * B - B * A = C)
    (hcentral : ∀ x : 𝔸, Commute C x) (t : ℝ) :
    exp (t • A) * B = (B + t • C) * exp (t • A) := by
  have h := exp_conj_of_central A B C hC hcentral t
  have := congrArg (fun z => z * exp (t • A)) h
  simp only [mul_assoc] at this
  rw [exp_neg_mul_exp] at this
  simpa [mul_assoc] using this

/-- **Baker–Campbell–Hausdorff, special case.**  If the commutator `[A, B] = AB - BA` is
central (commutes with every element of the algebra), then
`e^A e^B = e^{A + B + ½ [A, B]}`. -/
theorem bcH_special (A B : 𝔸) (hcentral : ∀ x : 𝔸, Commute (A * B - B * A) x) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) := by
  set C := A * B - B * A with hCdef
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ =>
      exp (u • (-(A + B))) * exp ((u ^ 2 / 2) • (-C)) * (exp (u • A) * exp (u • B))) 0 s := by
    intro s
    have hW : HasDerivAt (fun u : ℝ => exp (u • (-(A + B)))) (exp (s • (-(A + B))) * (-(A + B))) s :=
      hasDerivAt_exp_smul_const _ s
    have hZ : HasDerivAt (fun u : ℝ => exp ((u ^ 2 / 2) • (-C)))
        (s • (exp ((s ^ 2 / 2) • (-C)) * (-C))) s := by
      have h₁ := hasDerivAt_exp_smul_const (-C) (s ^ 2 / 2)
      have h₂ : HasDerivAt (fun u : ℝ => u ^ 2 / 2) s s := by
        simpa using ((hasDerivAt_pow 2 s).div_const 2)
      simpa [Function.comp] using h₁.scomp s h₂
    have hU : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have hV : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const B s
    have hk := (hW.mul hZ).mul (hU.mul hV)
    simp only [Pi.mul_apply] at hk
    have hZc : ∀ x : 𝔸, exp ((s ^ 2 / 2) • (-C)) * x = x * exp ((s ^ 2 / 2) • (-C)) :=
      fun x => ((((hcentral x).neg_left).smul_left (s ^ 2 / 2)).exp_left).eq
    have hUA : exp (s • A) * A = A * exp (s • A) := (((Commute.refl A).smul_left s).exp_left).eq
    have hVB : exp (s • B) * B = B * exp (s • B) := (((Commute.refl B).smul_left s).exp_left).eq
    have hUB : exp (s • A) * B = (B + s • C) * exp (s • A) :=
      exp_mul_of_central A B C hCdef.symm hcentral s
    have hzero : (exp (s • (-(A + B))) * (-(A + B)) * exp ((s ^ 2 / 2) • (-C))
          + exp (s • (-(A + B))) * (s • (exp ((s ^ 2 / 2) • (-C)) * (-C))))
            * (exp (s • A) * exp (s • B))
        + exp (s • (-(A + B))) * exp ((s ^ 2 / 2) • (-C))
            * (exp (s • A) * A * exp (s • B) + exp (s • A) * (exp (s • B) * B)) = 0 := by
      set W := exp (s • (-(A + B)))
      set Z := exp ((s ^ 2 / 2) • (-C))
      set U := exp (s • A)
      set V := exp (s • B)
      have k1 : W * -(A + B) * Z * (U * V) = -(W * Z * A * (U * V)) - W * Z * B * (U * V) := by
        rw [mul_assoc W, ← hZc (-(A + B))]; noncomm_ring
      have k2 : W * (s • (Z * -C)) * (U * V) = -(s • (W * Z * C * (U * V))) := by
        have h : W * (Z * -C) * (U * V) = -(W * Z * C * (U * V)) := by noncomm_ring
        rw [mul_smul_comm, smul_mul_assoc, h, smul_neg]
      have k3 : W * Z * (U * A * V) = W * Z * A * (U * V) := by rw [hUA]; noncomm_ring
      have k4 : W * Z * (U * (V * B)) = W * Z * B * (U * V) + s • (W * Z * C * (U * V)) := by
        rw [hVB, ← mul_assoc U, hUB, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_add,
          mul_smul_comm]
        congr 1 <;> noncomm_ring
      rw [add_mul, mul_add, k1, k2, k3, k4]
      abel
    rw [hzero] at hk
    exact hk
  have hdiff : Differentiable ℝ (fun u : ℝ =>
      exp (u • (-(A + B))) * exp ((u ^ 2 / 2) • (-C)) * (exp (u • A) * exp (u • B))) :=
    fun s => (key s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (key s).deriv) 1 0
  simp only [one_smul, one_pow, zero_smul, show ((0 : ℝ) ^ 2 / 2) = 0 by norm_num,
    NormedSpace.exp_zero, mul_one] at hconst
  -- `hconst : exp (-(A+B)) * exp ((1/2 : ℝ) • (-C)) * (exp A * exp B) = 1`
  have hcomm : Commute (-(A + B)) (((1 : ℝ) / 2) • (-C)) :=
    (((hcentral (-(A + B))).neg_left).smul_left ((1 : ℝ) / 2)).symm
  have hsplit : exp (-(A + B)) * exp (((1 : ℝ) / 2) • (-C))
      = exp (-(A + B + ((1 : ℝ) / 2) • C)) := by
    rw [← exp_add_of_commute' hcomm]
    congr 1
    module
  rw [hsplit] at hconst
  calc exp A * exp B
      = exp (A + B + ((1 : ℝ) / 2) • C) * exp (-(A + B + ((1 : ℝ) / 2) • C)) * (exp A * exp B) := by
        rw [exp_mul_exp_neg, one_mul]
    _ = exp (A + B + ((1 : ℝ) / 2) • C) * (exp (-(A + B + ((1 : ℝ) / 2) • C)) * (exp A * exp B)) := by
        rw [mul_assoc]
    _ = exp (A + B + ((1 : ℝ) / 2) • C) := by rw [hconst, mul_one]

end QPhys

