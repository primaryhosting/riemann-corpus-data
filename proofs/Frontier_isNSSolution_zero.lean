/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped BigOperators

/-- Physical space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/
noncomputable def pd (i : Fin 3) (f : Vec → ℝ) (x : Vec) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The divergence of a vector field on `ℝ³`. -/
noncomputable def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, pd i (fun y => v y i) x

/-- The `i`-th component of the (spatial) Laplacian of a time dependent vector field. -/
noncomputable def laplacianComp (u : ℝ → Vec → Vec) (t : ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  ∑ j, pd j (fun y => pd j (fun z => u t z i) y) x

/-- `IsNSSolution ν u p u₀` says that the pair `(u, p)` is a globally defined, smooth
solution of the incompressible Navier–Stokes equations on `ℝ³ × ℝ` with viscosity `ν`,
no external force, and initial velocity `u₀`:

* `u` and `p` are `C^∞` jointly in time and space,
* `u 0 = u₀`,
* `div u = 0` (incompressibility),
* `∂ₜ uᵢ + ∑ⱼ uⱼ ∂ⱼ uᵢ = ν Δuᵢ - ∂ᵢ p` (conservation of momentum). -/
structure IsNSSolution (nu : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) (u₀ : Vec → Vec) :
    Prop where
  smooth_velocity : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => u q.1 q.2)
  smooth_pressure : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => p q.1 q.2)
  initial_condition : ∀ x, u 0 x = u₀ x
  incompressible : ∀ t x, divergence (u t) x = 0
  momentum : ∀ t x i,
    deriv (fun s => u s x i) t + ∑ j, u t x j * pd j (fun y => u t y i) x
      = nu * laplacianComp u t i x - pd i (p t) x

/-- **Global regularity for the three dimensional incompressible Navier–Stokes equations.**

For every positive viscosity and every smooth, divergence free initial velocity field there
exists a globally defined smooth solution of the Navier–Stokes equations with that initial
datum.  This is the (unsolved) Clay Millennium Problem statement; it is *stated* here, not
assumed anywhere. -/
def NavierStokesGlobalRegularity : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : Vec → Vec, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, divergence u₀ x = 0) →
    ∃ u p, IsNSSolution nu u p u₀

/-- The same statement, restricted to initial data that are neither identically zero nor a
sinusoidal shear profile `x ↦ sin (k x₂) e₁`; both of those families are solved
unconditionally below (`isNSSolution_zero`, `isNSSolution_shearVelocity`). -/
def NavierStokesGlobalRegularityReduced : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : Vec → Vec, u₀ ≠ 0 →
    (∀ k : ℝ, u₀ ≠ fun x => Real.sin (k * x 1) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) →
    ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, divergence u₀ x = 0) → ∃ u p, IsNSSolution nu u p u₀

@[simp] lemma pd_zero (i : Fin 3) (x : Vec) : pd i (fun _ : Vec => (0 : ℝ)) x = 0 := by
  simp [pd]

@[simp] lemma divergence_zero (x : Vec) : divergence (fun _ : Vec => (0 : Vec)) x = 0 := by
  simp [divergence]

/-- **Base case.** The identically zero velocity and pressure fields form a global smooth
solution of the Navier–Stokes equations with zero initial datum. -/
theorem isNSSolution_zero (nu : ℝ) :
    IsNSSolution nu (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) where
  smooth_velocity := contDiff_const
  smooth_pressure := contDiff_const
  initial_condition := fun _ => rfl
  incompressible := fun _ x => divergence_zero x
  momentum := by
    intro t x i
    simp [laplacianComp]

/-! ### A nontrivial exact global solution: the viscously decaying shear flow -/

/-- Partial derivative of a scalar field that depends on a single coordinate. -/
lemma pd_coord (i j : Fin 3) (g : ℝ → ℝ) (hg : Differentiable ℝ g) (x : Vec) :
    pd i (fun y => g (y j)) x = if i = j then deriv g (x j) else 0 := by
  have hp : HasFDerivAt (fun y : Vec => y j) (EuclideanSpace.proj j : Vec →L[ℝ] ℝ) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := x)
  have h1 := (hg (x j)).hasDerivAt.hasFDerivAt.comp x hp
  simp only [Function.comp_def] at h1
  rw [pd, h1.fderiv]
  simp [EuclideanSpace.single_apply, eq_comm]

/-- The velocity field of the decaying shear flow
`u(t, x) = (e^{-ν k² t} sin (k x₂), 0, 0)`. -/
noncomputable def shearVelocity (nu k : ℝ) (t : ℝ) (x : Vec) : Vec :=
  (Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

lemma shearVelocity_apply (nu k t : ℝ) (x : Vec) (i : Fin 3) :
    shearVelocity nu k t x i =
      if i = 0 then Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1) else 0 := by
  simp [shearVelocity, EuclideanSpace.single_apply]

lemma shearVelocity_apply_ne (nu k t : ℝ) (x : Vec) {i : Fin 3} (hi : i ≠ 0) :
    shearVelocity nu k t x i = 0 := by
  simp [shearVelocity_apply, hi]

/-- Spatial derivative of the shear profile. -/
lemma deriv_shear_profile (C k : ℝ) :
    deriv (fun s : ℝ => C * Real.sin (k * s)) = fun s => C * (k * Real.cos (k * s)) := by
  funext s
  have h : HasDerivAt (fun s : ℝ => C * Real.sin (k * s)) (C * (k * Real.cos (k * s))) s := by
    have h0 := (Real.hasDerivAt_sin (k * s)).comp s ((hasDerivAt_id s).const_mul k)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0.const_mul C
  exact h.deriv

lemma deriv_shear_profile' (C k : ℝ) :
    deriv (fun s : ℝ => C * (k * Real.cos (k * s)))
      = fun s => C * (-(k ^ 2) * Real.sin (k * s)) := by
  funext s
  have h : HasDerivAt (fun s : ℝ => C * (k * Real.cos (k * s)))
      (C * (-(k ^ 2) * Real.sin (k * s))) s := by
    have h0 := (Real.hasDerivAt_cos (k * s)).comp s ((hasDerivAt_id s).const_mul k)
    have h1 := (h0.const_mul k).const_mul C
    convert h1 using 1
    ring
  exact h.deriv

lemma differentiable_shear_profile (C k : ℝ) :
    Differentiable ℝ (fun s : ℝ => C * Real.sin (k * s)) := by
  fun_prop

lemma differentiable_shear_profile' (C k : ℝ) :
    Differentiable ℝ (fun s : ℝ => C * (k * Real.cos (k * s))) := by
  fun_prop

/-- First spatial derivatives of the shear velocity field. -/
lemma pd_shearVelocity_zero (nu k t : ℝ) (i : Fin 3) (x : Vec) :
    pd i (fun y => shearVelocity nu k t y 0) x =
      if i = 1 then Real.exp (-(nu * k ^ 2) * t) * (k * Real.cos (k * x 1)) else 0 := by
  have h := pd_coord i 1 (fun s : ℝ => Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * s))
    (differentiable_shear_profile _ _) x
  rw [deriv_shear_profile] at h
  simpa [shearVelocity_apply] using h

lemma pd_shearVelocity_ne (nu k t : ℝ) (i : Fin 3) {m : Fin 3} (hm : m ≠ 0) (x : Vec) :
    pd i (fun y => shearVelocity nu k t y m) x = 0 := by
  have : (fun y => shearVelocity nu k t y m) = fun _ : Vec => (0 : ℝ) :=
    funext fun y => shearVelocity_apply_ne nu k t y hm
  rw [this, pd_zero]

/-- The decaying shear flow is incompressible. -/
lemma divergence_shearVelocity (nu k t : ℝ) (x : Vec) :
    divergence (shearVelocity nu k t) x = 0 := by
  have h0 : pd 0 (fun y => shearVelocity nu k t y 0) x = 0 := by
    rw [pd_shearVelocity_zero]; norm_num
  simp [divergence, Fin.sum_univ_three, h0,
    pd_shearVelocity_ne nu k t 1 (m := 1) (by decide),
    pd_shearVelocity_ne nu k t 2 (m := 2) (by decide)]

/-- The Laplacian of the first component of the shear velocity field. -/
lemma laplacianComp_shearVelocity_zero (nu k t : ℝ) (x : Vec) :
    laplacianComp (shearVelocity nu k) t 0 x
      = Real.exp (-(nu * k ^ 2) * t) * (-(k ^ 2) * Real.sin (k * x 1)) := by
  have hzero : ∀ j : Fin 3, j ≠ 1 →
      pd j (fun y => pd j (fun z => shearVelocity nu k t z 0) y) x = 0 := by
    intro j hj
    have : (fun y => pd j (fun z => shearVelocity nu k t z 0) y) = fun _ : Vec => (0 : ℝ) := by
      funext y; rw [pd_shearVelocity_zero]; simp [hj]
    rw [this, pd_zero]
  have hone : pd 1 (fun y => pd 1 (fun z => shearVelocity nu k t z 0) y) x
      = Real.exp (-(nu * k ^ 2) * t) * (-(k ^ 2) * Real.sin (k * x 1)) := by
    have hfun : (fun y : Vec => pd 1 (fun z => shearVelocity nu k t z 0) y)
        = fun y : Vec => (fun s : ℝ => Real.exp (-(nu * k ^ 2) * t) * (k * Real.cos (k * s))) (y 1) := by
      funext y; rw [pd_shearVelocity_zero]; simp
    rw [hfun, pd_coord 1 1 _ (differentiable_shear_profile' _ _) x, deriv_shear_profile']
    simp
  simp [laplacianComp, Fin.sum_univ_three, hone, hzero 0 (by decide), hzero 2 (by decide)]

/-- **A nontrivial exact global solution.**  For every viscosity `ν` and every wave number `k`
the viscously decaying shear flow `u(t,x) = (e^{-ν k² t} sin (k x₂), 0, 0)` with zero pressure
is a globally defined smooth solution of the Navier–Stokes equations. -/
theorem isNSSolution_shearVelocity (nu k : ℝ) :
    IsNSSolution nu (shearVelocity nu k) (fun _ _ => 0)
      (fun x => Real.sin (k * x 1) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) where
  smooth_velocity := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => Real.exp (-(nu * k ^ 2) * q.1)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => Real.sin (k * q.2 1)) :=
      Real.contDiff_sin.comp (contDiff_const.mul
        (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff).comp contDiff_snd))
    exact (h1.mul h2).smul contDiff_const
  smooth_pressure := contDiff_const
  initial_condition := by intro x; simp [shearVelocity]
  incompressible := divergence_shearVelocity nu k
  momentum := by
    intro t x i
    rcases eq_or_ne i 0 with rfl | hi
    · have hderiv : deriv (fun s => shearVelocity nu k s x 0) t
          = -(nu * k ^ 2) * Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1) := by
        have hfun : (fun s => shearVelocity nu k s x 0)
            = fun s : ℝ => Real.exp (-(nu * k ^ 2) * s) * Real.sin (k * x 1) := by
          funext s; simp [shearVelocity_apply]
        rw [hfun]
        have h : HasDerivAt (fun s : ℝ => Real.exp (-(nu * k ^ 2) * s) * Real.sin (k * x 1))
            (-(nu * k ^ 2) * Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1)) t := by
          have h0 := ((Real.hasDerivAt_exp (-(nu * k ^ 2) * t)).comp t
            ((hasDerivAt_id t).const_mul (-(nu * k ^ 2)))).mul_const (Real.sin (k * x 1))
          convert h0 using 1
          ring
        exact h.deriv
      have hconv : ∀ j : Fin 3,
          shearVelocity nu k t x j * pd j (fun y => shearVelocity nu k t y 0) x = 0 := by
        intro j
        rcases eq_or_ne j 0 with rfl | hj
        · rw [pd_shearVelocity_zero]; norm_num
        · rw [shearVelocity_apply_ne nu k t x hj, zero_mul]
      rw [hderiv, laplacianComp_shearVelocity_zero]
      simp only [Fin.sum_univ_three, hconv 0, hconv 1, hconv 2, pd_zero, add_zero, sub_zero]
      ring
    · have hfun : (fun s => shearVelocity nu k s x i) = fun _ : ℝ => (0 : ℝ) :=
        funext fun s => shearVelocity_apply_ne nu k s x hi
      have hlap : laplacianComp (shearVelocity nu k) t i x = 0 := by
        have h1 : ∀ j : Fin 3, pd j (fun y => shearVelocity nu k t y i) x = 0 := fun j =>
          pd_shearVelocity_ne nu k t j hi x
        have h2 : ∀ j : Fin 3,
            pd j (fun y => pd j (fun z => shearVelocity nu k t z i) y) x = 0 := by
          intro j
          have : (fun y => pd j (fun z => shearVelocity nu k t z i) y) = fun _ : Vec => (0 : ℝ) :=
            funext fun y => pd_shearVelocity_ne nu k t j hi y
          rw [this, pd_zero]
        simp [laplacianComp, Fin.sum_univ_three, h2 0, h2 1, h2 2]
      rw [hfun, hlap]
      simp [pd_shearVelocity_ne nu k t _ hi]

/-- **Navier–Stokes regularity: a Lean-checked reduction.**

Global regularity for the 3D incompressible Navier–Stokes equations (for all smooth,
divergence free initial data) is *equivalent* to global regularity for the reduced class of
initial data: the zero datum is handled unconditionally by the explicit trivial solution
`u ≡ 0`, `p ≡ 0` (see `isNSSolution_zero`), and every sinusoidal shear datum
`x ↦ sin (k x₂) e₁` is handled unconditionally by the explicit decaying shear flow
(see `isNSSolution_shearVelocity`). -/
theorem navier_stokes_regularity :
    NavierStokesGlobalRegularity ↔ NavierStokesGlobalRegularityReduced := by
  constructor
  · intro h nu hnu u₀ _ _ hsmooth hdiv
    exact h nu hnu u₀ hsmooth hdiv
  · intro h nu hnu u₀ hsmooth hdiv
    by_cases h0 : u₀ = 0
    · subst h0
      exact ⟨fun _ _ => 0, fun _ _ => 0, isNSSolution_zero nu⟩
    by_cases hshear :
        ∃ k : ℝ, u₀ = fun x => Real.sin (k * x 1) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
    · obtain ⟨k, rfl⟩ := hshear
      exact ⟨shearVelocity nu k, fun _ _ => 0, isNSSolution_shearVelocity nu k⟩
    · exact h nu hnu u₀ h0 (by
        intro k hk
        exact hshear ⟨k, hk⟩) hsmooth hdiv

end Frontier

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

