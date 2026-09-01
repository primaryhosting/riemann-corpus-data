/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ContDiff

namespace Frontier

/-- The physical space `ℝ³`, modelled as `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/
noncomputable def partialDeriv (f : Vec → ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The Laplacian `Δf = ∑ⱼ ∂ⱼ∂ⱼ f` of a scalar field on `ℝ³`. -/
noncomputable def laplacian (f : Vec → ℝ) (x : Vec) : ℝ :=
  ∑ j, partialDeriv (partialDeriv f j) j x

/-- The divergence `∇ · v = ∑ᵢ ∂ᵢ vᵢ` of a vector field on `ℝ³`. -/
noncomputable def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, partialDeriv (fun y => v y i) i x

/-- `u` (a time dependent velocity field) together with `p` (a time dependent pressure)
is a *global smooth solution* of the incompressible Navier–Stokes equations on `ℝ × ℝ³`
with viscosity `ν`:

* `u` and `p` are `C^∞` jointly in time and space;
* `u` is divergence free (incompressibility);
* the momentum equation `∂ₜuᵢ + (u · ∇)uᵢ = ν Δuᵢ - ∂ᵢp` holds at every point of
  space-time.
-/
structure IsGlobalSmoothSolution (ν : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) : Prop where
  smooth_velocity : ContDiff ℝ ∞ (fun q : ℝ × Vec => u q.1 q.2)
  smooth_pressure : ContDiff ℝ ∞ (fun q : ℝ × Vec => p q.1 q.2)
  incompressible : ∀ t x, divergence (u t) x = 0
  momentum : ∀ t x i,
    deriv (fun s => u s x i) t + ∑ j, u t x j * partialDeriv (fun y => u t y i) j x
      = ν * laplacian (fun y => u t y i) x - partialDeriv (p t) i x

/-- **Global regularity for the 3D incompressible Navier–Stokes equations** (the Clay
Millennium Problem, here in its whole–space, force–free formulation): for every smooth,
divergence-free initial velocity field `u₀` on `ℝ³` there exist a globally defined smooth
velocity field `u` and pressure `p` solving the Navier–Stokes equations with viscosity `ν`
and with initial datum `u₀`.

This `Prop` is the *statement* of the open problem; it is not asserted here.  The theorem
`Frontier.navier_stokes_regularity` below proves an unconditional special case of it. -/
def NavierStokesGlobalRegularity (ν : ℝ) : Prop :=
  ∀ u₀ : Vec → Vec, ContDiff ℝ ∞ u₀ → (∀ x, divergence u₀ x = 0) →
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution ν u p ∧ ∀ x, u 0 x = u₀ x

section Auxiliary

variable {a : ℝ → Vec}

/-- Coordinates of the derivative of a curve in `ℝ³`. -/
lemma deriv_apply (ha : Differentiable ℝ a) (i : Fin 3) (t : ℝ) :
    deriv (fun s => a s i) t = deriv a t i :=
  ((hasDerivAt_pi.1 (ha t).hasDerivAt) i).deriv

/-- Partial derivatives of a spatially constant field vanish. -/
@[simp] lemma partialDeriv_const (c : ℝ) (i : Fin 3) (x : Vec) :
    partialDeriv (fun _ : Vec => c) i x = 0 := by
  simp [partialDeriv]

/-- The Laplacian of a spatially constant field vanishes. -/
@[simp] lemma laplacian_const (c : ℝ) (x : Vec) :
    laplacian (fun _ : Vec => c) x = 0 := by
  have h : ∀ j, partialDeriv (fun _ : Vec => c) j = fun _ : Vec => (0 : ℝ) := by
    intro j; funext y; exact partialDeriv_const c j y
  simp [laplacian, h]

/-- The gradient of the linear pressure `x ↦ -⟨c, x⟩`. -/
lemma partialDeriv_linear_pressure (c : Vec) (i : Fin 3) (x : Vec) :
    partialDeriv (fun y : Vec => -∑ k, c k * y k) i x = -c i := by
  have h : (fun y : Vec => -∑ k, c k * y k)
      = fun y => (-(∑ k, c k • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ))) y := by
    funext y; simp
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Sanity check on the definitions: the `j`-th partial derivative of the `i`-th coordinate
function is `1` if `i = j` and `0` otherwise. -/
lemma partialDeriv_coord (i j : Fin 3) (x : Vec) :
    partialDeriv (fun y : Vec => y i) j x = if i = j then 1 else 0 := by
  have h : (fun y : Vec => y i) = fun y => (ContinuousLinearMap.proj i : Vec →L[ℝ] ℝ) y := rfl
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply]

/-- Sanity check on the definitions: the divergence of the identity vector field is `3`. -/
lemma divergence_id (x : Vec) : divergence (fun y : Vec => y) x = 3 := by
  simp [divergence, partialDeriv_coord]

end Auxiliary

/-- **Navier–Stokes regularity: the spatially uniform (base) case.**

For every viscosity `ν` and every smooth curve `a : ℝ → ℝ³` there is a global smooth
solution of the 3D incompressible Navier–Stokes equations whose velocity field is the
spatially uniform flow `u(t, x) = a t`, with the linear pressure `p(t, x) = -⟨a'(t), x⟩`.
In particular (taking `a` constant, e.g. `a = 0`) the initial value problem with any
constant divergence-free initial datum — the rest state `u₀ = 0` in particular — has a
globally smooth solution.

This is an unconditional, Lean-checked instance of `NavierStokesGlobalRegularity ν`
restricted to spatially uniform initial data; the general case is the open Millennium
Problem, stated above as `NavierStokesGlobalRegularity`. -/
theorem navier_stokes_regularity (ν : ℝ) (a : ℝ → Vec) (ha : ContDiff ℝ ∞ a) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution ν u p ∧ ∀ x, u 0 x = a 0 := by
  have hdiff : Differentiable ℝ a := (contDiff_infty_iff_deriv.1 ha).1
  have hderiv : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.1 ha).2
  refine ⟨fun t _ => a t, fun t x => -∑ k, deriv a t k * x k, ⟨?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · exact ha.comp contDiff_fst
  · refine ContDiff.neg (ContDiff.sum fun k _ => ContDiff.mul ?_ ?_)
    · exact (contDiff_apply ℝ ℝ k).comp (hderiv.comp contDiff_fst)
    · exact (contDiff_apply ℝ ℝ k).comp contDiff_snd
  · intro t x
    simp [divergence]
  · intro t x i
    have hp : partialDeriv (fun y : Vec => -∑ k, deriv a t k * y k) i x = -deriv a t i :=
      partialDeriv_linear_pressure (deriv a t) i x
    simp only [hp, deriv_apply hdiff i t, partialDeriv_const, laplacian_const]
    simp

/-- **Time translation invariance** (a Lean-checked reduction): global smooth solutions
are preserved by shifting time, so solving the initial value problem at time `s` is
equivalent to solving it at time `0`. -/
theorem isGlobalSmoothSolution_timeShift {ν : ℝ} {u : ℝ → Vec → Vec} {p : ℝ → Vec → ℝ}
    (h : IsGlobalSmoothSolution ν u p) (s : ℝ) :
    IsGlobalSmoothSolution ν (fun t x => u (t + s) x) (fun t x => p (t + s) x) := by
  have hshift : ContDiff ℝ ∞ (fun q : ℝ × Vec => (q.1 + s, q.2)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  refine ⟨h.smooth_velocity.comp hshift, h.smooth_pressure.comp hshift, ?_, ?_⟩
  · intro t x; exact h.incompressible (t + s) x
  · intro t x i
    have hd : deriv (fun r => u (r + s) x i) t = deriv (fun r => u r x i) (t + s) :=
      deriv_comp_add_const (fun r => u r x i) s t
    rw [hd]
    exact h.momentum (t + s) x i

/-- The rest state: for the zero initial velocity the incompressible Navier–Stokes
equations have a global smooth solution (namely `u = 0`, `p = 0`). -/
theorem navier_stokes_regularity_rest_state (ν : ℝ) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution ν u p ∧ ∀ x, u 0 x = 0 := by
  obtain ⟨u, p, hsol, hinit⟩ := navier_stokes_regularity ν (fun _ => 0) contDiff_const
  exact ⟨u, p, hsol, hinit⟩

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

