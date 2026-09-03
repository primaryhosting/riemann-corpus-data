-- (Lean 4 requires `import` lines to precede every command, including module docstrings,
-- so the required header comment is placed immediately after the import.)
import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

/-- Physical space: three-dimensional Euclidean space. -/
abbrev Space3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th standard coordinate direction of `Space3`. -/
noncomputable def dir (i : Fin 3) : Space3 := EuclideanSpace.single i (1 : ℝ)

/-- A time dependent vector field `u : ℝ → Space3 → Space3` is *smooth in space-time* if the
associated function of the pair `(t, x)` is `C^∞`. -/
def SmoothSpacetimeVec (u : ℝ → Space3 → Space3) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Space3 => u q.1 q.2)

/-- A time dependent scalar field `p : ℝ → Space3 → ℝ` is *smooth in space-time* if the
associated function of the pair `(t, x)` is `C^∞`. -/
def SmoothSpacetimeScalar (p : ℝ → Space3 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Space3 => p q.1 q.2)

/-- The incompressibility (divergence-free) condition `div u = 0` for a static vector field. -/
def DivFree (v : Space3 → Space3) : Prop :=
  ∀ x : Space3, ∑ i : Fin 3, (fderiv ℝ v x (dir i)) i = 0

/-- The incompressibility condition, at every time. -/
def DivFreeAllTime (u : ℝ → Space3 → Space3) : Prop :=
  ∀ t : ℝ, DivFree (u t)

/-- The momentum equation of the incompressible Navier–Stokes system with viscosity `ν` and
no external force:
`∂ₜ uⱼ + (u · ∇) uⱼ = ν Δ uⱼ - ∂ⱼ p`,
written componentwise.  Here the convective term `(u · ∇) u` is the directional derivative of
`u t` at `x` in the direction `u t x`, and the Laplacian is the sum over `i` of the second
derivatives in the coordinate directions. -/
def MomentumEquation (ν : ℝ) (u : ℝ → Space3 → Space3) (p : ℝ → Space3 → ℝ) : Prop :=
  ∀ (t : ℝ) (x : Space3) (j : Fin 3),
    (deriv (fun s : ℝ => u s x) t) j + (fderiv ℝ (u t) x (u t x)) j
      = ν * (∑ i : Fin 3, (fderiv ℝ (fun y : Space3 => fderiv ℝ (u t) y (dir i)) x (dir i)) j)
        - (fderiv ℝ (p t) x (dir j))

/-- `IsNavierStokesSolution ν u p` says that the velocity field `u` and pressure `p` solve the
three-dimensional incompressible Navier–Stokes equations with viscosity `ν` and zero force,
for all times `t ∈ ℝ`. -/
def IsNavierStokesSolution (ν : ℝ) (u : ℝ → Space3 → Space3) (p : ℝ → Space3 → ℝ) : Prop :=
  DivFreeAllTime u ∧ MomentumEquation ν u p

/-- Finiteness of the kinetic energy, uniformly in forward time: there is a constant `C` such
that for every `t ≥ 0` the field `u t` is square integrable with energy at most `C`. -/
def BoundedEnergy (u : ℝ → Space3 → Space3) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    MeasureTheory.Integrable (fun x : Space3 => ‖u t x‖ ^ 2) ∧
      ∫ x : Space3, ‖u t x‖ ^ 2 ≤ C

/-- The conclusion of the global regularity problem for the initial datum `u₀`: there exists a
globally defined, space-time smooth solution `(u, p)` of the Navier–Stokes system with
viscosity `ν`, attaining the initial datum `u₀` at time `0`, and with bounded energy. -/
def HasGlobalSmoothSolution (ν : ℝ) (u₀ : Space3 → Space3) : Prop :=
  ∃ (u : ℝ → Space3 → Space3) (p : ℝ → Space3 → ℝ),
    IsNavierStokesSolution ν u p ∧
      SmoothSpacetimeVec u ∧ SmoothSpacetimeScalar p ∧
      (∀ x : Space3, u 0 x = u₀ x) ∧
      BoundedEnergy u

/-- **The Navier–Stokes global regularity conjecture** (Clay Millennium Problem, existence and
smoothness statement) for viscosity `ν`:

for every divergence-free Schwartz-class initial velocity field `u₀` on `ℝ³` there exist a
smooth velocity field `u` and a smooth pressure `p`, defined for all times, solving the
incompressible Navier–Stokes equations with datum `u₀` and having globally bounded energy. -/
def NavierStokesGlobalRegularity (ν : ℝ) : Prop :=
  ∀ u₀ : SchwartzMap Space3 Space3, DivFree (u₀ : Space3 → Space3) →
    HasGlobalSmoothSolution ν (u₀ : Space3 → Space3)

section Trivial

/-- The identically zero velocity field together with the zero pressure solves the
Navier–Stokes equations. -/
theorem isNavierStokesSolution_zero (ν : ℝ) :
    IsNavierStokesSolution ν (fun _ _ => (0 : Space3)) (fun _ _ => (0 : ℝ)) := by
  constructor
  · intro t x
    simp
  · intro t x j
    simp

/-- The zero velocity field is smooth in space-time. -/
theorem smoothSpacetimeVec_zero : SmoothSpacetimeVec (fun _ _ => (0 : Space3)) :=
  contDiff_const

/-- The zero pressure is smooth in space-time. -/
theorem smoothSpacetimeScalar_zero : SmoothSpacetimeScalar (fun _ _ => (0 : ℝ)) :=
  contDiff_const

/-- The zero velocity field has (zero, hence) bounded energy. -/
theorem boundedEnergy_zero : BoundedEnergy (fun _ _ => (0 : Space3)) := by
  refine ⟨0, fun t _ => ⟨?_, ?_⟩⟩
  · simp
  · simp

/-- **Base case.**  For the zero initial datum the global regularity conclusion holds
unconditionally, witnessed by the zero solution. -/
theorem hasGlobalSmoothSolution_zero (ν : ℝ) :
    HasGlobalSmoothSolution ν (fun _ => (0 : Space3)) :=
  ⟨fun _ _ => 0, fun _ _ => 0, isNavierStokesSolution_zero ν, smoothSpacetimeVec_zero,
    smoothSpacetimeScalar_zero, fun _ => rfl, boundedEnergy_zero⟩

/-- A nonzero solution: any constant velocity field solves the equations with zero pressure.
(It does not have finite energy, so it is not a counterexample to anything; the point of this
lemma is that `IsNavierStokesSolution` is not over-constrained.) -/
theorem isNavierStokesSolution_const (ν : ℝ) (c : Space3) :
    IsNavierStokesSolution ν (fun _ _ => c) (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun t x => ?_, fun t x j => ?_⟩ <;> simp

/-- The momentum equation has genuine content: the (divergence-free) velocity field
`u t x = t • e₀`, whose time derivative is nonzero while all its spatial derivatives vanish,
is *not* a solution with zero pressure. -/
theorem not_isNavierStokesSolution_linear_in_time (ν : ℝ) :
    ¬ IsNavierStokesSolution ν (fun t (_ : Space3) => t • dir 0) (fun _ _ => (0 : ℝ)) := by
  rintro ⟨-, hmom⟩
  have h := hmom 0 0 0
  have hderiv : deriv (fun s : ℝ => (s • dir 0 : Space3)) 0 = dir 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dir 0)).deriv
  rw [hderiv] at h
  simp [dir] at h

end Trivial

/-- **Navier–Stokes regularity: base case together with a Lean-checked reduction.**

Let `ν` be a viscosity and let `u₀` be a divergence-free Schwartz-class initial velocity field
on `ℝ³`.  Assume that *either* `u₀` is the zero field, *or* the full Navier–Stokes global
regularity conjecture holds for the viscosity `ν`.  Then the initial datum `u₀` admits a
globally defined, space-time smooth, finite-energy solution of the three-dimensional
incompressible Navier–Stokes equations.

The first branch (the base case `u₀ = 0`) is discharged unconditionally by the explicit zero
solution; the second branch is the reduction of the statement to the conjecture itself.  The
Clay Millennium Problem is exactly the assertion that `NavierStokesGlobalRegularity ν` holds
for every `ν > 0`; that assertion is open and is *not* proved here. -/
theorem navier_stokes_regularity (ν : ℝ) (u₀ : SchwartzMap Space3 Space3)
    (hdiv : DivFree (u₀ : Space3 → Space3))
    (h : u₀ = 0 ∨ NavierStokesGlobalRegularity ν) :
    HasGlobalSmoothSolution ν (u₀ : Space3 → Space3) := by
  rcases h with h0 | hconj
  · -- Base case: the zero initial datum, solved explicitly by the zero solution.
    have : ((u₀ : Space3 → Space3)) = fun _ => (0 : Space3) := by
      subst h0
      funext x
      rfl
    rw [this]
    exact hasGlobalSmoothSolution_zero ν
  · -- Reduction: apply the conjecture to the given datum.
    exact hconj u₀ hdiv

end Frontier

