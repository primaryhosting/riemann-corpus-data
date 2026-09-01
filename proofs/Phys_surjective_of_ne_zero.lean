/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace Phys

open Representation

variable {k G M N : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The range of an intertwining map, as a subrepresentation of the target. -/
def rangeSubrep {ρ : Representation k G M} {σ : Representation k G N}
    (C : M →ₗ[k] N) (hC : ∀ g x, C (ρ g x) = σ g (C x)) : Subrepresentation σ where
  toSubmodule := LinearMap.range C
  apply_mem_toSubmodule g := by
    rintro v ⟨x, rfl⟩
    exact ⟨ρ g x, hC g x⟩

omit [IsAlgClosed k] in
/-- An intertwining map into an irreducible representation is surjective, unless it is zero. -/
theorem surjective_of_ne_zero {ρ : Representation k G M} {σ : Representation k G N}
    [σ.IsIrreducible] (C : M →ₗ[k] N) (hC : ∀ g x, C (ρ g x) = σ g (C x)) (hC0 : C ≠ 0) :
    Function.Surjective C := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (rangeSubrep C hC) with h | h
  · exact absurd (by
      ext x
      have : C x ∈ (rangeSubrep C hC : Subrepresentation σ) := ⟨x, rfl⟩
      rw [h] at this
      simpa using this) hC0
  · intro n
    have : n ∈ (rangeSubrep C hC : Subrepresentation σ) := by rw [h]; trivial
    exact this

/-- **Schur-type rigidity**: if `C` and `T` are intertwining maps from `ρ` to an irreducible,
finite-dimensional representation `σ` over an algebraically closed field, `C ≠ 0`, and every
vector killed by `C` is killed by `T` (the multiplicity-one condition), then `T` is a unique
scalar multiple of `C`. -/
theorem exists_unique_reduced_scalar {ρ : Representation k G M} {σ : Representation k G N}
    [FiniteDimensional k N] [σ.IsIrreducible]
    (C T : M →ₗ[k] N)
    (hC : ∀ g x, C (ρ g x) = σ g (C x)) (hT : ∀ g x, T (ρ g x) = σ g (T x))
    (hC0 : C ≠ 0) (hker : ∀ x, C x = 0 → T x = 0) :
    ∃! r : k, ∀ x, T x = r • C x := by
  have hsurj : Function.Surjective C := surjective_of_ne_zero C hC hC0
  -- factor `T` through `C`
  set e := LinearMap.quotKerEquivOfSurjective C hsurj
  have hker' : LinearMap.ker C ≤ LinearMap.ker T := fun x hx =>
    hker x (by simpa using hx)
  set phi : N →ₗ[k] N := ((LinearMap.ker C).liftQ T hker').comp e.symm.toLinearMap with hphi
  have hphiC : ∀ x, phi (C x) = T x := by
    intro x
    have hx : e (Submodule.Quotient.mk x) = C x := rfl
    have : e.symm (C x) = Submodule.Quotient.mk x := by
      rw [← hx, LinearEquiv.symm_apply_apply]
    simp only [hphi, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  -- `phi` is an intertwining map
  have hphieq : ∀ g n, phi (σ g n) = σ g (phi n) := by
    intro g n
    obtain ⟨x, rfl⟩ := hsurj n
    rw [← hC g x, hphiC, hphiC, hT]
  let Phi : IntertwiningMap σ σ := ⟨phi, fun g n => hphieq g n⟩
  obtain ⟨r, hr⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := σ)).2 Phi
  have hrphi : ∀ n, phi n = r • n := by
    intro n
    have : (algebraMap k (IntertwiningMap σ σ) r) n = Phi n := by rw [hr]
    simpa using this.symm
  refine ⟨r, fun x => by rw [← hphiC, hrphi], ?_⟩
  intro s hs
  obtain ⟨x, hx⟩ : ∃ x, C x ≠ 0 := by
    by_contra h
    exact hC0 (by ext x; simpa using not_not.mp (not_exists.mp h x))
  have := hs x
  rw [← hphiC x, hrphi] at this
  have hsub : (r - s) • C x = 0 := by
    rw [sub_smul, sub_eq_zero]; exact this
  rcases smul_eq_zero.mp hsub with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hx

/-- **The Wigner–Eckart theorem.**

Let `U`, `V`, `W` be representations of a symmetry group `G` over an algebraically closed field
(think `G = SU(2)`, `U` the spin-`k` space of a tensor operator, `V` the spin-`j` initial space
and `W` the spin-`j'` final space), with `W` irreducible and finite-dimensional.

Let `CG : U ⊗ V →ₗ W` be the Clebsch–Gordan intertwiner and `T : U ⊗ V →ₗ W` the intertwiner
attached to an irreducible tensor operator, and assume the multiplicity-one condition that
`CG` and `T` cannot separate vectors that `CG` kills.

Then there is a *unique* scalar `r` — the reduced matrix element `⟨j' ‖ T ‖ j⟩`, independent of
the magnetic quantum numbers — such that every matrix element `⟨j' m' | T^k_q | j m⟩` factors as
the Clebsch–Gordan coefficient times `r`. -/
theorem wigner_eckart {k G U V W : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρU : Representation k G U) (ρV : Representation k G V) (ρW : Representation k G W)
    [FiniteDimensional k W] [ρW.IsIrreducible]
    (CG T : U ⊗[k] V →ₗ[k] W)
    (hCG : ∀ g x, CG ((ρU.tprod ρV) g x) = ρW g (CG x))
    (hT : ∀ g x, T ((ρU.tprod ρV) g x) = ρW g (T x))
    (hCG0 : CG ≠ 0)
    (hmult : ∀ x, CG x = 0 → T x = 0) :
    ∃! r : k, ∀ (bra : W →ₗ[k] k) (u : U) (v : V),
      bra (T (u ⊗ₜ[k] v)) = r * bra (CG (u ⊗ₜ[k] v)) := by
  obtain ⟨r, hr, huniq⟩ := exists_unique_reduced_scalar (ρ := ρU.tprod ρV) (σ := ρW)
    CG T hCG hT hCG0 hmult
  refine ⟨r, fun bra u v => by rw [hr, map_smul, smul_eq_mul], ?_⟩
  intro s hs
  refine huniq s ?_
  intro x
  -- test against all functionals
  have key : ∀ bra : W →ₗ[k] k, bra (T x) = s * bra (CG x) := by
    intro bra
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => exact hs bra u v
    | add a b ha hb => simp only [map_add, ha, hb]; ring
  have : ∀ bra : W →ₗ[k] k, bra (T x - s • CG x) = 0 := by
    intro bra
    simp only [map_sub, map_smul, smul_eq_mul, key bra, sub_self]
  have := (Module.forall_dual_apply_eq_zero_iff k (T x - s • CG x)).mp this
  rw [sub_eq_zero] at this
  exact this

/-! ### Non-vacuity

We check that the hypotheses of `Phys.wigner_eckart` are satisfiable, by instantiating them with
the (one-dimensional, hence irreducible) trivial representation of an arbitrary group on `ℂ`. -/

section NonVacuous

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Subrepresentations of a trivial representation are exactly its submodules. -/
def trivialSubrepOrderIso :
    Subrepresentation (Representation.trivial k G V) ≃o Submodule k V where
  toFun := Subrepresentation.toSubmodule
  invFun p := ⟨p, by intro g v hv; simpa using hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance : (Representation.trivial k G k).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff trivialSubrepOrderIso).mpr inferInstance

/-- The hypotheses of the Wigner–Eckart theorem are satisfiable: here `U = V = W = ℂ` carry the
trivial representation of `G` and the Clebsch–Gordan map is the canonical isomorphism
`ℂ ⊗ ℂ ≃ ℂ`. -/
theorem wigner_eckart_nonvacuous (G : Type*) [Group G] :
    ∃! r : ℂ, ∀ (bra : ℂ →ₗ[ℂ] ℂ) (u v : ℂ),
      bra ((TensorProduct.lid ℂ ℂ) (u ⊗ₜ[ℂ] v)) =
        r * bra ((TensorProduct.lid ℂ ℂ) (u ⊗ₜ[ℂ] v)) := by
  have hequiv : ∀ (g : G) (x : ℂ ⊗[ℂ] ℂ),
      (TensorProduct.lid ℂ ℂ).toLinearMap
          (((Representation.trivial ℂ G ℂ).tprod (Representation.trivial ℂ G ℂ)) g x) =
        (Representation.trivial ℂ G ℂ) g ((TensorProduct.lid ℂ ℂ).toLinearMap x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simp [Representation.tprod_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hne : (TensorProduct.lid ℂ ℂ).toLinearMap ≠ 0 := by
    intro h
    have : (TensorProduct.lid ℂ ℂ).toLinearMap ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by rw [h]; rfl
    simp at this
  exact wigner_eckart (Representation.trivial ℂ G ℂ) (Representation.trivial ℂ G ℂ)
    (Representation.trivial ℂ G ℂ) _ _ hequiv hequiv hne (fun _ h => h)

end NonVacuous

end Phys

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

