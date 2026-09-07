/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

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

namespace Phys

section

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A complex representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/
def IsIrrep (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ p : Submodule ℂ V, (∀ g : G, ∀ v ∈ p, ρ g v ∈ p) → p = ⊥ ∨ p = ⊤

/-- A linear map intertwines two representations (it is *equivariant*). -/
def Intertwines (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (T : V →ₗ[ℂ] W) : Prop :=
  ∀ (g : G) (v : V), T (ρ g v) = σ g (T v)

/-- A nonzero intertwiner between irreducible representations is bijective (Schur). -/
theorem bijective_of_intertwines_of_ne_zero {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {S : V →ₗ[ℂ] W} (hS : Intertwines ρ σ S) (hS0 : S ≠ 0) :
    Function.Bijective S := by
  have hker : LinearMap.ker S = ⊥ := by
    rcases hρ.2 (LinearMap.ker S) (by
      intro g v hv
      simp only [LinearMap.mem_ker] at hv ⊢
      rw [hS g v, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hS0
  have hran : LinearMap.range S = ⊤ := by
    rcases hσ.2 (LinearMap.range S) (by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hS g v⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hS0
    · exact h
  exact ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩

/-- **Schur's lemma, quantitative form.**  Over `ℂ`, any two intertwiners between
finite-dimensional irreducible representations are proportional: if `S ≠ 0`, then
`T = c • S` for a unique scalar `c` (the *reduced matrix element*). -/
theorem exists_smul_of_intertwines [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {T S : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T) (hS : Intertwines ρ σ S) (hS0 : S ≠ 0) :
    ∃ c : ℂ, T = c • S := by
  haveI : Nontrivial V := hρ.1
  -- `S` is an isomorphism of representations.
  obtain ⟨hinj, hsurj⟩ := bijective_of_intertwines_of_ne_zero hρ hσ hS hS0
  let e : V ≃ₗ[ℂ] W := LinearEquiv.ofBijective S ⟨hinj, hsurj⟩
  have he : ∀ v : V, e v = S v := fun _ => rfl
  have hsymm : ∀ (g : G) (w : W), e.symm (σ g w) = ρ g (e.symm w) := by
    intro g w
    apply e.injective
    have h1 : e (ρ g (e.symm w)) = S (ρ g (e.symm w)) := rfl
    rw [e.apply_symm_apply, h1, hS g (e.symm w)]
    congr 1
    exact (e.apply_symm_apply w).symm
  -- The endomorphism `E = S⁻¹ ∘ T` of `V` is equivariant.
  let E : Module.End ℂ V := (e.symm : W →ₗ[ℂ] V) ∘ₗ T
  have hE : ∀ (g : G) (v : V), E (ρ g v) = ρ g (E v) := by
    intro g v
    show e.symm (T (ρ g v)) = ρ g (e.symm (T v))
    rw [hT g v, hsymm g (T v)]
  -- `E` has an eigenvalue since `ℂ` is algebraically closed.
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue E
  refine ⟨c, ?_⟩
  have hspace : Module.End.eigenspace E c = ⊤ := by
    rcases hρ.2 (Module.End.eigenspace E c) (by
      intro g v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hE g v, hv, map_smul]) with h | h
    · exact absurd h hc
    · exact h
  ext v
  have hv : E v = c • v := by
    rw [← Module.End.mem_eigenspace_iff, hspace]
    trivial
  have : T v = e (E v) := by
    show T v = e (e.symm (T v))
    rw [e.apply_symm_apply]
  rw [this, hv, map_smul, he]
  rfl

/-- **Wigner–Eckart theorem (abstract form).**

Let `ρ` (acting on `V`) and `σ` (acting on `W`) be irreducible complex representations of a
group `G`, with `V` finite-dimensional.  Let `S : V →ₗ[ℂ] W` be a fixed nonzero intertwiner
(the *Clebsch–Gordan map*) and let `T : V →ₗ[ℂ] W` be any intertwiner (a *tensor operator*).
Then every matrix element of `T` factors as a single scalar `c` — the *reduced matrix
element*, independent of the states involved — times the corresponding matrix element of the
Clebsch–Gordan map:
`⟨f, T v⟩ = c * ⟨f, S v⟩` for all states `v` and all linear functionals `f` on `W`. -/
theorem wigner_eckart [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {T S : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T) (hS : Intertwines ρ σ S) (hS0 : S ≠ 0) :
    ∃ c : ℂ, ∀ (f : W →ₗ[ℂ] ℂ) (v : V), f (T v) = c * f (S v) := by
  obtain ⟨c, hc⟩ := exists_smul_of_intertwines hρ hσ hT hS hS0
  refine ⟨c, fun f v => ?_⟩
  rw [hc]
  simp

end

section TensorOperator

variable {G : Type*} [Group G]
variable {Vj Vk W : Type*}
variable [AddCommGroup Vj] [Module ℂ Vj] [AddCommGroup Vk] [Module ℂ Vk]
variable [AddCommGroup W] [Module ℂ W]

/-- **Wigner–Eckart theorem for tensor operators, in coordinates.**

Here `Vj` carries the representation `ρ` of the "state" multiplet (basis vectors `bj m`,
labelled by magnetic quantum numbers `m`), `Vk` carries the representation `τ` of the tensor
operator's multiplet (basis `bk q`), and `W` carries the final irreducible representation `σ`
(basis `bW m'`).  A tensor operator is an intertwiner `T : Vj ⊗ Vk →ₗ[ℂ] W`, and the
Clebsch–Gordan map is a fixed nonzero intertwiner `S`.

The conclusion is the physicists' statement: there is a single reduced matrix element `c`,
independent of `m`, `q` and `m'`, with
`⟨m'| T^k_q |j m⟩ = c * ⟨j m ; k q | m'⟩`. -/
theorem wigner_eckart_tensor_operator
    [FiniteDimensional ℂ Vj] [FiniteDimensional ℂ Vk]
    {ρ : Representation ℂ G Vj} {τ : Representation ℂ G Vk} {σ : Representation ℂ G W}
    (hρτ : IsIrrep (Representation.tprod ρ τ)) (hσ : IsIrrep σ)
    {T S : Vj ⊗[ℂ] Vk →ₗ[ℂ] W}
    (hT : Intertwines (Representation.tprod ρ τ) σ T)
    (hS : Intertwines (Representation.tprod ρ τ) σ S) (hS0 : S ≠ 0)
    {M Q M' : Type*} (bj : Module.Basis M ℂ Vj) (bk : Module.Basis Q ℂ Vk) (bW : Module.Basis M' ℂ W) :
    ∃ c : ℂ, ∀ (m : M) (q : Q) (m' : M'),
      bW.repr (T (bj m ⊗ₜ[ℂ] bk q)) m' = c * bW.repr (S (bj m ⊗ₜ[ℂ] bk q)) m' := by
  obtain ⟨c, hc⟩ := wigner_eckart hρτ hσ hT hS hS0
  exact ⟨c, fun m q m' =>
    hc ((Finsupp.lapply m').comp (bW.repr : W →ₗ[ℂ] (M' →₀ ℂ))) (bj m ⊗ₜ[ℂ] bk q)⟩

/-- Sanity check (non-vacuity): the hypotheses of `Phys.wigner_eckart` are satisfiable —
the one-dimensional trivial representation of any group is irreducible and the identity is a
nonzero intertwiner of it with itself. -/
theorem wigner_eckart_hypotheses_satisfiable {G : Type*} [Group G] :
    ∃ (ρ : Representation ℂ G ℂ) (S : ℂ →ₗ[ℂ] ℂ),
      IsIrrep ρ ∧ Intertwines ρ ρ S ∧ S ≠ 0 := by
  refine ⟨Representation.trivial ℂ G ℂ, LinearMap.id, ⟨inferInstance, ?_⟩, ?_, ?_⟩
  · intro p _
    exact Ideal.eq_bot_or_top p
  · intro g v; rfl
  · intro h
    have h1 := LinearMap.congr_fun h (1 : ℂ)
    simp at h1

end TensorOperator

end Phys

