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

open TensorProduct

variable {G : Type*} [Group G] {U V W : Type*}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The space of intertwiners (equivariant linear maps) `U ⊗ V → W` for representations
`ρU`, `ρV`, `ρW` of a group `G`.

In the physical setting `U` carries the components `T^k_q` of a tensor operator of rank `k`,
`V` is the space of states `|j m⟩`, and `W` the space of states `|j' m'⟩`; an element of this
submodule is exactly an equivariant way of turning a component and a state into a state. -/
def tensorIntertwiners (ρU : Representation ℂ G U) (ρV : Representation ℂ G V)
    (ρW : Representation ℂ G W) : Submodule ℂ (U ⊗[ℂ] V →ₗ[ℂ] W) where
  carrier := {f | ∀ (g : G) (u : U) (v : V), f (ρU g u ⊗ₜ[ℂ] ρV g v) = ρW g (f (u ⊗ₜ[ℂ] v))}
  add_mem' := by
    intro a b ha hb g u v
    simp [ha g u v, hb g u v]
  zero_mem' := by
    intro g u v
    simp
  smul_mem' := by
    intro c a ha g u v
    simp [ha g u v]

@[simp]
theorem mem_tensorIntertwiners {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W} {f : U ⊗[ℂ] V →ₗ[ℂ] W} :
    f ∈ tensorIntertwiners ρU ρV ρW ↔
      ∀ (g : G) (u : U) (v : V), f (ρU g u ⊗ₜ[ℂ] ρV g v) = ρW g (f (u ⊗ₜ[ℂ] v)) :=
  Iff.rfl

/-- A nonzero map is nonzero on some pure tensor. -/
theorem exists_pure_tensor_ne_zero {f : U ⊗[ℂ] V →ₗ[ℂ] W} (hf : f ≠ 0) :
    ∃ (u : U) (v : V), f (u ⊗ₜ[ℂ] v) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hf (TensorProduct.ext' (fun u v => by simp [h u v]))

/-- Scalars are determined by their action on a nonzero map, tested on pure tensors. -/
theorem smul_pure_tensor_injective {f : U ⊗[ℂ] V →ₗ[ℂ] W} (hf : f ≠ 0) {r s : ℂ}
    (h : ∀ (u : U) (v : V), r • f (u ⊗ₜ[ℂ] v) = s • f (u ⊗ₜ[ℂ] v)) : r = s := by
  obtain ⟨u, v, huv⟩ := exists_pure_tensor_ne_zero hf
  have hsub : (r - s) • f (u ⊗ₜ[ℂ] v) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h u v
  rcases smul_eq_zero.mp hsub with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' huv

/-- **Wigner–Eckart theorem** (algebraic core).

Let `ρU`, `ρV`, `ρW` be representations of a group `G` on complex vector spaces, and assume the
*multiplicity-one* condition: the space of intertwiners `U ⊗ V → W` has rank at most one (for
`SU(2)` this is the statement that an irreducible `W = V_{j'}` occurs at most once in
`V_k ⊗ V_j`).

Then, given a fixed nonzero intertwiner `CG` (the Clebsch–Gordan map), every intertwiner `T`
(a tensor operator) is a *unique* scalar multiple of it: there is a unique **reduced matrix
element** `r` with
`T (u ⊗ v) = r • CG (u ⊗ v)`
for all `u`, `v`. Taking components, all the dependence of the matrix elements of `T` on the
magnetic quantum numbers is carried by the Clebsch–Gordan coefficients. -/
theorem wigner_eckart {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W}
    (hmult : Module.rank ℂ (tensorIntertwiners ρU ρV ρW) ≤ 1)
    (T CG : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hT : T ∈ tensorIntertwiners ρU ρV ρW) (hCG : CG ∈ tensorIntertwiners ρU ρV ρW)
    (hCG0 : CG ≠ 0) :
    ∃! r : ℂ, ∀ (u : U) (v : V), T (u ⊗ₜ[ℂ] v) = r • CG (u ⊗ₜ[ℂ] v) := by
  obtain ⟨f₀, hf₀⟩ := rank_le_one_iff.mp hmult
  obtain ⟨a, ha⟩ := hf₀ ⟨CG, hCG⟩
  obtain ⟨b, hb⟩ := hf₀ ⟨T, hT⟩
  have haCG : a • (f₀ : U ⊗[ℂ] V →ₗ[ℂ] W) = CG := congrArg Subtype.val ha
  have hbT : b • (f₀ : U ⊗[ℂ] V →ₗ[ℂ] W) = T := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hCG0 (by simpa using haCG.symm)
  have hTCG : T = (b / a) • CG := by
    rw [← haCG, ← hbT, smul_smul, div_mul_cancel₀ _ ha0]
  refine ⟨b / a, fun u v => by rw [hTCG]; simp, fun y hy => ?_⟩
  refine smul_pure_tensor_injective hCG0 (fun u v => ?_)
  rw [← hy u v, hTCG]
  simp

/-- The Wigner–Eckart theorem in the form used in physics: with respect to any families of
"tensor operator components" `e q`, "initial states" `f m` and "final-state functionals" `bra m'`,
the matrix elements of an equivariant tensor operator `T` factor as a single reduced matrix
element `r` times the Clebsch–Gordan coefficients `bra m' (CG (e q ⊗ f m))`. -/
theorem wigner_eckart_matrix_elements {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W}
    (hmult : Module.rank ℂ (tensorIntertwiners ρU ρV ρW) ≤ 1)
    (T CG : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hT : T ∈ tensorIntertwiners ρU ρV ρW) (hCG : CG ∈ tensorIntertwiners ρU ρV ρW)
    (hCG0 : CG ≠ 0)
    {Q M M' : Type*} (e : Q → U) (f : M → V) (bra : M' → (W →ₗ[ℂ] ℂ)) :
    ∃ r : ℂ, ∀ (m' : M') (q : Q) (m : M),
      bra m' (T (e q ⊗ₜ[ℂ] f m)) = r * bra m' (CG (e q ⊗ₜ[ℂ] f m)) := by
  obtain ⟨r, hr, -⟩ := wigner_eckart hmult T CG hT hCG hCG0
  refine ⟨r, fun m' q m => ?_⟩
  rw [hr (e q) (f m)]
  simp

/-- The multiplicity-one hypothesis of `Phys.wigner_eckart` is satisfiable, together with the
existence of a nonzero Clebsch-Gordan intertwiner: for the trivial representations on `ℂ` the
intertwiner space has rank at most one and contains the (nonzero) multiplication map. -/
theorem tensorIntertwiners_trivial_rank_le_one (G : Type*) [Group G] :
    Module.rank ℂ
        (tensorIntertwiners (1 : Representation ℂ G ℂ) (1 : Representation ℂ G ℂ)
          (1 : Representation ℂ G ℂ)) ≤ 1 ∧
      ∃ CG ∈ tensorIntertwiners (1 : Representation ℂ G ℂ) (1 : Representation ℂ G ℂ)
          (1 : Representation ℂ G ℂ), CG ≠ (0 : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) := by
  constructor
  · refine le_trans (Submodule.rank_le _) ?_
    simp [Module.rank_linearMap]
  · refine ⟨LinearMap.mul' ℂ ℂ, ?_, ?_⟩
    · intro g u v
      simp
    · intro h
      have h2 : (LinearMap.mul' ℂ ℂ : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by
        rw [h]; simp
      simp at h2

end Phys

