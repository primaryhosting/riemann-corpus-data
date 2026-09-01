/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

section

variable {k : Type*} [Field k] {G : Type*} [Monoid G]
  {A B : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

/-- `f` intertwines the representations `ρ` and `σ`. -/
def Intertwines (ρ : Representation k G A) (σ : Representation k G B) (f : A →ₗ[k] B) : Prop :=
  ∀ (g : G) (a : A), f (ρ g a) = σ g (f a)

/-- A representation is irreducible when the only invariant subspaces are `⊥` and `⊤`. -/
def IsIrreducible (σ : Representation k G B) : Prop :=
  ∀ W : Submodule k B, (∀ (g : G), ∀ x ∈ W, σ g x ∈ W) → W = ⊥ ∨ W = ⊤

/-- **Schur's lemma** (algebraically closed field, finite dimensions): every self-intertwiner of
an irreducible representation is a scalar. -/
theorem schur_scalar [IsAlgClosed k] [FiniteDimensional k B] [Nontrivial B]
    (σ : Representation k G B) (hσ : IsIrreducible σ)
    (f : B →ₗ[k] B) (hf : Intertwines σ σ f) :
    ∃ c : k, f = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (K := k) (V := B) f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : G), ∀ x ∈ Module.End.eigenspace f c, σ g x ∈ Module.End.eigenspace f c := by
    intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hf g x, hx, map_smul]
  rcases hσ (Module.End.eigenspace f c) hinv with h | h
  · exact absurd h hc
  · ext b
    have hb : b ∈ Module.End.eigenspace f c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hb
    simp [hb]

end

section

variable {k : Type*} [Field k] [IsAlgClosed k] {G : Type*} [Monoid G]
  {A B : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [FiniteDimensional k B] [Nontrivial B]

/--
**Wigner–Eckart theorem.**

`ρ` is a representation on the "source" space `A` (physically: the tensor product of the space
carrying the rank-`k` tensor operator with the space of initial states), and `σ` is an
*irreducible* representation on the "target" space `B` (the space of final states).

* `CG` is the Clebsch–Gordan intertwiner `A → B`,
* `s` is an intertwining section of `CG`, exhibiting a copy of `B` inside `A`,
* `hmult` is the multiplicity-one hypothesis: `B` occurs only once inside `A`, i.e. every
  intertwiner `A → B` vanishing on that copy is zero.

Then for *any* tensor operator `T` (i.e. any intertwiner `A → B`) there is a single scalar `c`
— the *reduced matrix element* — such that all matrix elements of `T` are `c` times the
corresponding Clebsch–Gordan coefficient. In particular the dependence of the matrix elements on
the magnetic quantum numbers is entirely carried by `CG`.
-/
theorem wigner_eckart
    (ρ : Representation k G A) (σ : Representation k G B) (hσ : IsIrreducible σ)
    (CG : A →ₗ[k] B) (hCG : Intertwines ρ σ CG)
    (s : B →ₗ[k] A) (hs : Intertwines σ ρ s) (hsec : ∀ b : B, CG (s b) = b)
    (hmult : ∀ u : A →ₗ[k] B, Intertwines ρ σ u → (∀ b : B, u (s b) = 0) → u = 0)
    (T : A →ₗ[k] B) (hT : Intertwines ρ σ T) :
    ∃ c : k, T = c • CG ∧ ∀ (bra : B →ₗ[k] k) (a : A), bra (T a) = c * bra (CG a) := by
  -- The composition `T ∘ s` is a self-intertwiner of the irreducible `σ`, hence a scalar `c`
  -- by Schur's lemma.  This scalar is the reduced matrix element.
  have hTs : Intertwines σ σ (T ∘ₗ s) := by
    intro g b
    simp only [LinearMap.comp_apply]
    rw [hs g b, hT g (s b)]
  obtain ⟨c, hc⟩ := schur_scalar σ hσ (T ∘ₗ s) hTs
  have hTsb : ∀ b : B, T (s b) = c • b := by
    intro b
    have := congrArg (fun F : B →ₗ[k] B => F b) hc
    simpa using this
  -- `T - c • CG` is an intertwiner killing the distinguished copy of `B` inside `A`,
  -- hence zero by multiplicity one.
  have hzero : T - c • CG = 0 := by
    refine hmult _ ?_ ?_
    · intro g a
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, hT g a, hCG g a, map_sub, map_smul]
    · intro b
      simp [hTsb b, hsec b]
  have hmain : T = c • CG := sub_eq_zero.mp hzero
  refine ⟨c, hmain, ?_⟩
  intro bra a
  rw [hmain]
  simp [smul_eq_mul]

/--
Matrix-element form of the Wigner–Eckart theorem.  Given any family of "kets" `ket i` in `A`
(labelled e.g. by a magnetic quantum number of the initial state together with the component of
the tensor operator) and any family of "bras" `bra j` on `B`, there is a *single* reduced matrix
element `c` such that every matrix element of `T` is `c` times the corresponding
Clebsch–Gordan coefficient `bra j (CG (ket i))`.
-/
theorem wigner_eckart_matrix_elements
    (ρ : Representation k G A) (σ : Representation k G B) (hσ : IsIrreducible σ)
    (CG : A →ₗ[k] B) (hCG : Intertwines ρ σ CG)
    (s : B →ₗ[k] A) (hs : Intertwines σ ρ s) (hsec : ∀ b : B, CG (s b) = b)
    (hmult : ∀ u : A →ₗ[k] B, Intertwines ρ σ u → (∀ b : B, u (s b) = 0) → u = 0)
    (T : A →ₗ[k] B) (hT : Intertwines ρ σ T)
    {ιA ιB : Type*} (ket : ιA → A) (bra : ιB → (B →ₗ[k] k)) :
    ∃ c : k, ∀ (j : ιB) (i : ιA), bra j (T (ket i)) = c * bra j (CG (ket i)) := by
  obtain ⟨c, -, hc⟩ := wigner_eckart ρ σ hσ CG hCG s hs hsec hmult T hT
  exact ⟨c, fun j i => hc (bra j) (ket i)⟩

end

/-- Sanity check: the hypotheses of `Phys.wigner_eckart` are simultaneously satisfiable, so the
theorem is not vacuous. -/
example :
    ∃ (ρ : Representation ℂ Unit ℂ) (σ : Representation ℂ Unit ℂ) (CG s : ℂ →ₗ[ℂ] ℂ),
      IsIrreducible σ ∧ Intertwines ρ σ CG ∧ Intertwines σ ρ s ∧ (∀ b : ℂ, CG (s b) = b) ∧
      (∀ u : ℂ →ₗ[ℂ] ℂ, Intertwines ρ σ u → (∀ b : ℂ, u (s b) = 0) → u = 0) := by
  refine ⟨1, 1, LinearMap.id, LinearMap.id, ?_, ?_, ?_, ?_, ?_⟩
  · intro W _
    exact IsSimpleOrder.eq_bot_or_eq_top W
  · intro g a; rfl
  · intro g a; rfl
  · intro b; rfl
  · intro u _ hu
    ext
    simpa using hu 1

end Phys

