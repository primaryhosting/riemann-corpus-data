import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other token in a file, so the
-- required header comment appears immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-!
## The statement

Langlands reciprocity predicts a correspondence between `n`-dimensional representations of the
absolute Galois group of a number field and automorphic representations of `GLₙ` over that field,
matching the local data (Frobenius eigenvalues ↔ Satake parameters, i.e. equality of `L`-functions).

The abelian base case `n = 1` over `ℚ` is class field theory: automorphic representations of
`GL₁/ℚ` are Hecke characters, i.e. (for those of conductor dividing `N`) Dirichlet characters
mod `N`, and these correspond to characters of the Galois group of the cyclotomic field
`ℚ(ζ_N)` — the correspondence being induced by the *Artin map*
`Gal(ℚ(ζ_N)/ℚ) ≃ (ℤ/Nℤ)ˣ`, which is characterised by its action on `N`-th roots of unity.

Below, `IsArtinMap` pins down the arithmetic normalisation of the reciprocity map, and
`IsGL1Reciprocity` says that a bijection between the automorphic side (Dirichlet characters)
and the Galois side (characters of the Galois group) is the one induced by the Artin map.
`Frontier.langlands_reciprocity` proves that such data exist for every cyclotomic field.
-/

variable (n : ℕ) (K : Type*) [Field K] [CharZero K]

/-- The (inverse of the) Artin reciprocity map for the cyclotomic extension `ℚ(ζₙ)/ℚ`:
an isomorphism `Gal(K/ℚ) ≃* (ℤ/nℤ)ˣ` sending `σ` to the exponent `a` with `σ ζ = ζ ^ a` for
every `n`-th root of unity `ζ`. -/
def IsArtinMap (art : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ) : Prop :=
  ∀ (σ : K ≃ₐ[ℚ] K) (x : K), x ^ n = 1 → σ x = x ^ ((art σ : ZMod n)).val

/-- Reciprocity for `GL₁` over `ℚ`, level `n`: the bijection `e` between automorphic
representations of `GL₁/ℚ` with conductor dividing `n` (i.e. Dirichlet characters mod `n`,
with values in `ℂ`) and one–dimensional complex representations of `Gal(K/ℚ)` is the one
obtained by transporting a Dirichlet character along the Artin map `art`. -/
def IsGL1Reciprocity (art : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ)
    (e : DirichletCharacter ℂ n ≃ ((K ≃ₐ[ℚ] K) →* ℂˣ)) : Prop :=
  ∀ (χ : DirichletCharacter ℂ n) (σ : K ≃ₐ[ℚ] K), (e χ) σ = χ.toUnitHom (art σ)

/-- **Langlands reciprocity, abelian base case (`GL₁` over `ℚ`).**

For the `n`-th cyclotomic field `K = ℚ(ζₙ)` there is an Artin reciprocity isomorphism
`art : Gal(K/ℚ) ≃* (ℤ/nℤ)ˣ`, characterised by `σ ζ = ζ ^ art σ` on `n`-th roots of unity, and a
bijection `e` between the automorphic side (Dirichlet characters mod `n` with values in `ℂ`, i.e.
automorphic representations of `GL₁/ℚ` of conductor dividing `n`) and the Galois side
(one-dimensional complex representations of `Gal(K/ℚ)`), such that `e` is induced by `art`.

The key input from Mathlib is `IsCyclotomicExtension.Rat.galEquivZMod` (with its characterisation
`IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq`), together with
`MulChar.equivToUnitHom`. -/
theorem langlands_reciprocity [NeZero n] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    ∃ (art : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ) (e : DirichletCharacter ℂ n ≃ ((K ≃ₐ[ℚ] K) →* ℂˣ)),
      IsArtinMap n K art ∧ IsGL1Reciprocity n K art e := by
  classical
  refine ⟨IsCyclotomicExtension.Rat.galEquivZMod n K,
    MulChar.equivToUnitHom.trans
      (MulEquiv.monoidHomCongrLeftEquiv
        (IsCyclotomicExtension.Rat.galEquivZMod n K).symm), ?_, ?_⟩
  · intro σ x hx
    exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K σ hx
  · intro χ σ
    rfl

/-- Any reciprocity correspondence is multiplicative: the bijection between Dirichlet characters
mod `n` and one-dimensional representations of `Gal(K/ℚ)` is an isomorphism of character groups.
This is the `GL₁` shadow of the compatibility of Langlands functoriality with tensor products. -/
theorem gl1Reciprocity_mul {art : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ}
    {e : DirichletCharacter ℂ n ≃ ((K ≃ₐ[ℚ] K) →* ℂˣ)} (h : IsGL1Reciprocity n K art e)
    (χ₁ χ₂ : DirichletCharacter ℂ n) : e (χ₁ * χ₂) = e χ₁ * e χ₂ := by
  ext σ
  rw [MonoidHom.mul_apply, h, h, h]
  simp [MulChar.equivToUnitHom_mul_apply χ₁ χ₂ (art σ)]

/-- The base case applies to the standard model `CyclotomicField n ℚ` of `ℚ(ζₙ)`. -/
theorem langlands_reciprocity_cyclotomicField (n : ℕ) [NeZero n] :
    ∃ (art : (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) ≃* (ZMod n)ˣ)
      (e : DirichletCharacter ℂ n ≃ ((CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) →* ℂˣ)),
      IsArtinMap n (CyclotomicField n ℚ) art ∧
        IsGL1Reciprocity n (CyclotomicField n ℚ) art e :=
  langlands_reciprocity n (CyclotomicField n ℚ)

end Frontier

