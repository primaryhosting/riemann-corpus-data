import Mathlib

/-!
# The algebraic core of the AKS primality criterion

This file contains the field-theoretic heart of the completeness direction of the
Agrawal–Kayal–Saxena primality test.
-/

open Polynomial Finset

namespace CS.AKS

section Core

variable {K : Type*} [Field K]

/-- `IntroP ζ ℓ m` says that the number `m` is *introspective* (at the `r`-th root of unity `ζ`)
for all the linear polynomials `X + a` with `a ≤ ℓ`. -/
def IntroP (ζ : K) (ℓ m : ℕ) : Prop :=
  ∀ k a : ℕ, a ≤ ℓ → (ζ ^ k + (a : K)) ^ m = ζ ^ (k * m) + (a : K)

lemma IntroP.one (ζ : K) (ℓ : ℕ) : IntroP ζ ℓ 1 := by
  intro k a _
  simp

lemma IntroP.mul {ζ : K} {ℓ m₁ m₂ : ℕ} (h₁ : IntroP ζ ℓ m₁) (h₂ : IntroP ζ ℓ m₂) :
    IntroP ζ ℓ (m₁ * m₂) := by
  intro k a ha
  have : (ζ ^ k + (a : K)) ^ (m₁ * m₂) = ((ζ ^ k + (a : K)) ^ m₁) ^ m₂ := by
    rw [pow_mul]
  rw [this, h₁ k a ha, h₂ (k * m₁) a ha]
  ring_nf

lemma IntroP.pow {ζ : K} {ℓ m : ℕ} (h : IntroP ζ ℓ m) (i : ℕ) : IntroP ζ ℓ (m ^ i) := by
  induction i with
  | zero => simpa using IntroP.one ζ ℓ
  | succ i ih => rw [pow_succ]; exact ih.mul h

/-- Introspectivity extends from the linear polynomials `X + a` to their products. -/
lemma IntroP.prod {ζ : K} {ℓ m : ℕ} (h : IntroP ζ ℓ m) (S : Finset ℕ) (hS : ∀ a ∈ S, a ≤ ℓ)
    (k : ℕ) :
    (∏ a ∈ S, (ζ ^ k + (a : K))) ^ m = ∏ a ∈ S, (ζ ^ (k * m) + (a : K)) := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun a ha => h k a (hS a ha)

end Core

end CS.AKS

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

