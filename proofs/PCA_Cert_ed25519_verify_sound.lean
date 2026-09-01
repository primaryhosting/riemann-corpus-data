/-
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

variable {G : Type*} [AddCommGroup G]

/-- The Ed25519 verification equation, in additive group notation.

`B` is the base point, `A` the public key, `R` the signature nonce point, `h` the challenge
scalar (in the real scheme, `h = SHA-512(R ‖ A ‖ M)` reduced mod the group order) and `s` the
signature scalar.  A signature `(R, s)` on the challenge `h` is accepted exactly when
`s • B = R + h • A`. -/
def Verify (B A R : G) (h s : ℤ) : Prop := s • B = R + h • A

/-- **Soundness and completeness of Ed25519 verification.**

Let `B` be a point of order `ell`, let the public key be `A = a • B` and the nonce point be
`R = r • B`.  Then the verification equation holds *if and only if* the signature scalar `s`
is the honest Schnorr response `r + h * a` modulo the group order `ell`.

The forward direction is soundness: an accepted signature certifies that the scalar `s` is
determined by the discrete logarithms `a` of the public key and `r` of the nonce point, so no
other scalar can be substituted.  The backward direction is completeness: the honestly computed
response is always accepted. -/
theorem ed25519_verify_sound {G : Type*} [AddCommGroup G] (B A R : G) (ell : ℕ)
    (hell : addOrderOf B = ell) (a r h s : ℤ) (hA : A = a • B) (hR : R = r • B) :
    Verify B A R h s ↔ (s : ZMod ell) = (r : ZMod ell) + (h : ZMod ell) * (a : ZMod ell) := by
  subst hA hR hell
  have key : Verify B (a • B) (r • B) h s ↔ ((addOrderOf B : ℕ) : ℤ) ∣ (s - (r + h * a)) := by
    rw [addOrderOf_dvd_iff_zsmul_eq_zero, sub_smul, sub_eq_zero, add_smul, mul_smul, Verify]
  rw [key, show ((r : ZMod (addOrderOf B)) + (h : ZMod _) * (a : ZMod _))
      = ((r + h * a : ℤ) : ZMod (addOrderOf B)) by push_cast; ring,
    ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd, dvd_sub_comm]

/-- Completeness: the honestly generated response `s ≡ r + h * a` is always accepted. -/
theorem verify_of_honest (B A R : G) (ell : ℕ) (hell : addOrderOf B = ell)
    (a r h s : ℤ) (hA : A = a • B) (hR : R = r • B)
    (hs : (s : ZMod ell) = (r : ZMod ell) + (h : ZMod ell) * (a : ZMod ell)) :
    Verify B A R h s :=
  (ed25519_verify_sound B A R ell hell a r h s hA hR).2 hs

/-- Soundness, in contrapositive form: a signature scalar that differs from the honest Schnorr
response modulo the group order is rejected. -/
theorem not_verify_of_ne (B A R : G) (ell : ℕ) (hell : addOrderOf B = ell)
    (a r h s : ℤ) (hA : A = a • B) (hR : R = r • B)
    (hs : (s : ZMod ell) ≠ (r : ZMod ell) + (h : ZMod ell) * (a : ZMod ell)) :
    ¬ Verify B A R h s :=
  fun hv => hs ((ed25519_verify_sound B A R ell hell a r h s hA hR).1 hv)

/-- Key extraction from two accepted signatures that share a nonce point but have distinct
challenges: in a group of prime order the secret key `a` is determined modulo `ell`.  This is the
standard argument showing that nonce reuse leaks the Ed25519 signing key. -/
theorem secret_key_of_nonce_reuse (B A R : G) (ell : ℕ) [Fact (Nat.Prime ell)]
    (hell : addOrderOf B = ell) (a r h₁ h₂ s₁ s₂ : ℤ) (hA : A = a • B) (hR : R = r • B)
    (hne : (h₁ : ZMod ell) ≠ (h₂ : ZMod ell))
    (hv₁ : Verify B A R h₁ s₁) (hv₂ : Verify B A R h₂ s₂) :
    (a : ZMod ell) = ((s₁ : ZMod ell) - (s₂ : ZMod ell)) / ((h₁ : ZMod ell) - (h₂ : ZMod ell)) := by
  have e₁ := (ed25519_verify_sound B A R ell hell a r h₁ s₁ hA hR).1 hv₁
  have e₂ := (ed25519_verify_sound B A R ell hell a r h₂ s₂ hA hR).1 hv₂
  have hsub : (h₁ : ZMod ell) - (h₂ : ZMod ell) ≠ 0 := sub_ne_zero_of_ne hne
  field_simp
  rw [e₁, e₂]
  ring

end PCA.Cert

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

