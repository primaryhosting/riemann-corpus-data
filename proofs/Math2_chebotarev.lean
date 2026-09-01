import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

namespace Math2

/-- If `ζ` is a primitive `n`-th root of unity and `a ≡ b [MOD n]`, then `ζ ^ a = ζ ^ b`. -/
theorem pow_eq_pow_of_modEq {M : Type*} [CommMonoid M] {n : ℕ} {ζ : M}
    (hζ : IsPrimitiveRoot ζ n) {a b : ℕ} (h : a ≡ b [MOD n]) : ζ ^ a = ζ ^ b := by
  have key : ∀ c : ℕ, ζ ^ c = ζ ^ (c % n) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c n]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [key a, key b, h]

/-- Coprimality only depends on the residue class. -/
theorem coprime_of_modEq {p a n : ℕ} (h : p ≡ a [MOD n]) (ha : a.Coprime n) : p.Coprime n := by
  unfold Nat.Coprime at ha ⊢
  rw [Nat.gcd_comm, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  exact ha

/-- Every automorphism of a field containing a primitive `n`-th root of unity `ζ` sends `ζ`
to a power `ζ ^ a` with `a` coprime to `n`: this is the cyclotomic character. -/
theorem exists_coprime_pow_eq_aut {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ} (hn : n ≠ 0)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (σ : L ≃ₐ[ℚ] L) :
    ∃ a : ℕ, a.Coprime n ∧ σ ζ = ζ ^ a := by
  haveI : NeZero n := ⟨hn⟩
  have hmap : IsPrimitiveRoot (σ ζ) n :=
    hζ.map_of_injective (f := (σ : L →+* L)) σ.injective
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) hmap.pow_eq_one
  refine ⟨a, ?_, ha.symm⟩
  exact (hζ.pow_iff_coprime (Nat.pos_of_ne_zero hn) a).mp (ha ▸ hmap)

/-- **Chebotarev density theorem for Frobenius conjugacy classes**, in the cyclotomic
(abelian) case, in its qualitative "infinitely many primes" form.

Let `L` be a field of characteristic zero containing a primitive `n`-th root of unity `ζ`
(for instance the cyclotomic field `ℚ(ζₙ)`), and let `σ` be any element of the Galois group
`Gal(L/ℚ)`.  A prime `p` not dividing `n` is unramified in `ℚ(ζₙ)`, and the Frobenius element
at `p` is characterised by its action `ζ ↦ ζ ^ p` on the `n`-th roots of unity.  The theorem
states that the set of primes whose Frobenius element is `σ` — i.e. of primes `p ∤ n` with
`σ ζ = ζ ^ p` — is infinite.  Since the Galois group here is abelian, the conjugacy class of
`σ` is `{σ}`, so this is exactly the statement that every Frobenius conjugacy class is hit by
infinitely many primes. -/
theorem chebotarev {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ} (hn : n ≠ 0)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (σ : L ≃ₐ[ℚ] L) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ n ∧ σ ζ = ζ ^ p}.Infinite := by
  obtain ⟨a, hacop, hσ⟩ := exists_coprime_pow_eq_aut hn hζ σ
  refine (Nat.infinite_setOf_prime_and_modEq hn hacop).mono ?_
  rintro p ⟨hp, hpa⟩
  have hcop : p.Coprime n := coprime_of_modEq hpa hacop
  refine ⟨hp, ?_, ?_⟩
  · intro hdvd
    have : p ∣ 1 := hcop ▸ Nat.dvd_gcd dvd_rfl hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · rw [hσ]
    exact pow_eq_pow_of_modEq hζ hpa.symm

/-- The theorem applied to the cyclotomic field `ℚ(ζₙ)` itself: for every element `σ` of
`Gal(ℚ(ζₙ)/ℚ)` there are infinitely many primes `p ∤ n` whose Frobenius element is `σ`,
i.e. with `σ ζ = ζ ^ p` for `ζ` a fixed primitive `n`-th root of unity. -/
theorem chebotarev_cyclotomicField (n : ℕ) [NeZero n]
    (σ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ n ∧
      σ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) =
        IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ p}.Infinite :=
  chebotarev (NeZero.ne n) (IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)) σ

end Math2

