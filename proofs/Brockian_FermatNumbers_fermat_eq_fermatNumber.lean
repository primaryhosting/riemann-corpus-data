import Mathlib

/-!
# Fermat numbers: the known primes, the small composites, coprimality, and the open question

The **Fermat numbers** are `F n = 2 ^ (2 ^ n) + 1`. This module records the
**concrete, fully verified** facts about the first few of them and isolates — as
an *unproven definition* — the genuinely **open** problem about Fermat primes.

## What is a theorem (settled) vs. what is open

The **known Fermat primes** are exactly `F₀,…,F₄ = 3, 5, 17, 257, 65537`; each
primality is verified below by `norm_num`. `F₅ = 4294967297 = 641 · 6700417` is
**composite** (Euler, 1732) and `F₆ = 274177 · 67280421310721` is composite too;
both are verified below by exhibiting the explicit factorization. The classical
**Goldbach theorem on Fermat numbers** — distinct Fermat numbers are pairwise
coprime — is proved here by *reusing Mathlib's* `Nat.coprime_fermatNumber_fermatNumber`.

What is genuinely **open** is whether there is *any* Fermat prime beyond `F₄`
(it is conjectured there is none, i.e. `F₀,…,F₄` are the only Fermat primes).
This open statement is recorded below as `FermatPrimeBeyondFour`. It is a
`def` of type `Prop`; it is **never asserted** anywhere in this file, and nothing
here proves or refutes it.

## Reuse of Mathlib

Mathlib already provides `Nat.fermatNumber n = 2 ^ (2 ^ n) + 1` together with the
coprimality theorem `Nat.coprime_fermatNumber_fermatNumber` (Goldbach's theorem)
in `Mathlib.NumberTheory.Fermat`. We keep a local `fermat` for framing, prove it
is *definitionally* `Nat.fermatNumber`, and derive coprimality from Mathlib.

None of the proofs below use `sorry`, `admit`, `native_decide`, or any added axiom.

## References
* Fermat number: <https://en.wikipedia.org/wiki/Fermat_number>
* Euler's factorization of `F₅` (1732); Landry's factorization of `F₆` (1880).
* Mathlib `Mathlib/NumberTheory/Fermat.lean`.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `F n = 2 ^ (2 ^ n) + 1`. -/
def fermat (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

/-- The local `fermat` agrees, *definitionally*, with Mathlib's `Nat.fermatNumber`. -/
theorem fermat_eq_fermatNumber (n : ℕ) : fermat n = Nat.fermatNumber n := rfl

/-- **OPEN**: is there a Fermat prime beyond `F₄`? (Conjectured: no — `F₀,…,F₄`
are believed to be the only Fermat primes.) This is an *unproven definition*; it
is never asserted or refuted in this file. -/
def FermatPrimeBeyondFour : Prop := ∃ n : ℕ, 5 ≤ n ∧ (fermat n).Prime

/-! ## (1) FLAGSHIP — the five known Fermat primes `F₀,…,F₄`

Each proof reduces `fermat k` to its literal value and then verifies primality
with `norm_num`'s primality extension. -/

/-- `F₀ = 2^(2^0) + 1 = 3` is prime. -/
theorem fermat_0_prime : (fermat 0).Prime := by norm_num [fermat]

/-- `F₁ = 2^(2^1) + 1 = 5` is prime. -/
theorem fermat_1_prime : (fermat 1).Prime := by norm_num [fermat]

/-- `F₂ = 2^(2^2) + 1 = 17` is prime. -/
theorem fermat_2_prime : (fermat 2).Prime := by norm_num [fermat]

/-- `F₃ = 2^(2^3) + 1 = 257` is prime. -/
theorem fermat_3_prime : (fermat 3).Prime := by norm_num [fermat]

/-- `F₄ = 2^(2^4) + 1 = 65537` is prime. This is the largest **known** Fermat prime. -/
theorem fermat_4_prime : (fermat 4).Prime := by norm_num [fermat]

/-! ## (2) FLAGSHIP — `F₅` and `F₆` are composite (explicit factorizations)

`F₅ = 2^32 + 1 = 4294967297 = 641 · 6700417` is Euler's 1732 factorization;
`F₆ = 2^64 + 1 = 18446744073709551617 = 274177 · 67280421310721` is Landry's. -/

/-- Euler's factorization `F₅ = 641 · 6700417`. -/
theorem fermat_5_eq : fermat 5 = 641 * 6700417 := by norm_num [fermat]

/-- `F₅` is **not** prime: it factors nontrivially as `641 · 6700417`. -/
theorem fermat_5_not_prime : ¬ (fermat 5).Prime :=
  Nat.not_prime_of_mul_eq fermat_5_eq.symm (by norm_num) (by norm_num)

/-- Landry's factorization `F₆ = 274177 · 67280421310721`. -/
theorem fermat_6_eq : fermat 6 = 274177 * 67280421310721 := by norm_num [fermat]

/-- `F₆` is **not** prime: it factors nontrivially as `274177 · 67280421310721`. -/
theorem fermat_6_not_prime : ¬ (fermat 6).Prime :=
  Nat.not_prime_of_mul_eq fermat_6_eq.symm (by norm_num) (by norm_num)

/-! ## (3) FLAGSHIP STRUCTURAL — Goldbach's coprimality theorem

Distinct Fermat numbers are pairwise coprime. This is Goldbach's classical
theorem; we derive it from Mathlib's `Nat.coprime_fermatNumber_fermatNumber`
via the definitional identity `fermat = Nat.fermatNumber`. -/

/-- **Goldbach's theorem on Fermat numbers**: any two *distinct* Fermat numbers
are coprime. -/
theorem fermat_coprime {m n : ℕ} (h : m ≠ n) : Nat.Coprime (fermat m) (fermat n) :=
  Nat.coprime_fermatNumber_fermatNumber h

end Brockian.FermatNumbers
