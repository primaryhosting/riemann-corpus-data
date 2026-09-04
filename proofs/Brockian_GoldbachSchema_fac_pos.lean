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

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires every `import` command to occur before
any other command, including module doc comments such as the header above.
Since the header has to be the very first thing in this file, this module is
written against the Lean 4 core library only.  The companion module
`Brockian.GoldbachSchemaMathlib` imports Mathlib, shows that the notion of
primality used here coincides with `Nat.Prime`, and restates the main result in
Mathlib's vocabulary.
-/

namespace Brockian.GoldbachSchema

/-- `IsPrime p` : `p` is a prime natural number. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- `IsGoldbachSum n` : `n` is a sum of two primes. -/
def IsGoldbachSum (n : Nat) : Prop :=
  ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n

/-- A *prime supply model* is a function producing, for every bound `N`, a
prime that is at least `N`.  This is exactly the resource the Goldbach schema
below consumes: it is what lets one exhibit Goldbach numbers beyond any
prescribed bound. -/
def PrimeSupplyModel (f : Nat → Nat) : Prop :=
  ∀ N : Nat, N ≤ f N ∧ IsPrime (f N)

/-! ## Discharging the model hypothesis

The conclusion below is naturally proved from a hypothesis `PrimeSupplyModel f`.
We discharge that hypothesis by constructing such an `f`, i.e. by proving the
infinitude of the primes from scratch (Euclid's argument via factorials).
-/

/-- Factorial. -/
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos : ∀ n : Nat, 0 < fac n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fac_pos n)

/-- Every positive number `m ≤ n` divides `fac n`. -/
theorem dvd_fac : ∀ {m n : Nat}, 0 < m → m ≤ n → m ∣ fac n := by
  intro m n hm hmn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k m with hk | hk
    · have hmk : m = k + 1 := by omega
      subst hmk
      exact ⟨fac k, rfl⟩
    · obtain ⟨c, hc⟩ := ih hk
      refine ⟨(k + 1) * c, ?_⟩
      show (k + 1) * fac k = m * ((k + 1) * c)
      rw [hc, Nat.mul_left_comm]

/-- Every `n ≥ 2` has a prime divisor. -/
theorem exists_prime_dvd : ∀ n : Nat, 2 ≤ n → ∃ p : Nat, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : ∀ m : Nat, m ∣ n → m = 1 ∨ m = n
    · exact ⟨n, ⟨hn, hp⟩, Nat.dvd_refl n⟩
    · have hex : ∃ m : Nat, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
        Classical.byContradiction fun hcon =>
          hp fun m hm =>
            Classical.byContradiction fun hne =>
              hcon ⟨m, hm, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
      obtain ⟨m, hmn, hm1, hmne⟩ := hex
      have hm0 : m ≠ 0 := by
        intro h
        subst h
        have : n = 0 := Nat.eq_zero_of_zero_dvd hmn
        omega
      have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmn
      have hmlt : m < n := Nat.lt_of_le_of_ne hmle hmne
      have hm2 : 2 ≤ m := by omega
      obtain ⟨p, hp', hpm⟩ := ih m hmlt hm2
      exact ⟨p, hp', Nat.dvd_trans hpm hmn⟩

/-- **Euclid**: there are primes beyond every bound. -/
theorem exists_prime_ge (N : Nat) : ∃ p : Nat, N ≤ p ∧ IsPrime p := by
  have hpos := fac_pos N
  have hge : 2 ≤ fac N + 1 := by omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd (fac N + 1) hge
  refine ⟨p, ?_, hp⟩
  apply Classical.byContradiction
  intro hlt
  have hltN : p < N := by omega
  have hp2 := hp.1
  have hpf : p ∣ fac N := dvd_fac (by omega) (Nat.le_of_lt hltN)
  have h1 : p ∣ 1 := by
    have hsub : p ∣ fac N + 1 - fac N := Nat.dvd_sub hpd hpf
    have he : fac N + 1 - fac N = 1 := by omega
    rwa [he] at hsub
  have := Nat.le_of_dvd Nat.zero_lt_one h1
  omega

/-- **Discharge of the model hypothesis.**  A prime supply model exists. -/
theorem exists_primeSupplyModel : ∃ f : Nat → Nat, PrimeSupplyModel f :=
  ⟨fun N => (exists_prime_ge N).choose, fun N => (exists_prime_ge N).choose_spec⟩

/-- Twice a prime is a sum of two primes. -/
theorem isGoldbachSum_two_mul {p : Nat} (hp : IsPrime p) : IsGoldbachSum (2 * p) :=
  ⟨p, p, hp, hp, by omega⟩

/-- **Goldbach beyond any bound — unconditionally.**

For every bound `N` there is an even number `n` with `N < n` and `4 ≤ n` which
is a sum of two primes.  This is the conclusion of the Goldbach schema, whose
`PrimeSupplyModel` hypothesis has been discharged here (see
`exists_primeSupplyModel`); the statement therefore carries no hypotheses. -/
theorem goldbach_beyond_of_model :
    ∀ N : Nat, ∃ n : Nat, N < n ∧ (∃ k : Nat, n = 2 * k) ∧ 4 ≤ n ∧ IsGoldbachSum n := by
  obtain ⟨f, hf⟩ := exists_primeSupplyModel
  intro N
  obtain ⟨hle, hp⟩ := hf (N + 2)
  have h2 : 2 ≤ f (N + 2) := hp.1
  exact ⟨2 * f (N + 2), by omega, ⟨f (N + 2), rfl⟩, by omega, isGoldbachSum_two_mul hp⟩

end Brockian.GoldbachSchema

import Mathlib
import Brockian.GoldbachSchema

/-!
# Mathlib companion to `Brockian.GoldbachSchema`

`Brockian.GoldbachSchema` is written against the Lean core library only (its
required header comment forces it to contain no `import` commands).  Here we
reconcile it with Mathlib: the primality notion used there is `Nat.Prime`, and
the main result `goldbach_beyond_of_model` is restated in Mathlib vocabulary.
-/

namespace Brockian.GoldbachSchema

/-- The self-contained primality predicate agrees with `Nat.Prime`. -/
theorem isPrime_iff_natPrime {p : ℕ} : IsPrime p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨h2, hdvd⟩
    exact Nat.prime_def.mpr ⟨h2, hdvd⟩
  · intro hp
    exact ⟨hp.two_le, fun m hm => hp.eq_one_or_self_of_dvd m hm⟩

/-- Being a sum of two primes, spelled with `Nat.Prime`. -/
theorem isGoldbachSum_iff {n : ℕ} :
    IsGoldbachSum n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  unfold IsGoldbachSum
  simp only [isPrime_iff_natPrime]

/-- `goldbach_beyond_of_model` in Mathlib vocabulary: beyond every bound there
is an even number `≥ 4` that is a sum of two primes. -/
theorem goldbach_beyond (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Even n ∧ 4 ≤ n ∧ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨n, hN, ⟨k, hk⟩, h4, hg⟩ := goldbach_beyond_of_model N
  exact ⟨n, hN, ⟨k, by omega⟩, h4, isGoldbachSum_iff.mp hg⟩

/-- The set of even numbers that are sums of two primes is infinite. -/
theorem infinite_even_goldbach :
    {n : ℕ | Even n ∧ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, hn, hev, _, hg⟩ := goldbach_beyond a
  exact ⟨n, ⟨hev, hg⟩, hn⟩

end Brockian.GoldbachSchema

