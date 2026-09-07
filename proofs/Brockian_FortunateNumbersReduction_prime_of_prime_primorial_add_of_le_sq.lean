import Mathlib

/-!
# Fortune Conjecture — conditional reduction module

CONDITIONAL: Fortune's conjecture (every fortunate number is prime) assuming the size
bound `H : ∀ n m, IsFortunate n m → m ≤ n ^ 2` (the fortunate number attached to `n#`
is at most `n ^ 2`).

Graduated from AXLE-verified Aristotle reduction
`Brockian.FortunateNumbers.FortuneConjecture`. Renamed namespace to avoid clashing with
the existing `Brockian/FortunateNumbers.lean` module.
-/

namespace Brockian.FortunateNumbersReduction

open Finset

/-- `IsFortunate n m` says that `m` is the *fortunate number* attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/
def IsFortunate (n m : ℕ) : Prop :=
  IsLeast {k : ℕ | 1 < k ∧ Nat.Prime (primorial n + k)} m

/-- **Unconditional structure result.** If `m > 1` and `n# + m` is prime, then no prime `q ≤ n`
divides `m`; i.e. every prime factor of `m` exceeds `n`.  (In particular a fortunate number is
coprime to `n#`.) -/
theorem not_dvd_of_prime_le {n m q : ℕ} (hm1 : 1 < m) (hp : Nat.Prime (primorial n + m))
    (hq : Nat.Prime q) (hqn : q ≤ n) : ¬ q ∣ m := by
  intro hdvdm
  have hdvdN : q ∣ primorial n :=
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq⟩)
  have hdvd : q ∣ primorial n + m := Nat.dvd_add hdvdN hdvdm
  have hle' : q ≤ m := Nat.le_of_dvd (by omega) hdvdm
  have hpos : 0 < primorial n := primorial_pos n
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h | h
  · exact hq.one_lt.ne' h
  · omega

/-- **Key unconditional step.** If `m > 1`, `n# + m` is prime and `m ≤ n ^ 2`, then `m` is prime.

Indeed, a composite `m` would have a prime factor `q` with `q ^ 2 ≤ m ≤ n ^ 2`, hence `q ≤ n`,
so `q` divides the primorial `n#` as well as `m`, hence divides the prime `n# + m`, which is
impossible since `1 < q < n# + m`. -/
theorem prime_of_prime_primorial_add_of_le_sq {n m : ℕ} (hm1 : 1 < m)
    (hp : Nat.Prime (primorial n + m)) (hle : m ≤ n ^ 2) : Nat.Prime m := by
  by_contra hmp
  have hqp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
  have hqn : m.minFac ≤ n := by
    by_contra hc
    have : n ^ 2 < m.minFac ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  exact not_dvd_of_prime_le hm1 hp hqp hqn (Nat.minFac_dvd m)

/-- **Fortune's conjecture, conditional reduction.**

Fortune's conjecture states that every fortunate number is prime; it is open.  The statement
below reduces it to the size bound saying that the fortunate number attached to `n#` is at
most `n ^ 2`.  (Fortunate numbers are conjecturally of size `O((log n)^2)`, far below `n ^ 2`,
so `hgap` is a very weak form of the expected prime-gap behaviour after primorials.) -/
theorem FortuneConjecture (hgap : ∀ n m : ℕ, IsFortunate n m → m ≤ n ^ 2) :
    ∀ n m : ℕ, IsFortunate n m → Nat.Prime m := fun n m hm =>
  prime_of_prime_primorial_add_of_le_sq hm.1.1 hm.1.2 (hgap n m hm)

end Brockian.FortunateNumbersReduction
