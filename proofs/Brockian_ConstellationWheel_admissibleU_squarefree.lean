import Mathlib
import Brockian.ConstellationLocalCount
import Brockian.ConstellationMultiplicative

/-
# Constellation Sieve Spectrum — Brick 3: the WHEEL PRODUCT (Euler product count).

Bricks 1–2 supplied the two structural facts behind a prime-constellation wheel:

* Brick 1 (`ConstellationLocalCount`): at a prime `p`, exactly `p − ν_p` residues dodge the
  constellation `H`, where `ν_p = |H mod p|` is the number of distinct residues of `H`.
* Brick 2 (`ConstellationMultiplicative`): the wheel-admissibility count
  `f n = |admissibleU n H|` is multiplicative across coprime moduli (CRT), with prime value
  `f p = p − ν_p`.

This brick fuses them into the **local-to-global product**: for a *squarefree* modulus `Q`,
the number of wheel-admissible residues is the exact Euler product of the local prime counts,

    |admissibleU Q H| = ∏_{p ∣ Q} (p − ν_p).

`admissibleU_squarefree` — the wheel product, by strong induction peeling one prime factor `p`
                          of `Q` (so `p ∤ Q/p`, `Coprime p (Q/p)`, `Q = p·(Q/p)`), applying
                          Brick 2 multiplicativity and Brick 1 at `p`, and splitting the
                          product over `Q.primeFactors = insert p (Q/p).primeFactors`. The base
                          case `Q = 1` is the empty product `1`, matching `|admissibleU 1 H| = 1`
                          (the trivial ring `ZMod 1` is a subsingleton, every element a unit).

`twin_wheel_count`       — the twin confinement `H = {0,2}` specialization: for squarefree `Q`
                          all of whose prime factors are `≥ 3`, every local count is `ν_p = 2`,
                          so the wheel count is exactly `∏_{p ∣ Q} (p − 2)`. This is the theorem
                          that turns the twin/first-Hardy–Littlewood factor `∏ (p − 2)` from an
                          ASSUMPTION into a proved exact count.

No `sorry`, `admit`, `native_decide`, or `axiom` is used. Core Mathlib only.
-/

namespace Brockian.ConstellationWheel

open Brockian.ConstellationMultiplicative

/-- **Brick 3 — the wheel product.** For a squarefree modulus `Q`, the number of
wheel-admissible residues for the constellation `H` is the exact Euler product of the local
prime counts `p − ν_p`, where `ν_p = |{ (h : ZMod p) : h ∈ H }|`:

    |admissibleU Q H| = ∏_{p ∣ Q} (p − |H mod p|).

Proof by strong induction on `Q`, peeling one prime factor `p`: squarefreeness gives `p ∤ Q/p`,
hence `Coprime p (Q/p)` and `Q = p · (Q/p)`. Brick 2 multiplicativity splits the count as a
product over the two coprime factors, Brick 1 evaluates the prime factor as `p − ν_p`, and the
induction hypothesis handles `Q/p`; the prime-factor set splits as
`insert p (Q/p).primeFactors`. The base `Q = 1` is the empty product `1`, and
`|admissibleU 1 H| = 1` since `ZMod 1` is a subsingleton (every element is a unit). -/
theorem admissibleU_squarefree (Q : ℕ) [NeZero Q] (hQ : Squarefree Q) (H : Finset ℤ) :
    (admissibleU Q H).card
      = ∏ p ∈ Q.primeFactors, (p - (H.image (fun h : ℤ => (h : ZMod p))).card) := by
  classical
  -- Generalize the `NeZero Q` instance to a plain hypothesis so we can strong-induct on `Q`.
  suffices key : ∀ n : ℕ, Squarefree n → ∀ (hn0 : n ≠ 0),
      (@admissibleU n ⟨hn0⟩ H).card
        = ∏ p ∈ n.primeFactors, (p - (H.image (fun h : ℤ => (h : ZMod p))).card) by
    exact key Q hQ (NeZero.ne Q)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn hn0
    rcases eq_or_ne n 1 with rfl | hn1
    · -- Base case `n = 1`: RHS is the empty product `1`, LHS is `1` (subsingleton ring).
      rw [Nat.primeFactors_one, Finset.prod_empty]
      have hEq : (@admissibleU 1 ⟨hn0⟩ H) = Finset.univ := by
        unfold admissibleU
        apply Finset.filter_true_of_mem
        intro a _ h _
        exact isUnit_of_subsingleton _
      rw [hEq, Finset.card_univ, ZMod.card]
    · -- Inductive step: peel a prime factor `p` of `n`.
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨m, rfl⟩ := hpn
      have hp0 : p ≠ 0 := left_ne_zero_of_mul hn0
      have hm0 : m ≠ 0 := right_ne_zero_of_mul hn0
      haveI : Fact p.Prime := ⟨hp⟩
      haveI hNp : NeZero p := ⟨hp0⟩
      haveI hNm : NeZero m := ⟨hm0⟩
      -- `p ∤ m`: else `p·p ∣ p·m`, forcing `IsUnit p`, contradicting primality.
      have hpm : ¬ p ∣ m := by
        intro hd
        exact hp.prime.not_unit (hn p (mul_dvd_mul_left p hd))
      have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
      have hmsq : Squarefree m := hn.squarefree_of_dvd (dvd_mul_left m p)
      have hlt : m < p * m := by
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have h2 : 2 * m ≤ p * m := mul_le_mul_right' hp.two_le m
        omega
      have hpnotmem : p ∉ m.primeFactors := by
        rw [Nat.mem_primeFactors]
        rintro ⟨-, hd, -⟩
        exact hpm hd
      have hpf : (p * m).primeFactors = insert p m.primeFactors := by
        rw [Nat.primeFactors_mul hp0 hm0, hp.primeFactors, Finset.insert_eq]
      calc (admissibleU (p * m) H).card
          = (admissibleU p H).card * (admissibleU m H).card := admissibleU_mul hcop H
        _ = (p - (H.image (fun h : ℤ => (h : ZMod p))).card) * (admissibleU m H).card := by
              rw [admissibleU_prime p H]
        _ = (p - (H.image (fun h : ℤ => (h : ZMod p))).card)
              * ∏ q ∈ m.primeFactors, (q - (H.image (fun h : ℤ => (h : ZMod q))).card) := by
              rw [IH m hlt hmsq hm0]
        _ = ∏ q ∈ (p * m).primeFactors,
              (q - (H.image (fun h : ℤ => (h : ZMod q))).card) := by
              rw [hpf, Finset.prod_insert hpnotmem]

/-- **Twin wheel count.** For a squarefree modulus `Q` all of whose prime factors are `≥ 3`,
the twin constellation `H = {0, 2}` has wheel count exactly `∏_{p ∣ Q} (p − 2)`.

At each prime `p ≥ 3` the two offsets `0, 2` are distinct mod `p` (since `p ∤ 2`), so the local
count is `ν_p = 2`; rewriting every factor `p − ν_p = p − 2` in the wheel product of
`admissibleU_squarefree` gives the result. This upgrades the twin/first-Hardy–Littlewood factor
`∏ (p − 2)` from an assumption to a proved exact count. -/
theorem twin_wheel_count (Q : ℕ) [NeZero Q] (hQ : Squarefree Q)
    (h3 : ∀ p ∈ Q.primeFactors, 3 ≤ p) :
    (admissibleU Q ({0, 2} : Finset ℤ)).card = ∏ p ∈ Q.primeFactors, (p - 2) := by
  classical
  rw [admissibleU_squarefree Q hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hp3 : 3 ≤ p := h3 p hp
  -- `2 ≠ 0` in `ZMod p` when `p ≥ 3`, so the offsets `{0,2}` are distinct mod `p` and `ν_p = 2`.
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 2] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hne : ((0 : ℤ) : ZMod p) ≠ ((2 : ℤ) : ZMod p) := by
    intro hc
    push_cast at hc
    exact h2ne hc.symm
  have himg : (({0, 2} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 2 := by
    rw [Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  rw [himg]

end Brockian.ConstellationWheel
