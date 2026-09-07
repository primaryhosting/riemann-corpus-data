import Mathlib
import Brockian.ConstellationLocalCount
import Brockian.ConstellationMultiplicative
import Brockian.ConstellationWheel

/-
# Constellation Sieve Spectrum — GATE sub-brick 3: EDGE and RUN Euler-product counts.

Bricks 1–3 (`ConstellationLocalCount`, `ConstellationMultiplicative`, `ConstellationWheel`)
supplied the general wheel machinery: at a prime `p` the wheel-admissible count of a
constellation `H` is `p − ν_p` (`ν_p = |H mod p|`), the count is CRT-multiplicative, and for a
squarefree modulus `Q` it equals the exact Euler product `∏_{p ∣ Q} (p − ν_p)`.

This file specializes that machinery to the two derived offset sets that arise on the twin
wheel (a vertex `a` is *present* iff `{0,2}` is admissible, i.e. `a, a+2` are both units):

* a `+3` EDGE `a ~ a+3` is present iff BOTH endpoints are present, i.e. `a, a+2, a+3, a+5`
  are all units — offset set `H_E = {0,2,3,5}`;
* a `P3` RUN `a, a+3, a+6` (three vertices in a line) is present iff `a, a+2, a+3, a+5, a+6, a+8`
  are all units — offset set `H_T = {0,2,3,5,6,8}`.

The arithmetic content:

`nu_E`      — for a prime `p ≥ 7`, the four offsets `0,2,3,5` are pairwise distinct mod `p`
              (every pairwise difference has absolute value in `{1,2,3,5}`, all `< 7 ≤ p`), so
              `ν = 4`.
`nu_T`      — for a prime `p ≥ 7`, the six offsets `0,2,3,5,6,8` are pairwise distinct mod `p`.
              The pairwise absolute differences are `{1,2,3,4,5,6,8}` — note `7` is NOT among
              them, which is exactly why `ν = 6` holds even at `p = 7` (where `8 ≡ 1`, and
              `1 ∉ {0,2,3,5,6}`). For `p ≥ 7` no such difference is divisible by `p` (the `≤ 6`
              ones since `p > 6`, and `8` since `p` is an odd prime so `p ∤ 8 = 2^3`).
`E_local`   — edge local count `|admissibleU p {0,2,3,5}| = p − 4` for prime `p ≥ 7`.
`T_local`   — run  local count `|admissibleU p {0,2,3,5,6,8}| = p − 6` for prime `p ≥ 7`.
`E_wheel`   — edge count `|admissibleU Q {0,2,3,5}| = ∏_{p ∣ Q} (p − 4)` for squarefree `Q`
              all of whose prime factors are `≥ 7`.
`T_wheel`   — run  count `|admissibleU Q {0,2,3,5,6,8}| = ∏_{p ∣ Q} (p − 6)`, likewise.

These are the essential arithmetic content of the gate: the exact edge Euler product `∏ (p − 4)`
and the exact run Euler product `∏ (p − 6)`.

## Algebraic path-multiplicity reconstruction (`recon_V`, `recon_E`, `recon_T`).

For a disjoint union of paths with `n1` singletons (`P1`), `n2` edges (`P2`), `n3` length-two
runs (`P3`), the vertex / edge / run totals satisfy
    V = n1 + 2·n2 + 3·n3,   E = n2 + 2·n3,   T = n3.
Inverting: `n3 = T`, `n2 = E − 2·T`, `n1 = V − 2·E + T`. We define `n1, n2, n3` by these inverse
formulas (over `ℤ`, to avoid `ℕ` truncation) and prove the forward reconstruction identities
    `V = n1 + 2·n2 + 3·n3`,   `E = n2 + 2·n3`,   `T = n3`,
which are clean `ring` identities. (The vertex identity carries coefficient `3` on `n3`, not `1`:
a `P3` component has three vertices. This is the mathematically correct reconstruction.)

### HONEST SCOPE.
`V`, `E`, `T` here are the EXACT Euler products of the vertex / edge / run offset sets — that
part is fully proved. The algebraic multiplicities `n1, n2, n3` satisfy the reconstruction
identities as pure algebra. Their identification with the actual `P1/P2/P3` component counts of
the twin wheel graph requires the (still-open) graph-decomposition theorem and is NOT claimed
here; only the arithmetic Euler products and the algebraic reconstruction are established.

No `sorry`, `admit`, `native_decide`, or `axiom` is used. Core Mathlib only.
-/

namespace Brockian.ConstellationCounts

open Brockian.ConstellationMultiplicative
open Brockian.ConstellationWheel

/-- For an integer `d` with `0 < |d| ≤ 6` and a modulus `p ≥ 7`, `p ∤ d` (over `ℤ`). -/
private theorem not_dvd_le6 (p : ℕ) (hp : 7 ≤ p) {d : ℤ} (hd0 : d ≠ 0)
    (h6 : d.natAbs ≤ 6) : ¬ (p : ℤ) ∣ d := by
  intro h
  have hp' : p ∣ d.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h
  have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
  have := Nat.le_of_dvd hpos hp'
  omega

/-- For an integer `d` with `|d| = 8` and a prime `p ≥ 7`, `p ∤ d` (since `8 = 2^3` and `p`
is an odd prime). -/
private theorem not_dvd_8 (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) {d : ℤ}
    (hd : d.natAbs = 8) : ¬ (p : ℤ) ∣ d := by
  intro h
  have hp' : p ∣ d.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h
  rw [hd] at hp'
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8] at hp'
  have hp2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hp'
  have := Nat.le_of_dvd (by norm_num) hp2
  omega

/-- Distinctness bridge: if `p ∤ (a − b)` over `ℤ`, then the integer casts of `a` and `b` into
`ZMod p` are distinct. -/
private theorem castNe (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : ¬ (p : ℤ) ∣ (a - b)) :
    ((a : ZMod p)) ≠ ((b : ZMod p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  intro hc
  apply h
  have hz : ((a - b : ℤ) : ZMod p) = 0 := by push_cast; rw [hc]; ring
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

/-- **Edge offset multiplicity.** For a prime `p ≥ 7`, the offsets `0,2,3,5` reduce to four
distinct residues mod `p`, so `ν = 4`. -/
private theorem nu_E (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (({0, 2, 3, 5} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 4 := by
  have e02 : ((0 : ℤ) : ZMod p) ≠ ((2 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e03 : ((0 : ℤ) : ZMod p) ≠ ((3 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e05 : ((0 : ℤ) : ZMod p) ≠ ((5 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e23 : ((2 : ℤ) : ZMod p) ≠ ((3 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e25 : ((2 : ℤ) : ZMod p) ≠ ((5 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e35 : ((3 : ℤ) : ZMod p) ≠ ((5 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  rw [Finset.image_insert, Finset.image_insert, Finset.image_insert, Finset.image_singleton,
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨e02, e03, e05⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨e23, e25⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_singleton]; exact e35),
      Finset.card_singleton]

/-- **Run offset multiplicity.** For a prime `p ≥ 7`, the offsets `0,2,3,5,6,8` reduce to six
distinct residues mod `p`, so `ν = 6`. -/
private theorem nu_T (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (({0, 2, 3, 5, 6, 8} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 6 := by
  have e02 : ((0 : ℤ) : ZMod p) ≠ ((2 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e03 : ((0 : ℤ) : ZMod p) ≠ ((3 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e05 : ((0 : ℤ) : ZMod p) ≠ ((5 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e06 : ((0 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e08 : ((0 : ℤ) : ZMod p) ≠ ((8 : ℤ) : ZMod p) :=
    castNe p (not_dvd_8 p hp (by decide))
  have e23 : ((2 : ℤ) : ZMod p) ≠ ((3 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e25 : ((2 : ℤ) : ZMod p) ≠ ((5 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e26 : ((2 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e28 : ((2 : ℤ) : ZMod p) ≠ ((8 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e35 : ((3 : ℤ) : ZMod p) ≠ ((5 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e36 : ((3 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e38 : ((3 : ℤ) : ZMod p) ≠ ((8 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e56 : ((5 : ℤ) : ZMod p) ≠ ((6 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e58 : ((5 : ℤ) : ZMod p) ≠ ((8 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  have e68 : ((6 : ℤ) : ZMod p) ≠ ((8 : ℤ) : ZMod p) :=
    castNe p (not_dvd_le6 p hp (by decide) (by decide))
  rw [Finset.image_insert, Finset.image_insert, Finset.image_insert, Finset.image_insert,
      Finset.image_insert, Finset.image_singleton,
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
            exact ⟨e02, e03, e05, e06, e08⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
            exact ⟨e23, e25, e26, e28⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
            exact ⟨e35, e36, e38⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨e56, e58⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_singleton]; exact e68),
      Finset.card_singleton]

/-- **Edge local count.** For a prime `p ≥ 7`, the number of wheel-admissible residues for the
edge offset set `{0,2,3,5}` is exactly `p − 4`. -/
theorem E_local (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (admissibleU p ({0, 2, 3, 5} : Finset ℤ)).card = p - 4 := by
  rw [admissibleU_prime p ({0, 2, 3, 5} : Finset ℤ), nu_E p hp]

/-- **Run local count.** For a prime `p ≥ 7`, the number of wheel-admissible residues for the
run offset set `{0,2,3,5,6,8}` is exactly `p − 6`. -/
theorem T_local (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (admissibleU p ({0, 2, 3, 5, 6, 8} : Finset ℤ)).card = p - 6 := by
  rw [admissibleU_prime p ({0, 2, 3, 5, 6, 8} : Finset ℤ), nu_T p hp]

/-- **Edge wheel count (Euler product).** For a squarefree modulus `Q` all of whose prime
factors are `≥ 7`, the edge count is the exact Euler product `∏_{p ∣ Q} (p − 4)`. -/
theorem E_wheel (Q : ℕ) [NeZero Q] (hQ : Squarefree Q)
    (h7 : ∀ p ∈ Q.primeFactors, 7 ≤ p) :
    (admissibleU Q ({0, 2, 3, 5} : Finset ℤ)).card = ∏ p ∈ Q.primeFactors, (p - 4) := by
  rw [admissibleU_squarefree Q hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  rw [nu_E p (h7 p hp)]

/-- **Run wheel count (Euler product).** For a squarefree modulus `Q` all of whose prime
factors are `≥ 7`, the run count is the exact Euler product `∏_{p ∣ Q} (p − 6)`. -/
theorem T_wheel (Q : ℕ) [NeZero Q] (hQ : Squarefree Q)
    (h7 : ∀ p ∈ Q.primeFactors, 7 ≤ p) :
    (admissibleU Q ({0, 2, 3, 5, 6, 8} : Finset ℤ)).card = ∏ p ∈ Q.primeFactors, (p - 6) := by
  rw [admissibleU_squarefree Q hQ]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  rw [nu_T p (h7 p hp)]

/-! ### Algebraic path-multiplicity reconstruction (over `ℤ`).

`n1, n2, n3` are the inverse formulas expressing the `P1/P2/P3` component multiplicities in
terms of the vertex/edge/run totals `V, E, T`; the theorems below re-derive `V, E, T` from
them, closing the reconstruction loop. -/

/-- `P1`-multiplicity (isolated vertices): `n1 = V − 2E + T`. -/
def n1 (V E T : ℤ) : ℤ := V - 2 * E + T

/-- `P2`-multiplicity (edges/2-runs): `n2 = E − 2T`. -/
def n2 (E T : ℤ) : ℤ := E - 2 * T

/-- `P3`-multiplicity (3-runs): `n3 = T`. -/
def n3 (T : ℤ) : ℤ := T

/-- Vertex reconstruction: a `P1` has 1 vertex, a `P2` has 2, a `P3` has 3. -/
theorem recon_V (V E T : ℤ) : V = n1 V E T + 2 * n2 E T + 3 * n3 T := by
  unfold n1 n2 n3; ring

/-- Edge reconstruction: a `P2` has 1 edge, a `P3` has 2. -/
theorem recon_E (E T : ℤ) : E = n2 E T + 2 * n3 T := by
  unfold n2 n3; ring

/-- Run reconstruction: only `P3` components carry a 3-run. -/
theorem recon_T (T : ℤ) : T = n3 T := rfl

end Brockian.ConstellationCounts
