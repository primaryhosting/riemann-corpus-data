/-!
# Exact counts for the twin-sieve spectral campaign

This module repairs the component-count algebra and closes the prime-local
forbidden-offset counts used by the squarefree twin-sieve wheel.

If components have sizes one, two, and three with counts `n1`, `n2`, and
`n3`, while `V`, `E`, and `T` count vertices, edges, and three-vertex
components, then

* `V = n1 + 2*n2 + 3*n3`,
* `E = n2 + 2*n3`, and
* `T = n3`.

The subtraction-safe consequence is `n1 + 2*E = V + T`.  For wheel products
`V = 3*A`, `E = 2*B`, and `T = C`, this becomes
`n1 + 4*B = 3*A + C`.  The commonly written natural-number expression
`3*A - 4*B + C` is not safe because `Nat` subtraction truncates; at `A=B=C=1`
it evaluates to one even though the correct count is zero.
-/

import Mathlib
import Brockian.AdmissibilityKTuple
import Brockian.AdmissibilityCRTGeneral

set_option autoImplicit false

open Finset
open Brockian.AdmissibilityKTuple
open Brockian.AdmissibilityCRTGeneral

namespace Brockian.SieveSpectrumCounts

/-! ## Subtraction-safe component algebra -/

/-- Vertex/edge/three-component accounting determines the component counts
without any truncated subtraction. -/
theorem component_count_relations
    {n1 n2 n3 V E T : Nat}
    (hV : n1 + 2 * n2 + 3 * n3 = V)
    (hE : n2 + 2 * n3 = E)
    (hT : n3 = T) :
    n3 = T ∧ n2 + 2 * T = E ∧ n1 + 2 * E = V + T := by
  subst T
  constructor
  · rfl
  constructor
  · exact hE
  omega

/-- Product-form specialization for a twin-sieve wheel.  This is the canonical
natural-number statement of the corrected formulas. -/
theorem wheel_component_count_relations
    {n1 n2 n3 A B C : Nat}
    (hV : n1 + 2 * n2 + 3 * n3 = 3 * A)
    (hE : n2 + 2 * n3 = 2 * B)
    (hT : n3 = C) :
    n3 = C ∧ n2 + 2 * C = 2 * B ∧ n1 + 4 * B = 3 * A + C := by
  obtain ⟨hn3, hn2, hn1⟩ :=
    component_count_relations hV hE hT
  exact ⟨hn3, hn2, by omega⟩

/-- The familiar closed formulas are exact over integers, where subtraction
does not truncate. -/
theorem wheel_component_count_int_form
    {n1 n2 n3 A B C : Nat}
    (hV : n1 + 2 * n2 + 3 * n3 = 3 * A)
    (hE : n2 + 2 * n3 = 2 * B)
    (hT : n3 = C) :
    (n1 : Int) = 3 * A - 4 * B + C ∧
      (n2 : Int) = 2 * B - 2 * C ∧ (n3 : Int) = C := by
  obtain ⟨hn3, hn2, hn1⟩ :=
    wheel_component_count_relations hV hE hT
  constructor <;> omega

/-- Once nonnegativity is available, the safe natural-number closed forms use
subtraction only after all positive terms have been assembled. -/
theorem wheel_component_count_nat_form
    {n1 n2 n3 A B C : Nat}
    (hV : n1 + 2 * n2 + 3 * n3 = 3 * A)
    (hE : n2 + 2 * n3 = 2 * B)
    (hT : n3 = C) :
    n1 = 3 * A + C - 4 * B ∧
      n2 = 2 * B - 2 * C ∧ n3 = C := by
  obtain ⟨hn3, hn2, hn1⟩ :=
    wheel_component_count_relations hV hE hT
  constructor <;> omega

/-- The multiplicity of the central eigenvalue `2` is `n1+n3`; its safe
product relation is therefore `(n1+n3) + 4*B = 3*A + 2*C`. -/
theorem wheel_spectral_multiplicity_relations
    {n1 n2 n3 A B C : Nat}
    (hV : n1 + 2 * n2 + 3 * n3 = 3 * A)
    (hE : n2 + 2 * n3 = 2 * B)
    (hT : n3 = C) :
    n3 = C ∧ n2 + 2 * C = 2 * B ∧
      (n1 + n3) + 4 * B = 3 * A + 2 * C := by
  obtain ⟨hn3, hn2, hn1⟩ :=
    wheel_component_count_relations hV hE hT
  exact ⟨hn3, hn2, by omega⟩

/-- Concrete witness that the left-associated natural-number formula is not a
valid boundary-wheel statement. -/
theorem nat_subtraction_boundary_counterexample :
    3 * 1 - 4 * 1 + 1 = 1 ∧ 3 * 1 + 1 - 4 * 1 = 0 := by
  norm_num

/-! ## Prime-local forbidden-offset counts -/

/-- Offsets struck by requiring `a` and `a+2` to be nonzero. -/
def vertexOffsets (p : Nat) : Finset (ZMod p) := {0, 2}

/-- Offsets struck by requiring both `a` and `a+3` to be twin-admissible. -/
def edgeOffsets (p : Nat) : Finset (ZMod p) := {0, 2, 3, 5}

/-- Offsets struck by a three-vertex run `a, a+3, a+6`. -/
def tripleRunOffsets (p : Nat) : Finset (ZMod p) := {0, 2, 3, 5, 6, 8}

private theorem natCast_ne_natCast_of_lt
    {a b p : Nat} (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    (a : ZMod p) ≠ (b : ZMod p) := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
  exact hab hv

private theorem prime_ge_seven_cases {p : Nat} (hp : p.Prime) (h7 : 7 ≤ p) :
    p = 7 ∨ 8 < p := by
  by_cases hp7 : p = 7
  · exact Or.inl hp7
  right
  have hp8 : p ≠ 8 := by
    intro h
    subst p
    norm_num at hp
  omega

theorem vertexOffsets_card {p : Nat} (hp : p.Prime) (h7 : 7 ≤ p) :
    (vertexOffsets p).card = 2 := by
  rcases prime_ge_seven_cases hp h7 with rfl | hp8
  · decide
  rw [vertexOffsets, Finset.card_pair]
  simpa using (natCast_ne_natCast_of_lt (a := 0) (b := 2) (p := p)
    (by omega) (by omega) (by norm_num))

theorem edgeOffsets_card {p : Nat} (hp : p.Prime) (h7 : 7 ≤ p) :
    (edgeOffsets p).card = 4 := by
  rcases prime_ge_seven_cases hp h7 with rfl | hp8
  · decide
  simp only [edgeOffsets]
  have h02 : (0 : ZMod p) ≠ 2 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 2) (p := p) (by omega) (by omega) (by norm_num))
  have h03 : (0 : ZMod p) ≠ 3 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 3) (p := p) (by omega) (by omega) (by norm_num))
  have h05 : (0 : ZMod p) ≠ 5 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 5) (p := p) (by omega) (by omega) (by norm_num))
  have h23 : (2 : ZMod p) ≠ 3 := natCast_ne_natCast_of_lt
    (a := 2) (b := 3) (p := p) (by omega) (by omega) (by norm_num)
  have h25 : (2 : ZMod p) ≠ 5 := natCast_ne_natCast_of_lt
    (a := 2) (b := 5) (p := p) (by omega) (by omega) (by norm_num)
  have h35 : (3 : ZMod p) ≠ 5 := natCast_ne_natCast_of_lt
    (a := 3) (b := 5) (p := p) (by omega) (by omega) (by norm_num)
  have h0 : (0 : ZMod p) ∉ ({2, 3, 5} : Finset (ZMod p)) := by
    simp [h02, h03, h05]
  have h2 : (2 : ZMod p) ∉ ({3, 5} : Finset (ZMod p)) := by
    simp [h23, h25]
  have h3 : (3 : ZMod p) ∉ ({5} : Finset (ZMod p)) := by
    simp [h35]
  rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton]

theorem tripleRunOffsets_card {p : Nat} (hp : p.Prime) (h7 : 7 ≤ p) :
    (tripleRunOffsets p).card = 6 := by
  rcases prime_ge_seven_cases hp h7 with rfl | hp8
  · decide
  simp only [tripleRunOffsets]
  have h02 : (0 : ZMod p) ≠ 2 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 2) (p := p) (by omega) (by omega) (by norm_num))
  have h03 : (0 : ZMod p) ≠ 3 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 3) (p := p) (by omega) (by omega) (by norm_num))
  have h05 : (0 : ZMod p) ≠ 5 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 5) (p := p) (by omega) (by omega) (by norm_num))
  have h06 : (0 : ZMod p) ≠ 6 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 6) (p := p) (by omega) (by omega) (by norm_num))
  have h08 : (0 : ZMod p) ≠ 8 := by simpa using (natCast_ne_natCast_of_lt
    (a := 0) (b := 8) (p := p) (by omega) (by omega) (by norm_num))
  have h23 : (2 : ZMod p) ≠ 3 := natCast_ne_natCast_of_lt
    (a := 2) (b := 3) (p := p) (by omega) (by omega) (by norm_num)
  have h25 : (2 : ZMod p) ≠ 5 := natCast_ne_natCast_of_lt
    (a := 2) (b := 5) (p := p) (by omega) (by omega) (by norm_num)
  have h26 : (2 : ZMod p) ≠ 6 := natCast_ne_natCast_of_lt
    (a := 2) (b := 6) (p := p) (by omega) (by omega) (by norm_num)
  have h28 : (2 : ZMod p) ≠ 8 := natCast_ne_natCast_of_lt
    (a := 2) (b := 8) (p := p) (by omega) (by omega) (by norm_num)
  have h35 : (3 : ZMod p) ≠ 5 := natCast_ne_natCast_of_lt
    (a := 3) (b := 5) (p := p) (by omega) (by omega) (by norm_num)
  have h36 : (3 : ZMod p) ≠ 6 := natCast_ne_natCast_of_lt
    (a := 3) (b := 6) (p := p) (by omega) (by omega) (by norm_num)
  have h38 : (3 : ZMod p) ≠ 8 := natCast_ne_natCast_of_lt
    (a := 3) (b := 8) (p := p) (by omega) (by omega) (by norm_num)
  have h56 : (5 : ZMod p) ≠ 6 := natCast_ne_natCast_of_lt
    (a := 5) (b := 6) (p := p) (by omega) (by omega) (by norm_num)
  have h58 : (5 : ZMod p) ≠ 8 := natCast_ne_natCast_of_lt
    (a := 5) (b := 8) (p := p) (by omega) (by omega) (by norm_num)
  have h68 : (6 : ZMod p) ≠ 8 := natCast_ne_natCast_of_lt
    (a := 6) (b := 8) (p := p) (by omega) (by omega) (by norm_num)
  have h0 : (0 : ZMod p) ∉ ({2, 3, 5, 6, 8} : Finset (ZMod p)) := by
    simp [h02, h03, h05, h06, h08]
  have h2 : (2 : ZMod p) ∉ ({3, 5, 6, 8} : Finset (ZMod p)) := by
    simp [h23, h25, h26, h28]
  have h3 : (3 : ZMod p) ∉ ({5, 6, 8} : Finset (ZMod p)) := by
    simp [h35, h36, h38]
  have h5 : (5 : ZMod p) ∉ ({6, 8} : Finset (ZMod p)) := by
    simp [h56, h58]
  have h6 : (6 : ZMod p) ∉ ({8} : Finset (ZMod p)) := by
    simp [h68]
  rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h5,
    Finset.card_insert_of_notMem h6, Finset.card_singleton]

/-- Prime-local vertex factor `p-2`. -/
theorem vertex_count_prime {p : Nat} [NeZero p] (hp : p.Prime) (h7 : 7 ≤ p) :
    (admissibleTupleResidues p (vertexOffsets p)).card = p - 2 := by
  rw [admissibleTupleResidues_card, vertexOffsets_card hp h7]

/-- Prime-local edge factor `p-4`. -/
theorem edge_count_prime {p : Nat} [NeZero p] (hp : p.Prime) (h7 : 7 ≤ p) :
    (admissibleTupleResidues p (edgeOffsets p)).card = p - 4 := by
  rw [admissibleTupleResidues_card, edgeOffsets_card hp h7]

/-- Prime-local three-run factor `p-6`. -/
theorem triple_run_count_prime {p : Nat} [NeZero p] (hp : p.Prime) (h7 : 7 ≤ p) :
    (admissibleTupleResidues p (tripleRunOffsets p)).card = p - 6 := by
  rw [admissibleTupleResidues_card, tripleRunOffsets_card hp h7]

/-! ## Iterated CRT products over the large wheel primes -/

/-- For a finite injective family of primes at least seven, the twin-admissible
vertex count is the exact product `prod_i (p_i - 2)`. -/
theorem vertex_count_prime_family
    {ι : Type*} [Fintype ι] (p : ι -> Nat) [∀ i, NeZero (p i)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) :
    (Finset.univ.filter (fun a : ZMod (∏ i, p i) =>
        ∀ i, (ZMod.prodEquivPi p (pairwise_coprime_of_primes p hp hinj) a) i
          ∈ admissibleTupleResidues (p i) (vertexOffsets (p i)))).card
      = ∏ i, (p i - 2) := by
  rw [admissibleTupleResidues_prodCRT_primes_card p hp hinj]
  exact Finset.prod_congr rfl fun i _ => by
    rw [vertexOffsets_card (hp i) (h7 i)]

/-- The exact edge-survivor product `prod_i (p_i - 4)`. -/
theorem edge_count_prime_family
    {ι : Type*} [Fintype ι] (p : ι -> Nat) [∀ i, NeZero (p i)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) :
    (Finset.univ.filter (fun a : ZMod (∏ i, p i) =>
        ∀ i, (ZMod.prodEquivPi p (pairwise_coprime_of_primes p hp hinj) a) i
          ∈ admissibleTupleResidues (p i) (edgeOffsets (p i)))).card
      = ∏ i, (p i - 4) := by
  rw [admissibleTupleResidues_prodCRT_primes_card p hp hinj]
  exact Finset.prod_congr rfl fun i _ => by
    rw [edgeOffsets_card (hp i) (h7 i)]

/-- The exact three-run product `prod_i (p_i - 6)`. -/
theorem triple_run_count_prime_family
    {ι : Type*} [Fintype ι] (p : ι -> Nat) [∀ i, NeZero (p i)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) :
    (Finset.univ.filter (fun a : ZMod (∏ i, p i) =>
        ∀ i, (ZMod.prodEquivPi p (pairwise_coprime_of_primes p hp hinj) a) i
          ∈ admissibleTupleResidues (p i) (tripleRunOffsets (p i)))).card
      = ∏ i, (p i - 6) := by
  rw [admissibleTupleResidues_prodCRT_primes_card p hp hinj]
  exact Finset.prod_congr rfl fun i _ => by
    rw [tripleRunOffsets_card (hp i) (h7 i)]

/-! ## The full `15 * Q` prime family -/

/-- Adjoin the small wheel primes `3` and `5` to the large-prime family. -/
def fullWheelPrime {ι : Type*} (p : ι -> Nat) : Fin 2 ⊕ ι -> Nat
  | Sum.inl j => if j = 0 then 3 else 5
  | Sum.inr i => p i

theorem fullWheelPrime_prime
    {ι : Type*} (p : ι -> Nat) (hp : ∀ i, (p i).Prime) :
    ∀ j, (fullWheelPrime p j).Prime := by
  intro j
  cases j with
  | inl j => fin_cases j <;> norm_num [fullWheelPrime]
  | inr i => exact hp i

theorem fullWheelPrime_injective
    {ι : Type*} (p : ι -> Nat) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) : Function.Injective (fullWheelPrime p) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          fin_cases x <;> fin_cases y <;> simp [fullWheelPrime] at hxy ⊢
      | inr y =>
          fin_cases x <;> simp [fullWheelPrime] at hxy
          all_goals have := h7 y; omega
  | inr x =>
      cases y with
      | inl y =>
          fin_cases y <;> simp [fullWheelPrime] at hxy
          all_goals have := h7 x; omega
      | inr y =>
          apply congrArg Sum.inr
          apply hinj
          simpa [fullWheelPrime] using hxy

private theorem vertexOffsets_card_three : (vertexOffsets 3).card = 2 := by decide
private theorem vertexOffsets_card_five : (vertexOffsets 5).card = 2 := by decide
private theorem edgeOffsets_card_three : (edgeOffsets 3).card = 2 := by decide
private theorem edgeOffsets_card_five : (edgeOffsets 5).card = 3 := by decide
private theorem tripleRunOffsets_card_three : (tripleRunOffsets 3).card = 2 := by decide
private theorem tripleRunOffsets_card_five : (tripleRunOffsets 5).card = 4 := by decide

/-- The complete vertex factor over `{3,5} union {p_i}` is
`1 * 3 * prod_i (p_i-2)`. -/
theorem fullWheel_vertex_factor
    {ι : Type*} [Fintype ι] (p : ι -> Nat)
    (hp : ∀ i, (p i).Prime) (h7 : ∀ i, 7 ≤ p i) :
    (∏ j : Fin 2 ⊕ ι,
      (fullWheelPrime p j - (vertexOffsets (fullWheelPrime p j)).card))
      = 3 * ∏ i, (p i - 2) := by
  rw [Fintype.prod_sum_type]
  have hsmall :
      (∏ j : Fin 2,
        (fullWheelPrime p (Sum.inl j) -
          (vertexOffsets (fullWheelPrime p (Sum.inl j))).card)) = 3 := by
    rw [Fin.prod_univ_two]
    change (3 - (vertexOffsets 3).card) * (5 - (vertexOffsets 5).card) = 3
    rw [vertexOffsets_card_three, vertexOffsets_card_five]
  rw [hsmall]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    simp only [fullWheelPrime]
    rw [vertexOffsets_card (hp i) (h7 i)]

/-- The complete edge factor is `1 * 2 * prod_i (p_i-4)`. -/
theorem fullWheel_edge_factor
    {ι : Type*} [Fintype ι] (p : ι -> Nat)
    (hp : ∀ i, (p i).Prime) (h7 : ∀ i, 7 ≤ p i) :
    (∏ j : Fin 2 ⊕ ι,
      (fullWheelPrime p j - (edgeOffsets (fullWheelPrime p j)).card))
      = 2 * ∏ i, (p i - 4) := by
  rw [Fintype.prod_sum_type]
  have hsmall :
      (∏ j : Fin 2,
        (fullWheelPrime p (Sum.inl j) -
          (edgeOffsets (fullWheelPrime p (Sum.inl j))).card)) = 2 := by
    rw [Fin.prod_univ_two]
    change (3 - (edgeOffsets 3).card) * (5 - (edgeOffsets 5).card) = 2
    rw [edgeOffsets_card_three, edgeOffsets_card_five]
  rw [hsmall]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    simp only [fullWheelPrime]
    rw [edgeOffsets_card (hp i) (h7 i)]

/-- The complete three-run factor is `1 * 1 * prod_i (p_i-6)`. -/
theorem fullWheel_triple_run_factor
    {ι : Type*} [Fintype ι] (p : ι -> Nat)
    (hp : ∀ i, (p i).Prime) (h7 : ∀ i, 7 ≤ p i) :
    (∏ j : Fin 2 ⊕ ι,
      (fullWheelPrime p j - (tripleRunOffsets (fullWheelPrime p j)).card))
      = ∏ i, (p i - 6) := by
  rw [Fintype.prod_sum_type]
  have hsmall :
      (∏ j : Fin 2,
        (fullWheelPrime p (Sum.inl j) -
          (tripleRunOffsets (fullWheelPrime p (Sum.inl j))).card)) = 1 := by
    rw [Fin.prod_univ_two]
    change (3 - (tripleRunOffsets 3).card) *
      (5 - (tripleRunOffsets 5).card) = 1
    rw [tripleRunOffsets_card_three, tripleRunOffsets_card_five]
  rw [hsmall, one_mul]
  exact Finset.prod_congr rfl fun i _ => by
    simp only [fullWheelPrime]
    rw [tripleRunOffsets_card (hp i) (h7 i)]

/-- Exact vertex count over the full squarefree wheel prime family. -/
theorem fullWheel_vertex_count
    {ι : Type*} [Fintype ι] (p : ι -> Nat)
    [∀ j, NeZero (fullWheelPrime p j)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) :
    let q := fullWheelPrime p
    let hq := fullWheelPrime_prime p hp
    let hqi := fullWheelPrime_injective p hinj h7
    (Finset.univ.filter (fun a : ZMod (∏ j, q j) =>
        ∀ j, (ZMod.prodEquivPi q
          (pairwise_coprime_of_primes q hq hqi) a) j
            ∈ admissibleTupleResidues (q j) (vertexOffsets (q j)))).card
      = 3 * ∏ i, (p i - 2) := by
  dsimp only
  rw [admissibleTupleResidues_prodCRT_primes_card
    (fullWheelPrime p) (fullWheelPrime_prime p hp)
    (fullWheelPrime_injective p hinj h7)]
  exact fullWheel_vertex_factor p hp h7

/-- Exact edge count over the full squarefree wheel prime family. -/
theorem fullWheel_edge_count
    {ι : Type*} [Fintype ι] (p : ι -> Nat)
    [∀ j, NeZero (fullWheelPrime p j)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) :
    let q := fullWheelPrime p
    let hq := fullWheelPrime_prime p hp
    let hqi := fullWheelPrime_injective p hinj h7
    (Finset.univ.filter (fun a : ZMod (∏ j, q j) =>
        ∀ j, (ZMod.prodEquivPi q
          (pairwise_coprime_of_primes q hq hqi) a) j
            ∈ admissibleTupleResidues (q j) (edgeOffsets (q j)))).card
      = 2 * ∏ i, (p i - 4) := by
  dsimp only
  rw [admissibleTupleResidues_prodCRT_primes_card
    (fullWheelPrime p) (fullWheelPrime_prime p hp)
    (fullWheelPrime_injective p hinj h7)]
  exact fullWheel_edge_factor p hp h7

/-- Exact three-run count over the full squarefree wheel prime family. -/
theorem fullWheel_triple_run_count
    {ι : Type*} [Fintype ι] (p : ι -> Nat)
    [∀ j, NeZero (fullWheelPrime p j)]
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, 7 ≤ p i) :
    let q := fullWheelPrime p
    let hq := fullWheelPrime_prime p hp
    let hqi := fullWheelPrime_injective p hinj h7
    (Finset.univ.filter (fun a : ZMod (∏ j, q j) =>
        ∀ j, (ZMod.prodEquivPi q
          (pairwise_coprime_of_primes q hq hqi) a) j
            ∈ admissibleTupleResidues (q j) (tripleRunOffsets (q j)))).card
      = ∏ i, (p i - 6) := by
  dsimp only
  rw [admissibleTupleResidues_prodCRT_primes_card
    (fullWheelPrime p) (fullWheelPrime_prime p hp)
    (fullWheelPrime_injective p hinj h7)]
  exact fullWheel_triple_run_factor p hp h7

/-! ## Boundary-wheel arithmetic checks -/

/-- The three large-prime Euler factors `(A,B,C)` for a finite prime set. -/
def wheelFactors (S : Finset Nat) : Nat × Nat × Nat :=
  (∏ p ∈ S, (p - 2), ∏ p ∈ S, (p - 4), ∏ p ∈ S, (p - 6))

/-- Predicted counts `(n1,n2,n3)`, using subtraction only after positive
terms are assembled. -/
def predictedComponentCounts (S : Finset Nat) : Nat × Nat × Nat :=
  let F := wheelFactors S
  (3 * F.1 + F.2.2 - 4 * F.2.1, 2 * F.2.1 - 2 * F.2.2, F.2.2)

theorem boundary_wheel_Q1 :
    wheelFactors ∅ = (1, 1, 1) ∧ predictedComponentCounts ∅ = (0, 0, 1) := by
  norm_num [wheelFactors, predictedComponentCounts]

theorem boundary_wheel_Q7 :
    wheelFactors {7} = (5, 3, 1) ∧ predictedComponentCounts {7} = (4, 4, 1) := by
  norm_num [wheelFactors, predictedComponentCounts]

theorem boundary_wheel_Q11 :
    wheelFactors {11} = (9, 7, 5) ∧ predictedComponentCounts {11} = (4, 4, 5) := by
  norm_num [wheelFactors, predictedComponentCounts]

theorem boundary_wheel_Q77 :
    wheelFactors {7, 11} = (45, 21, 5) ∧
      predictedComponentCounts {7, 11} = (56, 32, 5) := by
  norm_num [wheelFactors, predictedComponentCounts]

theorem boundary_wheel_Q91 :
    wheelFactors {7, 13} = (55, 27, 7) ∧
      predictedComponentCounts {7, 13} = (64, 40, 7) := by
  norm_num [wheelFactors, predictedComponentCounts]

end Brockian.SieveSpectrumCounts
