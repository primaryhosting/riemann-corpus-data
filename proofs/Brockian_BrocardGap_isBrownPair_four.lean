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

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`; the only known ones are the
*Brown pairs* `(4, 5)`, `(5, 11)`, `(7, 71)`, and Brocard's conjecture (still open) states that
there are no further solutions.

This file develops the *gap* side of the problem, i.e. how far apart the perfect squares
surrounding `n ! + 1` are, and records what can be proved unconditionally:

* `Brockian.BrocardGap.BrocardGapConjecture` : for `n ≥ 10` the two consecutive squares
  bracketing `n ! + 1` are more than `2 ^ (n + 1)` apart;
* `Brockian.BrocardGap.unique_sq_near_factorial` : consequently, for `n ≥ 10` at most one
  natural number has its square within `2 ^ n` of `n ! + 1`;
* `Brockian.BrocardGap.no_brownPair_of_mem_Icc_eight_hundred` : an unconditional verification
  that there is no Brown pair with `8 ≤ n ≤ 100`;
* `Brockian.BrocardGap.two_pow_lt_of_brownPair` : any solution with `n ≥ 10` has `2 ^ n < m`;
* `Brockian.BrocardGap.brownPair_eq_sqrt`, `brownPair_factorization`, `brownPair_odd` :
  elementary structure of a solution;
* `Brockian.BrocardGap.brocardConjecture_iff_no_square` : a reformulation of the full
  (open) Brocard conjecture as the statement that `n ! + 1` is never a perfect square
  for `n ≥ 8`.
-/

open scoped Nat

namespace Brockian.BrocardGap

/-- A *Brown pair* is a pair `(n, m)` solving Brocard's equation `n ! + 1 = m ^ 2`. -/
def IsBrownPair (n m : ℕ) : Prop := n ! + 1 = m ^ 2

theorem isBrownPair_four : IsBrownPair 4 5 := by
  unfold IsBrownPair; norm_num [Nat.factorial]

theorem isBrownPair_five : IsBrownPair 5 11 := by
  unfold IsBrownPair; norm_num [Nat.factorial]

theorem isBrownPair_seven : IsBrownPair 7 71 := by
  unfold IsBrownPair; norm_num [Nat.factorial]

/-- Brocard's conjecture: `(4, 5)`, `(5, 11)` and `(7, 71)` are the only Brown pairs, i.e.
there is no solution of `n ! + 1 = m ^ 2` with `n ≥ 8`.  This is an open problem; the
statement is only *defined* here, never asserted. -/
def BrocardConjecture : Prop := ∀ n m : ℕ, 8 ≤ n → ¬ IsBrownPair n m

/-- Brocard's conjecture is exactly the statement that `n ! + 1` is not a perfect square
for `n ≥ 8`. -/
theorem brocardConjecture_iff_no_square :
    BrocardConjecture ↔ ∀ n : ℕ, 8 ≤ n → ¬ ∃ k : ℕ, n ! + 1 = k ^ 2 := by
  constructor
  · rintro h n hn ⟨k, hk⟩
    exact h n k hn hk
  · intro h n m hn hm
    exact h n hn ⟨m, hm⟩

/-! ### Elementary structure of a Brown pair -/

/-- The square root in a Brown pair is positive. -/
theorem brownPair_pos (n m : ℕ) (h : IsBrownPair n m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [IsBrownPair] at h
  · exact hm

/-- In a Brown pair, `m` is forced to be `⌊√(n ! + 1)⌋`; in particular `m` is unique given `n`. -/
theorem brownPair_eq_sqrt (n m : ℕ) (h : IsBrownPair n m) : m = Nat.sqrt (n ! + 1) := by
  rw [show n ! + 1 = m ^ 2 from h, Nat.sqrt_eq']

/-- A Brown pair factors the factorial: `n ! = (m - 1) * (m + 1)`. -/
theorem brownPair_factorization (n m : ℕ) (h : IsBrownPair n m) : n ! = (m - 1) * (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := brownPair_pos n m h; omega⟩
  have h' : n ! + 1 = (k + 1) ^ 2 := h
  simp only [Nat.add_sub_cancel]
  nlinarith [h']

/-- For `n ≥ 2` the square root in a Brown pair is odd. -/
theorem brownPair_odd (n m : ℕ) (hn : 2 ≤ n) (h : IsBrownPair n m) : Odd m := by
  have hdvd : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  rcases Nat.even_or_odd m with he | ho
  · exfalso
    obtain ⟨t, ht⟩ := hdvd
    obtain ⟨s, rfl⟩ := he
    have h' : n ! + 1 = (s + s) ^ 2 := h
    have hsq : (s + s) ^ 2 = 2 * (2 * s * s) := by ring
    omega
  · exact ho

/-! ### Growth of the factorial -/

/-- For `n ≥ 10` we have `2 * 4 ^ n ≤ n !`. -/
theorem two_mul_four_pow_le_factorial (n : ℕ) (hn : 10 ≤ n) : 2 * 4 ^ n ≤ n ! := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 10 with hk | hk
    · have hk10 : k = 9 := by omega
      subst hk10
      norm_num [Nat.factorial]
    · have h := ih (by omega)
      calc 2 * 4 ^ (k + 1) = 4 * (2 * 4 ^ k) := by ring
        _ ≤ 4 * k ! := Nat.mul_le_mul_left 4 h
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul_right _ (by omega)
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- For `n ≥ 10`, `2 ^ n ≤ ⌊√(n ! + 1)⌋`. -/
theorem two_pow_le_sqrt_factorial (n : ℕ) (hn : 10 ≤ n) : 2 ^ n ≤ Nat.sqrt (n ! + 1) := by
  have h4 : ((2 : ℕ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h := two_mul_four_pow_le_factorial n hn
  exact Nat.le_sqrt'.2 (by omega)

/-- Any Brown pair with `n ≥ 10` has an exponentially large square root: `2 ^ n < m`. -/
theorem two_pow_lt_of_brownPair (n m : ℕ) (hn : 10 ≤ n) (h : IsBrownPair n m) : 2 ^ n < m := by
  have hfac := two_mul_four_pow_le_factorial n hn
  have h4 : ((2 : ℕ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h' : n ! + 1 = m ^ 2 := h
  have hlt : ((2 : ℕ) ^ n) ^ 2 < m ^ 2 := by omega
  exact lt_of_pow_lt_pow_left' 2 hlt

/-! ### The gap between the squares surrounding `n ! + 1` -/

/-- **Brocard Gap Conjecture (gap form).**
For `n ≥ 10`, the two consecutive perfect squares bracketing `n ! + 1`, namely `m ^ 2` and
`(m + 1) ^ 2` for `m = ⌊√(n ! + 1)⌋`, are more than `2 ^ (n + 1)` apart: Brocard's quantity
`n ! + 1` lies in a region where perfect squares are exponentially sparse. -/
theorem BrocardGapConjecture (n : ℕ) (hn : 10 ≤ n) :
    2 ^ (n + 1) < (Nat.sqrt (n ! + 1) + 1) ^ 2 - Nat.sqrt (n ! + 1) ^ 2 := by
  have h := two_pow_le_sqrt_factorial n hn
  set m := Nat.sqrt (n ! + 1) with hm
  have hexp : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
  have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  omega

/-- **Uniqueness of a near square.** For `n ≥ 10` there is at most one natural number `m` whose
square lies within `2 ^ n` of `n ! + 1`. -/
theorem unique_sq_near_factorial (n : ℕ) (hn : 10 ≤ n) (m₁ m₂ : ℕ)
    (h₁ : |(n ! : ℤ) + 1 - (m₁ : ℤ) ^ 2| ≤ 2 ^ n)
    (h₂ : |(n ! : ℤ) + 1 - (m₂ : ℤ) ^ 2| ≤ 2 ^ n) : m₁ = m₂ := by
  have hfac : (2 : ℤ) * 4 ^ n ≤ (n ! : ℤ) := by
    exact_mod_cast two_mul_four_pow_le_factorial n hn
  have hsq : (2 : ℤ) ^ n * 2 ^ n = 4 ^ n := by
    rw [← mul_pow]; norm_num
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  have hle : (2 : ℤ) ^ n ≤ 4 ^ n := by gcongr; norm_num
  have key : ∀ m : ℕ, |(n ! : ℤ) + 1 - (m : ℤ) ^ 2| ≤ 2 ^ n → (2 : ℤ) ^ n < (m : ℤ) := by
    intro m hm
    have hlow : (n ! : ℤ) + 1 - 2 ^ n ≤ (m : ℤ) ^ 2 := by
      have := (abs_le.1 hm).2; linarith
    by_contra hcon
    push_neg at hcon
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    nlinarith [hlow, hsq, hcon, hm0, hle, hfac]
  have k₁ := key m₁ h₁
  have k₂ := key m₂ h₂
  by_contra hne
  rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
  · have hstep : ((m₁ : ℤ) + 1) ≤ (m₂ : ℤ) := by exact_mod_cast hlt
    have hb₁ : (n ! : ℤ) + 1 - 2 ^ n ≤ (m₁ : ℤ) ^ 2 := by
      have := (abs_le.1 h₁).2; linarith
    have hb₂ : (m₂ : ℤ) ^ 2 ≤ (n ! : ℤ) + 1 + 2 ^ n := by
      have := (abs_le.1 h₂).1; linarith
    nlinarith [hstep, hb₁, hb₂, k₁, hpos]
  · have hlt : m₂ < m₁ := by omega
    have hstep : ((m₂ : ℤ) + 1) ≤ (m₁ : ℤ) := by exact_mod_cast hlt
    have hb₂ : (n ! : ℤ) + 1 - 2 ^ n ≤ (m₂ : ℤ) ^ 2 := by
      have := (abs_le.1 h₂).2; linarith
    have hb₁ : (m₁ : ℤ) ^ 2 ≤ (n ! : ℤ) + 1 + 2 ^ n := by
      have := (abs_le.1 h₁).1; linarith
    nlinarith [hstep, hb₁, hb₂, k₂, hpos]

/-! ### An unconditional finite verification -/

/-- A number strictly between two consecutive squares is not a square. -/
theorem not_isSquare_of_between (X m : ℕ) (h1 : m ^ 2 < X) (h2 : X < (m + 1) ^ 2) :
    ¬ ∃ k : ℕ, X = k ^ 2 := by
  rintro ⟨k, rfl⟩
  have hk : m < k := by nlinarith
  have h3 : m + 1 ≤ k := hk
  nlinarith

/-- There is no Brown pair `(n, m)` with `8 ≤ n ≤ 100`: Brocard's equation has no solution in
that range. -/
theorem no_brownPair_of_mem_Icc_eight_hundred (n m : ℕ) (h8 : 8 ≤ n) (h100 : n ≤ 100) :
    ¬ IsBrownPair n m := by
  intro h
  have hex : ∃ k : ℕ, n ! + 1 = k ^ 2 := ⟨m, h⟩
  interval_cases n
  · exact not_isSquare_of_between _ 200 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 602 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1904 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 6317 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 21886 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 78911 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 295259 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1143535 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 4574143 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 18859677 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 80014834 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 348776576 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1559776268 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 7147792818 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 33526120082 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 160785623545 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 787685471322 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 3938427356614 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 20082117944245 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 104349745809073 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 552166953567228 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 2973510046012910 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 16286585271694955 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 90679869067935485 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 512962802680363491 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 2946746955341073478 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 17182339742875652406 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 101652092779175702171 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 609912556675054213027 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 3709953246501409085690 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 22869687743093501007951 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 142821154179615294686593 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 903280290523322408635610 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 5783815921445270815783609 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 37483411234209726053065805 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 245795164849461258960674062 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1630420674178430788228519563 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 10937194378152021970306618007 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 74179661362209580727623742159 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 508550136674023695658451670185 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 3523338699662022653505900576721 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 24663370897634158574541304037050 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 174396368086360611696209329639024 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1245439180886558699493562057691804 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 8980989654316715588967781706572076 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 65382591597917144387816492317568177 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 480461962427038942460267525096444474 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 3563201278858419461033351267854721464 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 26664556771205919519070097139612996000 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 201312988912482288333668455069536465757 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1533154046820761769413164705689608744377 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 11776379687564843276211019969710858039009 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 91219444817107882594696857529818207676198 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 712446639319201784948673912308403605115342 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 5609810447812647575362248801595614968784558 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 44526490041372451122965980435912297622389065 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 356211920330979608983727843487298380979112523 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 2871872314724746021942727901945240734448707786 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 23331200978034608323876057832648816217523382535 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 190974110596668796970008672429388554580114244205 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1574812859496908794403637793960093262759360945119 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 13081378078327271990661335578798848847474255303826 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 109446661301155695857080695109221322834464193656741 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 922213960297642814598347871007016379244405330655250 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 7825244940376376925358096892704591704511772131306815 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 66858922078602825324590583356376523422703411874063526 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 575142194723999224356836312510183507170717503745407529 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 4980877514193196669713282991946078429827937232372941867 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 43422283469044442400520987277954690033900570230313299933 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 381028991060110634246276414878912279469899189376847948137 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 3365156932181068109459677272856044111292549448241189337343 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 29910169058002623210200515287548862104836069367192860122492 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 267524684928818862621490012042605003730753817304274266583374 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 2407722164359369763593410108383445033576784355738468399250368 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 21802851503903891305843592056331800458090082265244558375673041 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 198633430462262788036763464177703883166690275063913206990548481 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1820505461284132832359203813645046756110583331925714370170257092 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 16784231035053557904028966906346483792025484094796637394973403970 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 155650555359345674201535001388480503193835670087005087695666582899 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1451811729660401840498379775717372701145990271033308799231637667601 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 13619201234191322393627253212934023042404388731461906952430812397994 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 128483287477042947436606854413089420338280480054241478815100633956558 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1218899489080933816973227253068021382231629321448981884930371490328689 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 11627560052213890684239693812535151882288553865765313903995958273943586 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 111527638075238136262755547542307772029800712447380847367329167783382104 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 1075533591796017115343430456551200439746548977577162936545074776552498754 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 10427685057848376925507942191442630012584828624363222101172323570579332599 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 101636501751285493870798488028947073709983082260934656117721845292980988580 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 995830274128553338795685900500337369492022050359737013283228306377142743139 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 9807790764615756210934052418079289148346460527555220609613824741800936687334 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 97092175013660332284448160034192795594426266264944604365617979012105653222056 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 966054943799492973133000870362309068674974070396662776244736194062917963496762 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex
  · exact not_isSquare_of_between _ 9660549437994929731330008703623090686749740703966627762447361940629179634967623 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) hex

end Brockian.BrocardGap

