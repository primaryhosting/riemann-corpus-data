import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

set_option grind.warning false

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/
theorem classical_query_lower_bound_rpow {n q : ℕ} (A : QueryAlg n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (q : ℝ) + 2 := by
  have h := classical_query_lower_bound A hA
  have h' : ((2:ℝ)) ^ (n : ℕ) ≤ ((q : ℝ) + 2) ^ 2 := by exact_mod_cast h
  have ha : (0:ℝ) ≤ (2:ℝ) ^ ((n : ℝ) / 2) := by positivity
  have hb : (0:ℝ) ≤ (q : ℝ) + 2 := by positivity
  have hsq : ((2:ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2:ℝ) ^ (n : ℕ) := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0), Real.rpow_natCast]
  nlinarith [h', ha, hb, hsq]

/-- **Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries.**

1. *(quantum, one query per round)* For every instance `f` with hidden shift `s`:
   * a single query produces a measurement outcome that is uniformly distributed
     on the hyperplane orthogonal to `s`;
   * the outcomes of `2 * n` independent rounds form a probability distribution,
     and the probability that they fail to determine `s` is at most `2 ^ (-n)`;
     so `2 * n = O(n)` queries suffice.
2. *(classical)* Every deterministic classical algorithm which always outputs the
   hidden shift using `q` queries satisfies `2 ^ (n / 2) ≤ q + 2`, i.e. it needs
   `Ω(2 ^ (n / 2))` queries. -/
theorem simon_algorithm :
    (∀ (n : ℕ) (f : BV n → BV n) (s : BV n), IsSimon f s →
        (∀ y : BV n, prob f y = if ip y s = 0 then 2 / 2 ^ n else 0) ∧
        (∑ Y : Fin (2 * n) → BV n, ∏ i, prob f (Y i)) = 1 ∧
        failProb f s (2 * n) ≤ 1 / 2 ^ n) ∧
    (∀ (n q : ℕ) (A : QueryAlg n),
        (∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) →
        (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (q : ℝ) + 2) := by
  refine ⟨fun n f s hf =>
      ⟨fun y => prob_eq hf y, sum_prod_prob_eq_one hf (2 * n), quantum_simon_success hf⟩,
    fun _ _ A hA => classical_query_lower_bound_rpow A hA⟩

end QI

import RequestProject.Simon.Basic

/-!
# Simon's problem: the quantum subroutine

One round of Simon's algorithm uses a *single* query to the oracle for `f`:

* prepare `2^(-n/2) ∑ₓ |x⟩|0⟩` and query the oracle, giving
  `unifState f = 2^(-n/2) ∑ₓ |x⟩|f x⟩`;
* apply the Hadamard transform to the first register, giving `simonState f`;
* measure the first register.

The main result `QI.prob_eq` computes the resulting distribution: the outcome is
uniformly distributed on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to the
hidden shift `s`.
-/

namespace QI

variable {n : ℕ}

/-- The state `2^(-n/2) ∑ₓ |x⟩|f x⟩` obtained from `|0⟩|0⟩` by Hadamards on the
first register followed by one oracle query. -/
noncomputable def unifState (f : BV n → BV n) (p : BV n × BV n) : ℂ :=
  if p.2 = f p.1 then ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ else 0

/-- The Hadamard transform applied to the first register. -/
noncomputable def hadamard1 (psi : BV n × BV n → ℂ) (p : BV n × BV n) : ℂ :=
  ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ∑ x : BV n, (chi (ip x p.1) : ℂ) * psi (x, p.2)

/-- The state of Simon's algorithm just before the measurement. -/
noncomputable def simonState (f : BV n → BV n) : BV n × BV n → ℂ :=
  hadamard1 (unifState f)

/-- The real number `∑_{x ∈ f⁻¹(w)} (-1)^⟪x,y⟫`. -/
def fibreSum (f : BV n → BV n) (y w : BV n) : ℝ :=
  ∑ x : BV n, if f x = w then chi (ip x y) else 0

/-- The probability of measuring `y` in the first register. -/
noncomputable def prob (f : BV n → BV n) (y : BV n) : ℝ :=
  ∑ w : BV n, ‖simonState f (y, w)‖ ^ 2

lemma sqrt_two_pow_inv_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ))⁻¹ * ((Real.sqrt (2 ^ n) : ℝ))⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 ^ n)]

lemma simonState_eq (f : BV n → BV n) (y w : BV n) :
    simonState f (y, w) = (((2 : ℝ) ^ n)⁻¹ * fibreSum f y w : ℝ) := by
  have hcast : ((fibreSum f y w : ℝ) : ℂ)
      = ∑ x : BV n, (if f x = w then (chi (ip x y) : ℂ) else 0) := by
    rw [fibreSum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => by split <;> simp
  have key : ∀ x : BV n,
      (chi (ip x y) : ℂ) * (if w = f x then ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ)⁻¹ else 0)
        = ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ)⁻¹ * (if f x = w then (chi (ip x y) : ℂ) else 0) := by
    intro x
    by_cases h : f x = w
    · simp [h, mul_comm]
    · simp [h, Ne.symm h]
  rw [Complex.ofReal_mul, hcast]
  simp only [simonState, hadamard1, unifState]
  rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.mul_sum, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, sqrt_two_pow_inv_sq n]

lemma prob_eq_sum_sq (f : BV n → BV n) (y : BV n) :
    prob f y = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ∑ w : BV n, (fibreSum f y w) ^ 2 := by
  simp only [prob, simonState_eq, Complex.norm_real, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  ring

/-- Expanding the square of a fibre sum as a double sum over pairs with equal
`f`-value. -/
lemma sum_fibreSum_sq (f : BV n → BV n) (y : BV n) :
    ∑ w : BV n, (fibreSum f y w) ^ 2 =
      ∑ x : BV n, ∑ x' : BV n, if f x = f x' then chi (ip x y) * chi (ip x' y) else 0 := by
  have inner : ∀ x x' : BV n,
      ∑ w : BV n, (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0)
        = if f x = f x' then chi (ip x y) * chi (ip x' y) else 0 := by
    intro x x'
    have hstep : ∀ w : BV n,
        (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0)
          = if f x = w then (if f x' = w then chi (ip x y) * chi (ip x' y) else 0) else 0 := by
      intro w; split <;> simp
    simp_rw [hstep]
    rw [Finset.sum_ite_eq Finset.univ (f x)
      (fun w => if f x' = w then chi (ip x y) * chi (ip x' y) else 0)]
    simp [eq_comm]
  calc ∑ w : BV n, (fibreSum f y w) ^ 2
      = ∑ w : BV n, ∑ x : BV n, ∑ x' : BV n,
          (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [sq, fibreSum, Finset.sum_mul_sum]
    _ = ∑ x : BV n, ∑ x' : BV n, ∑ w : BV n,
          (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => inner x x'

/-- For a Simon function, the fibre of `x` is the pair `{x, x + s}`. -/
lemma filter_fibre {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) (x : BV n) :
    (Finset.univ.filter fun x' => f x = f x') = {x, x + s} := by
  ext x'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact hf.2 x x'

/-- **The measurement distribution of Simon's subroutine.**  For a function
satisfying Simon's promise with hidden shift `s`, one quantum query produces a
uniformly random element of the hyperplane orthogonal to `s`. -/
theorem prob_eq {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) (y : BV n) :
    prob f y = if ip y s = 0 then 2 / 2 ^ n else 0 := by
  have hxs : ∀ x : BV n, x ≠ x + s := by
    intro x h
    apply hf.1
    have : x + 0 = x + s := by simpa using h
    exact (add_left_cancel this).symm
  have inner : ∀ x : BV n,
      (∑ x' : BV n, if f x = f x' then chi (ip x y) * chi (ip x' y) else 0)
        = 1 + chi (ip s y) := by
    intro x
    rw [← Finset.sum_filter, filter_fibre hf x,
      Finset.sum_pair (hxs x), chi_mul_self]
    rw [ip_add_left, chi_add, ← mul_assoc, chi_mul_self, one_mul]
  have hsum : ∑ w : BV n, (fibreSum f y w) ^ 2 = 2 ^ n * (1 + chi (ip s y)) := by
    rw [sum_fibreSum_sq]
    simp_rw [inner]
    rw [Finset.sum_const, Finset.card_univ, card_bv, nsmul_eq_mul]
    push_cast
    ring
  rw [prob_eq_sum_sq, hsum]
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rcases zmod_two_cases (ip y s) with h | h
  · rw [if_pos h, ip_comm s y, h, show chi 0 = 1 from by rw [chi, if_pos rfl]]
    field_simp
    ring
  · rw [if_neg (by rw [h]; decide), ip_comm s y, h,
      show chi 1 = -1 from by rw [chi, if_neg (by decide)]]
    ring

end QI

import Mathlib

/-!
# Simon's problem: basic definitions

We work with the `𝔽₂`-vector space `BV n = Fin n → ZMod 2` of `n`-bit strings,
equipped with the standard bilinear form `ip x y = ∑ i, x i * y i`.

A function `f : BV n → BV n` *satisfies the Simon promise with hidden shift `s`*
(`IsSimon f s`) when `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`; i.e. `f` is
two-to-one and its fibres are the cosets of the subgroup `{0, s}`.
-/

namespace QI

/-- `n`-bit strings, viewed as a vector space over `𝔽₂`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The standard bilinear form on `BV n`. -/
def ip {n : ℕ} (x y : BV n) : ZMod 2 := ∑ i, x i * y i

/-- The character `(-1)^b` of `ZMod 2`, valued in `ℝ`. -/
def chi (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

/-- `f` satisfies Simon's promise with hidden shift `s`. -/
def IsSimon {n : ℕ} (f : BV n → BV n) (s : BV n) : Prop :=
  s ≠ 0 ∧ ∀ x y, f x = f y ↔ (y = x ∨ y = x + s)

section
variable {n : ℕ}

lemma card_bv (n : ℕ) : Fintype.card (BV n) = 2 ^ n := by
  simp [BV]

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

@[simp] lemma bv_add_self (x : BV n) : x + x = 0 := by
  funext i
  simpa using zmod_two_add_self (x i)

lemma bv_add_left_cancel_self (x y : BV n) : x + (x + y) = y := by
  rw [← add_assoc, bv_add_self, zero_add]

lemma ip_comm (x y : BV n) : ip x y = ip y x := by
  simp only [ip]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma ip_add_left (x y z : BV n) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [add_mul]

lemma ip_add_right (x y z : BV n) : ip x (y + z) = ip x y + ip x z := by
  rw [ip_comm, ip_add_left, ip_comm y x, ip_comm z x]

@[simp] lemma ip_zero_left (x : BV n) : ip 0 x = 0 := by simp [ip]

@[simp] lemma ip_zero_right (x : BV n) : ip x 0 = 0 := by simp [ip]

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod_two_cases a with ha | ha <;> rcases zmod_two_cases b with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [chi, show (1 : ZMod 2) + 1 = 0 from by decide, show (1 : ZMod 2) ≠ 0 from by decide]

lemma chi_mul_self (a : ZMod 2) : chi a * chi a = 1 := by
  rcases zmod_two_cases a with ha | ha <;> subst ha <;> norm_num [chi]

lemma chi_eq_one_iff (a : ZMod 2) : chi a = 1 ↔ a = 0 := by
  rcases zmod_two_cases a with ha | ha <;> subst ha <;> norm_num [chi]

/-- The `i`-th standard basis vector of `BV n`. -/
def e {n : ℕ} (i : Fin n) : BV n := fun j => if j = i then 1 else 0

lemma ip_e_left (i : Fin n) (x : BV n) : ip (e i) x = x i := by
  simp [ip, e, Finset.sum_ite_eq' Finset.univ i x]

lemma ip_e_right (i : Fin n) (x : BV n) : ip x (e i) = x i := by
  rw [ip_comm, ip_e_left]

lemma exists_ne_zero_coord {x : BV n} (hx : x ≠ 0) : ∃ i, x i = 1 := by
  by_contra h
  push_neg at h
  apply hx
  funext i
  rcases zmod_two_cases (x i) with h0 | h1
  · simpa using h0
  · exact absurd h1 (h i)

/-- If `s ≠ 0` there is a vector pairing to `1` with `s`. -/
lemma exists_ip_eq_one {s : BV n} (hs : s ≠ 0) : ∃ y : BV n, ip y s = 1 := by
  obtain ⟨i, hi⟩ := exists_ne_zero_coord hs
  exact ⟨e i, by rw [ip_e_left, hi]⟩

/-- Key nondegeneracy fact: if `s ≠ 0`, `t ≠ 0` and `t ≠ s`, then some vector
orthogonal to `s` pairs to `1` with `t`. -/
lemma exists_ip_zero_ip_one {s t : BV n} (ht : t ≠ 0) (hst : t ≠ s) :
    ∃ y : BV n, ip y s = 0 ∧ ip y t = 1 := by
  have hne : ∃ i, s i ≠ t i := by
    by_contra h
    push_neg at h
    exact hst (funext fun i => (h i).symm)
  obtain ⟨i, hi⟩ := hne
  rcases zmod_two_cases (s i) with h0 | h1
  · -- s i = 0, hence t i = 1
    have hti : t i = 1 := by
      rcases zmod_two_cases (t i) with h | h
      · exact absurd (h0.trans h.symm) hi
      · exact h
    exact ⟨e i, by rw [ip_e_left, h0], by rw [ip_e_left, hti]⟩
  · -- s i = 1, hence t i = 0
    have hti : t i = 0 := by
      rcases zmod_two_cases (t i) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hi
    obtain ⟨j, hj⟩ := exists_ne_zero_coord ht
    refine ⟨e j + s j • e i, ?_, ?_⟩
    · rw [ip_add_left, ip_e_left]
      have : ip (s j • e i) s = s j * s i := by
        simp [ip, e, Finset.sum_ite_eq' Finset.univ i]
      rw [this, h1, mul_one, zmod_two_add_self]
    · rw [ip_add_left, ip_e_left]
      have : ip (s j • e i) t = s j * t i := by
        simp [ip, e, Finset.sum_ite_eq' Finset.univ i]
      rw [this, hti, mul_zero, add_zero, hj]

end

end QI

import RequestProject.Simon.Quantum

/-!
# Simon's problem: `O(n)` quantum queries suffice

Each run of the quantum subroutine costs one query and returns a uniformly
random element of the hyperplane `orth s = {y | ⟪y, s⟫ = 0}` (`QI.prob_eq`).

After `m` runs, the classical post-processing solves the linear system
`⟪y i, t⟫ = 0` and outputs the unique nonzero solution, which succeeds exactly
when the sample tuple `Y` *determines* `s` (`QI.Determines`).  The main estimate
`QI.failProb_le` bounds the probability of failure by `2 ^ n / 2 ^ m`; with
`m = 2 * n` queries the failure probability is at most `2 ^ (-n)`
(`QI.quantum_simon_success`).
-/

namespace QI

variable {n : ℕ}

/-- The hyperplane orthogonal to `s`. -/
def orth (s : BV n) : Finset (BV n) := Finset.univ.filter (fun y => ip y s = 0)

@[simp] lemma mem_orth {s y : BV n} : y ∈ orth s ↔ ip y s = 0 := by simp [orth]

/-- A tuple of measurement outcomes *determines* `s` if `s` is the only nonzero
vector orthogonal to all of them (so that solving the linear system reveals `s`). -/
def Determines {m : ℕ} (Y : Fin m → BV n) (s : BV n) : Prop :=
  ∀ t : BV n, t ≠ 0 → (∀ i, ip (Y i) t = 0) → t = s

instance decidableDetermines {m : ℕ} (Y : Fin m → BV n) (s : BV n) :
    Decidable (Determines Y s) := by
  unfold Determines
  infer_instance

/-- Halving lemma: a nonzero linear functional `⟪·, t⟫` splits a set closed
under translation by a vector `y₀` with `⟪y₀, t⟫ = 1` into two halves. -/
lemma card_filter_half (W : Finset (BV n)) (t y₀ : BV n) (hy₀ : ip y₀ t = 1)
    (hW : ∀ y ∈ W, y + y₀ ∈ W) :
    2 * (W.filter (fun y => ip y t = 0)).card = W.card := by
  classical
  have hswap : (W.filter (fun y => ip y t = 0)).card
      = (W.filter (fun y => ¬ ip y t = 0)).card := by
    refine Finset.card_bij' (fun y _ => y + y₀) (fun y _ => y + y₀) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨hW a ha.1, ?_⟩
      rw [ip_add_left, ha.2, hy₀, zero_add]
      decide
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨hW a ha.1, ?_⟩
      have h1 : ip a t = 1 := by
        rcases zmod_two_cases (ip a t) with h | h
        · exact absurd h ha.2
        · exact h
      rw [ip_add_left, h1, hy₀]
      decide
    · intro a _
      show a + y₀ + y₀ = a
      rw [add_assoc, bv_add_self, add_zero]
    · intro a _
      show a + y₀ + y₀ = a
      rw [add_assoc, bv_add_self, add_zero]
  have := Finset.card_filter_add_card_filter_not (s := W) (fun y => ip y t = 0)
  omega

lemma card_orth {s : BV n} (hs : s ≠ 0) : 2 * (orth s).card = 2 ^ n := by
  obtain ⟨y₀, hy₀⟩ := exists_ip_eq_one hs
  have h := card_filter_half (Finset.univ : Finset (BV n)) s y₀ hy₀ (by simp)
  rw [Finset.card_univ, card_bv] at h
  exact h

lemma card_orth_pos {s : BV n} (hs : s ≠ 0) : 0 < (orth s).card := by
  have h := card_orth hs
  have : (0:ℕ) < 2 ^ n := Nat.two_pow_pos n
  omega

lemma card_orth_filter {s t : BV n} (ht : t ≠ 0) (hts : t ≠ s) :
    2 * ((orth s).filter (fun y => ip y t = 0)).card = (orth s).card := by
  obtain ⟨y₀, h0, h1⟩ := exists_ip_zero_ip_one ht hts
  refine card_filter_half (orth s) t y₀ h1 ?_
  intro y hy
  rw [mem_orth] at hy ⊢
  rw [ip_add_left, hy, h0, add_zero]

/-- `Determines Y s` says exactly that the solution set of the linear system
`⟪Y i, t⟫ = 0` is `{0, s}`, so classical Gaussian elimination on the measured
outcomes recovers the hidden shift `s`. -/
lemma determines_iff {m : ℕ} {s : BV n} (Y : Fin m → BV n) (hY : ∀ i, Y i ∈ orth s) :
    Determines Y s ↔ ∀ t : BV n, (∀ i, ip (Y i) t = 0) ↔ (t = 0 ∨ t = s) := by
  constructor
  · intro hd t
    constructor
    · intro hort
      by_cases h0 : t = 0
      · exact Or.inl h0
      · exact Or.inr (hd t h0 hort)
    · rintro (rfl | rfl)
      · intro i; simp
      · intro i
        rw [← mem_orth]
        exact hY i
  · intro h t ht0 hort
    rcases (h t).1 hort with h1 | h1
    · exact absurd h1 ht0
    · exact h1

/-! ### Counting the bad sample tuples -/

/-- Sample tuples that fail to determine `s`. -/
noncomputable def badTuples (s : BV n) (m : ℕ) : Finset (Fin m → BV n) :=
  (Fintype.piFinset fun _ => orth s).filter (fun Y => ¬ Determines Y s)

lemma badTuples_subset (s : BV n) (m : ℕ) :
    badTuples s m ⊆ (Finset.univ.filter (fun t : BV n => t ≠ 0 ∧ t ≠ s)).biUnion
      (fun t => Fintype.piFinset fun _ => (orth s).filter (fun y => ip y t = 0)) := by
  classical
  intro Y hY
  rw [badTuples, Finset.mem_filter, Fintype.mem_piFinset] at hY
  obtain ⟨hmem, hnd⟩ := hY
  rw [Determines] at hnd
  push_neg at hnd
  obtain ⟨t, ht0, hort, hts⟩ := hnd
  refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
  · simp [ht0, hts]
  · exact Fintype.mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨hmem i, hort i⟩

/-- The number of bad tuples is at most `2 ^ n / 2 ^ m` times the total number
of sample tuples. -/
theorem card_badTuples_le (s : BV n) (m : ℕ) :
    2 ^ m * (badTuples s m).card ≤ 2 ^ n * (orth s).card ^ m := by
  classical
  set T : Finset (BV n) := Finset.univ.filter (fun t : BV n => t ≠ 0 ∧ t ≠ s) with hT
  have hsub := badTuples_subset s m
  have hcard : (badTuples s m).card
      ≤ ∑ t ∈ T, ((orth s).filter (fun y => ip y t = 0)).card ^ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Fintype.card_piFinset_const]
  have hterm : ∀ t ∈ T, 2 ^ m * ((orth s).filter (fun y => ip y t = 0)).card ^ m
      = (orth s).card ^ m := by
    intro t htT
    have ht : t ≠ 0 ∧ t ≠ s := by
      have := Finset.mem_filter.1 htT
      exact this.2
    have h2 := card_orth_filter ht.1 ht.2
    calc 2 ^ m * ((orth s).filter (fun y => ip y t = 0)).card ^ m
        = (2 * ((orth s).filter (fun y => ip y t = 0)).card) ^ m := by
          rw [Nat.mul_pow]
      _ = (orth s).card ^ m := by rw [h2]
  calc 2 ^ m * (badTuples s m).card
      ≤ 2 ^ m * ∑ t ∈ T, ((orth s).filter (fun y => ip y t = 0)).card ^ m :=
        Nat.mul_le_mul_left _ hcard
    _ = ∑ t ∈ T, 2 ^ m * ((orth s).filter (fun y => ip y t = 0)).card ^ m := by
        rw [Finset.mul_sum]
    _ = ∑ _t ∈ T, (orth s).card ^ m := Finset.sum_congr rfl hterm
    _ = T.card * (orth s).card ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (orth s).card ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        calc T.card ≤ (Finset.univ : Finset (BV n)).card := Finset.card_le_card (by simp [hT])
          _ = 2 ^ n := by rw [Finset.card_univ, card_bv]

/-! ### The failure probability of Simon's algorithm -/

/-- The probability that the outcomes of `m` independent runs of the quantum
subroutine fail to determine the hidden shift. -/
noncomputable def failProb (f : BV n → BV n) (s : BV n) (m : ℕ) : ℝ :=
  ∑ Y ∈ Finset.univ.filter (fun Y : Fin m → BV n => ¬ Determines Y s), ∏ i, prob f (Y i)

lemma prob_of_mem_orth {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) {y : BV n}
    (hy : y ∈ orth s) : prob f y = ((orth s).card : ℝ)⁻¹ := by
  rw [prob_eq hf, if_pos (mem_orth.1 hy)]
  have h := card_orth hf.1
  have hc : ((orth s).card : ℝ) * 2 = 2 ^ n := by
    have h' : ((2 * (orth s).card : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  have hpos : (0:ℝ) < (orth s).card := by
    exact_mod_cast card_orth_pos hf.1
  field_simp
  linarith [hc]

lemma prob_of_not_mem_orth {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) {y : BV n}
    (hy : y ∉ orth s) : prob f y = 0 := by
  rw [prob_eq hf, if_neg]
  simpa using hy

/-- The distribution of the measurement outcomes of `m` independent runs is a
probability distribution. -/
theorem sum_prod_prob_eq_one {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) (m : ℕ) :
    ∑ Y : Fin m → BV n, ∏ i, prob f (Y i) = 1 := by
  classical
  have hone : ∑ y : BV n, prob f y = 1 := by
    have hsplit : ∑ y : BV n, prob f y = ∑ y ∈ orth s, prob f y := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro y _ hy
      exact prob_of_not_mem_orth hf hy
    rw [hsplit]
    rw [Finset.sum_congr rfl fun y hy => prob_of_mem_orth hf hy]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : (0:ℝ) < (orth s).card := by exact_mod_cast card_orth_pos hf.1
    field_simp
  have := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (BV n)))
    (fun (_ : Fin m) (y : BV n) => prob f y)
  rw [Fintype.piFinset_univ] at this
  rw [← this, Finset.prod_congr rfl fun i _ => hone]
  simp

/-- **The failure probability of `m` rounds of Simon's algorithm is at most
`2 ^ n / 2 ^ m`.** -/
theorem failProb_le {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) (m : ℕ) :
    failProb f s m ≤ 2 ^ n / 2 ^ m := by
  classical
  have hpos : (0:ℝ) < (orth s).card := by exact_mod_cast card_orth_pos hf.1
  -- only tuples inside the hyperplane contribute
  have hsub : badTuples s m ⊆
      Finset.univ.filter (fun Y : Fin m → BV n => ¬ Determines Y s) := by
    intro Y hY
    rw [badTuples, Finset.mem_filter] at hY
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hY.2⟩
  have hzero : ∀ Y ∈ Finset.univ.filter (fun Y : Fin m → BV n => ¬ Determines Y s),
      Y ∉ badTuples s m → ∏ i, prob f (Y i) = 0 := by
    intro Y hY hYbad
    rw [badTuples, Finset.mem_filter] at hYbad
    have hnd : ¬ Determines Y s := (Finset.mem_filter.1 hY).2
    have : Y ∉ (Fintype.piFinset fun _ => orth s) := fun h => hYbad ⟨h, hnd⟩
    rw [Fintype.mem_piFinset] at this
    push_neg at this
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (prob_of_not_mem_orth hf hi)
  have hsum : failProb f s m = ∑ Y ∈ badTuples s m, ∏ i, prob f (Y i) := by
    rw [failProb]
    exact (Finset.sum_subset hsub hzero).symm
  have hval : ∀ Y ∈ badTuples s m, ∏ i, prob f (Y i) = (((orth s).card : ℝ)⁻¹) ^ m := by
    intro Y hY
    rw [badTuples, Finset.mem_filter, Fintype.mem_piFinset] at hY
    rw [Finset.prod_congr rfl fun i _ => prob_of_mem_orth hf (hY.1 i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsum, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  -- now a purely numerical estimate
  have hcount : (2:ℝ) ^ m * (badTuples s m).card ≤ 2 ^ n * ((orth s).card : ℝ) ^ m := by
    have h2 : ((2 ^ m * (badTuples s m).card : ℕ) : ℝ) ≤ ((2 ^ n * (orth s).card ^ m : ℕ) : ℝ) :=
      Nat.cast_le.2 (card_badTuples_le s m)
    push_cast at h2
    exact h2
  have h2pos : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have hne : ((orth s).card : ℝ) ≠ 0 := ne_of_gt hpos
  have key : ((badTuples s m).card : ℝ) ≤ 2 ^ n * ((orth s).card : ℝ) ^ m / 2 ^ m := by
    rw [le_div_iff₀ h2pos]
    linarith [hcount]
  have hinv : (0:ℝ) ≤ (((orth s).card : ℝ)⁻¹) ^ m := by positivity
  calc ((badTuples s m).card : ℝ) * (((orth s).card : ℝ)⁻¹) ^ m
      ≤ (2 ^ n * ((orth s).card : ℝ) ^ m / 2 ^ m) * (((orth s).card : ℝ)⁻¹) ^ m :=
        mul_le_mul_of_nonneg_right key hinv
    _ = 2 ^ n / 2 ^ m := by
        field_simp
        rw [← mul_pow]
        field_simp
        exact one_pow m

/-- **Simon's algorithm with `2 * n` quantum queries.**  For any function
satisfying Simon's promise with hidden shift `s`, running the one-query quantum
subroutine `2 * n` times produces measurement outcomes which determine `s`,
except with probability at most `2 ^ (-n)`. -/
theorem quantum_simon_success {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) :
    failProb f s (2 * n) ≤ 1 / 2 ^ n := by
  have h := failProb_le hf (2 * n)
  have hpow : (2:ℝ) ^ n / 2 ^ (2 * n) = 1 / 2 ^ n := by
    rw [two_mul, pow_add]
    field_simp
  rwa [hpow] at h

end QI

import RequestProject.Simon.Basic

/-!
# Simon's problem: the classical query lower bound

A deterministic classical query algorithm is modelled as a decision tree: it
adaptively chooses the next query point from the list of answers received so
far, and finally outputs a guess.

The main result `QI.classical_lower_bound` says: if `q * q + 3 ≤ 2 ^ n`, then no
`q`-query deterministic algorithm can solve Simon's problem, i.e. there is an
instance on which it errs.  Equivalently (`QI.classical_query_lower_bound`), a
correct algorithm needs `2 ^ n ≤ (q + 2) ^ 2` queries, i.e. `q = Ω(2 ^ (n / 2))`.
-/

namespace QI

variable {n : ℕ}

/-- A deterministic classical query algorithm: `next t` is the point queried
after having received the list of answers `t`, and `out t` is the final guess. -/
structure QueryAlg (n : ℕ) where
  /-- next query point, as a function of the answers received so far -/
  next : List (BV n) → BV n
  /-- the final output, as a function of the answers received -/
  out : List (BV n) → BV n

/-- The list of answers received after `k` queries to `f`. -/
def trace (A : QueryAlg n) (f : BV n → BV n) : ℕ → List (BV n)
  | 0 => []
  | k + 1 => trace A f k ++ [f (A.next (trace A f k))]

/-- The `k`-th query point of `A` when run on `f`. -/
def query (A : QueryAlg n) (f : BV n → BV n) (k : ℕ) : BV n := A.next (trace A f k)

/-- The output of `A` after `q` queries to `f`. -/
def result (A : QueryAlg n) (f : BV n → BV n) (q : ℕ) : BV n := A.out (trace A f q)

lemma trace_succ (A : QueryAlg n) (f : BV n → BV n) (k : ℕ) :
    trace A f (k + 1) = trace A f k ++ [f (query A f k)] := rfl

/-- Two oracles agreeing on all the query points that the algorithm asks of `f`
produce the same transcript. -/
lemma trace_congr (A : QueryAlg n) (f g : BV n → BV n) :
    ∀ k : ℕ, (∀ j < k, g (query A f j) = f (query A f j)) → trace A g k = trace A f k
  | 0, _ => rfl
  | k + 1, h => by
      have ih : trace A g k = trace A f k :=
        trace_congr A f g k fun j hj => h j (Nat.lt_succ_of_lt hj)
      have hq : query A g k = query A f k := by
        simp only [query, ih]
      rw [trace_succ, trace_succ, ih, hq, h k (Nat.lt_succ_self k)]

/-! ### Constructing Simon functions with prescribed values -/

/-- Canonical representative of the coset `{x, x + s}`, chosen using a
coordinate `i` where `s i = 1`. -/
def repOf (s : BV n) (i : Fin n) (x : BV n) : BV n := if x i = 0 then x else x + s

lemma repOf_cases (s : BV n) (i : Fin n) (x : BV n) :
    repOf s i x = x ∨ repOf s i x = x + s := by
  unfold repOf; split <;> simp

lemma repOf_add_s {s : BV n} {i : Fin n} (hs : s i = 1) (x : BV n) :
    repOf s i (x + s) = repOf s i x := by
  have hx : (x + s) i = x i + 1 := by simp [hs]
  simp only [repOf]
  rcases zmod_two_cases (x i) with h | h
  · have h1 : (x + s) i ≠ 0 := by rw [hx, h, zero_add]; decide
    rw [if_neg h1, if_pos h, add_assoc, bv_add_self, add_zero]
  · have h0 : (x + s) i = 0 := by rw [hx, h]; decide
    have h1 : ¬ (x i = 0) := by rw [h]; decide
    rw [if_pos h0, if_neg h1]

lemma repOf_eq_iff {s : BV n} {i : Fin n} (hs : s i = 1) (x y : BV n) :
    repOf s i x = repOf s i y ↔ (y = x ∨ y = x + s) := by
  constructor
  · intro h
    rcases repOf_cases s i x with hx | hx <;> rcases repOf_cases s i y with hy | hy
    · have hxy : x = y := by rw [← hx, ← hy]; exact h
      exact Or.inl hxy.symm
    · have hxy : x = y + s := by rw [← hx, ← hy]; exact h
      exact Or.inr (by rw [hxy, add_assoc, bv_add_self, add_zero])
    · have hxy : x + s = y := by rw [← hx, ← hy]; exact h
      exact Or.inr hxy.symm
    · have hxy : x + s = y + s := by rw [← hx, ← hy]; exact h
      exact Or.inl (add_right_cancel hxy).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (repOf_add_s hs x).symm

/-- **Extension lemma.**  If `s ≠ 0` and no two points of a finite set `X`
differ by `s`, then there is a function satisfying Simon's promise with hidden
shift `s` which is the identity on `X`. -/
lemma exists_isSimon_id_on {s : BV n} (hs : s ≠ 0) (X : Finset (BV n))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s) :
    ∃ f : BV n → BV n, IsSimon f s ∧ ∀ x ∈ X, f x = x := by
  classical
  obtain ⟨i, hi⟩ := exists_ne_zero_coord hs
  set r : BV n → BV n := repOf s i with hr
  -- `r` is injective on `X`
  have hinj : ∀ x ∈ X, ∀ y ∈ X, r x = r y → x = y := by
    intro x hx y hy hxy
    rcases (repOf_eq_iff hi x y).1 hxy with h | h
    · exact h.symm
    · exact absurd (by rw [h, ← add_assoc, bv_add_self, zero_add] : x + y = s) (hX x hx y hy)
  set R : Finset (BV n) := X.image r with hR
  have hmap : ∀ a : {a : BV n // a ∈ X}, r a.1 ∈ R := fun a =>
    Finset.mem_image_of_mem r a.2
  let g : {a : BV n // a ∈ X} → {b : BV n // b ∈ R} := fun a => ⟨r a.1, hmap a⟩
  have hgbij : Function.Bijective g := by
    constructor
    · intro a b hab
      exact Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg Subtype.val hab))
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hb
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  let e : {a : BV n // a ∈ X} ≃ {b : BV n // b ∈ R} := Equiv.ofBijective g hgbij
  let L : Equiv.Perm (BV n) := e.symm.extendSubtype
  refine ⟨fun z => L (r z), ⟨hs, ?_⟩, ?_⟩
  · intro x y
    constructor
    · intro h
      exact (repOf_eq_iff hi x y).1 (L.injective h)
    · intro h
      exact congrArg L ((repOf_eq_iff hi x y).2 h)
  · intro x hx
    have hmem : r x ∈ R := Finset.mem_image_of_mem r hx
    show L (r x) = x
    rw [show L (r x) = (e.symm ⟨r x, hmem⟩ : BV n) from
      Equiv.extendSubtype_apply_of_mem e.symm (r x) hmem]
    have : e ⟨x, hx⟩ = ⟨r x, hmem⟩ := rfl
    rw [← this, Equiv.symm_apply_apply]

/-- Simon instances exist for every nonzero hidden shift, so the promise is not
vacuous. -/
lemma exists_isSimon {s : BV n} (hs : s ≠ 0) : ∃ f : BV n → BV n, IsSimon f s := by
  obtain ⟨f, hf, -⟩ := exists_isSimon_id_on hs ∅ (by simp)
  exact ⟨f, hf⟩

/-! ### The lower bound -/

/-- **Classical lower bound for Simon's problem.**  If `q * q + 3 ≤ 2 ^ n`, then
every deterministic `q`-query algorithm fails on some Simon instance. -/
theorem classical_lower_bound {n q : ℕ} (A : QueryAlg n) (hq : q * q + 3 ≤ 2 ^ n) :
    ∃ (f : BV n → BV n) (s : BV n), IsSimon f s ∧ result A f q ≠ s := by
  classical
  -- the (at most `q`) points queried when the oracle is the identity
  set X : Finset (BV n) := (Finset.range q).image (fun k => query A id k) with hXdef
  have hXcard : X.card ≤ q := le_trans (Finset.card_image_le) (by simp)
  -- the forbidden shifts
  set D : Finset (BV n) := ((X ×ˢ X).image (fun p => p.1 + p.2)) ∪ {0} with hDdef
  have hDcard : D.card ≤ q * q + 1 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : ((X ×ˢ X).image (fun p => p.1 + p.2)).card ≤ q * q := by
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul hXcard hXcard
    simpa using Nat.add_le_add h1 (le_of_eq (Finset.card_singleton 0))
  -- there are at least two admissible shifts
  have hcompl : 1 < (Finset.univ \ D).card := by
    have hcard : (Finset.univ \ D).card = 2 ^ n - D.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_bv]
    have hD : D.card ≤ 2 ^ n := le_trans hDcard (by omega)
    omega
  obtain ⟨s, hsD, t, htD, hst⟩ := Finset.one_lt_card.1 hcompl
  have hmem : ∀ u ∈ Finset.univ \ D, u ≠ 0 ∧ ∀ x ∈ X, ∀ y ∈ X, x + y ≠ u := by
    intro u hu
    have hu' : u ∉ D := (Finset.mem_sdiff.1 hu).2
    constructor
    · intro h0
      exact hu' (by rw [h0, hDdef]; exact Finset.mem_union_right _ (Finset.mem_singleton_self 0))
    · intro x hx y hy hxy
      refine hu' ?_
      rw [hDdef]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, hxy⟩
  obtain ⟨hs0, hsX⟩ := hmem s hsD
  obtain ⟨ht0, htX⟩ := hmem t htD
  obtain ⟨f, hf, hfid⟩ := exists_isSimon_id_on hs0 X hsX
  obtain ⟨g, hg, hgid⟩ := exists_isSimon_id_on ht0 X htX
  -- both oracles agree with the identity on all queried points
  have key : ∀ (h : BV n → BV n), (∀ x ∈ X, h x = x) → result A h q = result A id q := by
    intro h hid
    have : trace A h q = trace A id q := by
      refine trace_congr A id h q ?_
      intro j hj
      have hmemj : query A id j ∈ X := by
        rw [hXdef]
        exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
      simpa using hid _ hmemj
    simp [result, this]
  have hfr : result A f q = result A id q := key f hfid
  have hgr : result A g q = result A id q := key g hgid
  by_cases hres : result A id q = s
  · exact ⟨g, t, hg, by rw [hgr, hres]; exact hst⟩
  · exact ⟨f, s, hf, by rw [hfr]; exact hres⟩

/-- **`Ω(2 ^ (n / 2))` classical queries are necessary.**  A deterministic
algorithm that always outputs the hidden shift after `q` queries must satisfy
`2 ^ n ≤ (q + 2) ^ 2`. -/
theorem classical_query_lower_bound {n q : ℕ} (A : QueryAlg n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) :
    2 ^ n ≤ (q + 2) ^ 2 := by
  by_contra h
  push_neg at h
  have hq : q * q + 3 ≤ 2 ^ n := by nlinarith [h]
  obtain ⟨f, s, hfs, hne⟩ := classical_lower_bound A hq
  exact hne (hA f s hfs)

end QI

