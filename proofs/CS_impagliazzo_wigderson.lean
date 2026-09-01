/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
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

namespace CS

/-!
## Setting

We formalise the derandomisation half of the Impagliazzo–Wigderson theorem:

*strong circuit lower bounds ⟹ P = BPP.*

The hardness-versus-randomness construction (Nisan–Wigderson generator together with
hardness amplification) turns a function in `E` requiring circuits of size `2^{Ω(n)}`
into a pseudorandom generator `G` with logarithmic seed length that fools all
polynomial-size circuits with error `1/6`.  That generator is taken here as the
hypothesis `hPRG` (together with the logarithmic seed length `hlog`), and what is
proved is that such a generator collapses `BPP` into `P`: the bounded-error
randomised algorithm `A` is replaced by a deterministic majority vote over the
polynomially many outputs of `G`, and this deterministic procedure decides the
language exactly.

Inputs are bit strings (`List Bool`), a language is a predicate `L : List Bool → Bool`,
and a randomised algorithm on inputs of length `n` uses `m n` random bits.
-/

/-- The acceptance probability of a test `f` on `m` uniform random bits, i.e. the
fraction of the `2 ^ m` random strings on which `f` outputs `true`. -/
noncomputable def prob {m : ℕ} (f : (Fin m → Bool) → Bool) : ℚ :=
  ((Finset.univ.filter fun r => f r = true).card : ℚ) / 2 ^ m

/-- Majority vote of `t` Boolean values: `true` iff strictly more than half of them are
`true`. -/
def majorityVote {t : ℕ} (f : Fin t → Bool) : Bool :=
  decide (t < 2 * (Finset.univ.filter fun i => f i = true).card)

/-- `L` is decided deterministically in polynomial time given the (polynomial-time)
algorithm `A`: there is a polynomially bounded family of seeds, computed
deterministically from the input, such that the majority vote of `A` over those seeds
decides `L` on every input. -/
def DerandomizedInP (m : ℕ → ℕ)
    (A : ∀ x : List Bool, (Fin (m x.length) → Bool) → Bool)
    (L : List Bool → Bool) : Prop :=
  ∃ (t : ℕ → ℕ) (c k : ℕ)
    (seeds : ∀ x : List Bool, Fin (t x.length) → (Fin (m x.length) → Bool)),
    (∀ n, t n ≤ c * (n + 1) ^ k) ∧
    ∀ x, majorityVote (fun i => A x (seeds x i)) = L x

/-- If strictly more than half of the seeds `y` satisfy `g y = b`, then the majority
vote of `g` taken along any indexing `e` of the seed space equals `b`. -/
theorem majorityVote_of_majority {s : ℕ} (g : (Fin s → Bool) → Bool) (b : Bool)
    (e : Fin (2 ^ s) ≃ (Fin s → Bool))
    (h : 2 ^ s < 2 * (Finset.univ.filter fun y => (g y == b) = true).card) :
    majorityVote (fun i => g (e i)) = b := by
  have hcard : (Finset.univ.filter fun i : Fin (2 ^ s) => g (e i) = true).card
      = (Finset.univ.filter fun y => g y = true).card := Finset.card_equiv e (by simp)
  cases b with
  | true =>
      simp only [majorityVote, hcard, decide_eq_true_eq]
      simpa using h
  | false =>
      have hsplit : (Finset.univ.filter fun y : (Fin s → Bool) => g y = true).card
          + (Finset.univ.filter fun y : (Fin s → Bool) => ¬ (g y = true)).card = 2 ^ s := by
        rw [Finset.card_filter_add_card_filter_not]; simp
      have h' : 2 ^ s < 2 * (Finset.univ.filter fun y : (Fin s → Bool) => ¬ (g y = true)).card := by
        refine lt_of_lt_of_le h (le_of_eq ?_)
        congr 2
        ext y
        simp
      simp only [majorityVote, hcard, decide_eq_false_iff_not, not_lt]
      omega

/-- An acceptance probability exceeding `1/2` means a strict majority of the seeds
are accepting. -/
theorem card_gt_of_prob_gt_half {s : ℕ} (f : (Fin s → Bool) → Bool) (h : 1 / 2 < prob f) :
    2 ^ s < 2 * (Finset.univ.filter fun y => f y = true).card := by
  rw [prob, lt_div_iff₀ (by positivity)] at h
  have : ((2 : ℚ) ^ s : ℚ) < 2 * ((Finset.univ.filter fun y => f y = true).card : ℚ) := by
    linarith
  exact_mod_cast this

/-- **Impagliazzo–Wigderson (derandomisation form): strong circuit lower bounds imply
`P = BPP`.**

Assume `L` is decided by a bounded-error randomised algorithm `A` using `m n` random
bits on inputs of length `n` (`hBPP`: the algorithm is correct with probability more
than `2/3`).  Assume moreover that the hardness-versus-randomness construction supplies
a pseudorandom generator `G` with seed length `s n` which fools the tests attached to
`A` with error at most `1/6` (`hPRG`) and whose seed length is logarithmic, so that the
seed space has polynomial size (`hlog`).

Then `L` is decided deterministically by the majority vote of `A` over the polynomially
many pseudorandom strings `G y`, i.e. `L ∈ P` (relative to the deterministic
polynomial-time algorithm `A`). -/
theorem impagliazzo_wigderson
    (L : List Bool → Bool) (m s : ℕ → ℕ)
    (A : ∀ x : List Bool, (Fin (m x.length) → Bool) → Bool)
    (G : ∀ n : ℕ, (Fin (s n) → Bool) → (Fin (m n) → Bool))
    (c k : ℕ)
    (hlog : ∀ n, 2 ^ s n ≤ c * (n + 1) ^ k)
    (hBPP : ∀ x : List Bool, 2 / 3 < prob (fun r => (A x r == L x)))
    (hPRG : ∀ x : List Bool,
        |prob (fun y => (A x (G x.length y) == L x)) - prob (fun r => (A x r == L x))|
          ≤ 1 / 6) :
    DerandomizedInP m A L := by
  have hequiv : ∀ n : ℕ, Fin (2 ^ s n) ≃ (Fin (s n) → Bool) := fun n =>
    (Fintype.equivFinOfCardEq (by simp)).symm
  refine ⟨fun n => 2 ^ s n, c, k, fun x i => G x.length (hequiv x.length i), hlog, ?_⟩
  intro x
  -- the generator preserves the success probability up to `1/6`, hence keeps it above `1/2`
  have hhalf : 1 / 2 < prob (fun y => (A x (G x.length y) == L x)) := by
    have h1 := hBPP x
    have h2 := abs_le.1 (hPRG x)
    linarith [h2.1, h2.2]
  exact majorityVote_of_majority (fun y => A x (G x.length y)) (L x) (hequiv x.length)
    (card_gt_of_prob_gt_half _ hhalf)

/-- The hypotheses of `impagliazzo_wigderson` are satisfiable, so the theorem is not
vacuous: the trivial (deterministic, always correct) randomised algorithm together with
the identity generator meets all of them, for an arbitrary language `L`. -/
example (L : List Bool → Bool) :
    ∃ (m s : ℕ → ℕ) (A : ∀ x : List Bool, (Fin (m x.length) → Bool) → Bool)
      (G : ∀ n : ℕ, (Fin (s n) → Bool) → (Fin (m n) → Bool)) (c k : ℕ),
      (∀ n, 2 ^ s n ≤ c * (n + 1) ^ k) ∧
      (∀ x : List Bool, 2 / 3 < prob (fun r => (A x r == L x))) ∧
      (∀ x : List Bool,
        |prob (fun y => (A x (G x.length y) == L x)) - prob (fun r => (A x r == L x))|
          ≤ 1 / 6) := by
  refine ⟨fun _ => 1, fun _ => 1, fun x _ => L x, fun _ y => y, 2, 0, fun n => by norm_num,
    fun x => ?_, fun x => ?_⟩
  · simp [prob]
    norm_num
  · simp [prob]

end CS

