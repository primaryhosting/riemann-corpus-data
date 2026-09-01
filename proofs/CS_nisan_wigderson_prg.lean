import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- Real-valued indicator of a Boolean value. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

variable {ℓ m : ℕ}

/-- The `k`-th hybrid string: the first `k` output bits are produced by the generator
component functions `G j` on the seed `x`, the remaining ones are the truly random bits `r j`. -/
def hybridStr (G : Fin m → (Fin ℓ → Bool) → Bool) (k : ℕ)
    (x : Fin ℓ → Bool) (r : Fin m → Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < k then G j x else r j

/-- Unnormalised acceptance count of the distinguisher `D` on the `k`-th hybrid. -/
def hybSum (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool) (k : ℕ) : ℝ :=
  ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (D (hybridStr G k x r))

/-- Acceptance probability of `D` on the `k`-th hybrid distribution. -/
noncomputable def hybrid (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)
    (k : ℕ) : ℝ :=
  hybSum G D k / (2 ^ ℓ * 2 ^ m)

/-- The Nisan–Wigderson / Yao next-bit predictor for the `i`-th output bit, built from the
distinguisher `D`, the earlier generator components `G j` (`j < i`), a fixed string `r` of
random bits and a bit `c` telling whether to complement the output. -/
def nwPredictor (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)
    (i : Fin m) (r : Fin m → Bool) (c : Bool) (x : Fin ℓ → Bool) : Bool :=
  xor c (if D (hybridStr G i x r) then r i else !(r i))

/-- Probability (over the seed `x`) that the predictor correctly computes the `i`-th
generator component `G i`. -/
noncomputable def predProb (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)
    (i : Fin m) (r : Fin m → Bool) (c : Bool) : ℝ :=
  (∑ x : Fin ℓ → Bool, ind (nwPredictor G D i r c x == G i x)) / 2 ^ ℓ

section Aux

lemma ind_not (b : Bool) : ind (!b) = 1 - ind b := by
  cases b <;> simp [ind]

lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]

/-- Averaging over an updated coordinate: summing `F` over all strings with the `i`-th
coordinate overwritten by `b`, for both values of `b`, doubles the total sum. -/
lemma sum_update_bool (i : Fin m) (F : (Fin m → Bool) → ℝ) :
    ∑ b : Bool, ∑ r : Fin m → Bool, F (Function.update r i b) = 2 * ∑ r : Fin m → Bool, F r := by
  have hinv : Function.Involutive (fun r : Fin m → Bool => Function.update r i (!(r i))) := by
    intro r
    simp [Function.update_idem]
  have hswap : ∑ r : Fin m → Bool, F (Function.update r i (!(r i)))
      = ∑ r : Fin m → Bool, F r :=
    Equiv.sum_comp (hinv.toPerm _) F
  rw [Finset.sum_comm]
  have hpt : ∀ r : Fin m → Bool, ∑ b : Bool, F (Function.update r i b)
      = F r + F (Function.update r i (!(r i))) := by
    intro r
    rw [Fintype.sum_bool]
    cases h : r i
    · rw [show Function.update r i false = r by rw [← h]; exact Function.update_eq_self i r]
      simp only [Bool.not_false]
      ring
    · rw [show Function.update r i true = r by rw [← h]; exact Function.update_eq_self i r]
      simp only [Bool.not_true]
  calc ∑ r : Fin m → Bool, ∑ b : Bool, F (Function.update r i b)
      = ∑ r : Fin m → Bool, (F r + F (Function.update r i (!(r i)))) := by
        exact Finset.sum_congr rfl fun r _ => hpt r
    _ = (∑ r : Fin m → Bool, F r) + ∑ r : Fin m → Bool, F (Function.update r i (!(r i))) :=
        Finset.sum_add_distrib
    _ = 2 * ∑ r : Fin m → Bool, F r := by rw [hswap]; ring

/-- The `(i+1)`-st hybrid is the `i`-th hybrid with the `i`-th random bit overwritten by
the generator bit. -/
lemma hybridStr_succ (G : Fin m → (Fin ℓ → Bool) → Bool) (i : Fin m)
    (x : Fin ℓ → Bool) (r : Fin m → Bool) :
    hybridStr G ((i : ℕ) + 1) x r = hybridStr G i x (Function.update r i (G i x)) := by
  funext j
  rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
  · have hlt : (j : ℕ) < (i : ℕ) + 1 := by omega
    simp [hybridStr, hlt, h]
  · have hj : j = i := Fin.ext h
    subst hj
    simp [hybridStr]
  · have h1 : ¬ ((j : ℕ) < (i : ℕ) + 1) := by omega
    have h2 : ¬ ((j : ℕ) < (i : ℕ)) := by omega
    have hne : j ≠ i := by
      intro hj; subst hj; omega
    simp [hybridStr, h1, h2, Function.update_of_ne hne]

end Aux

section Core

variable (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)

/-- The unnormalised number of `(x, r)` pairs on which the (uncomplemented) next-bit
predictor for position `i` is correct, expressed through two consecutive hybrids. -/
lemma corr_eq (i : Fin m) :
    ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool,
        ind (nwPredictor G D i r false x == G i x)
      = hybSum G D ((i : ℕ) + 1) - hybSum G D i + 2 ^ ℓ * 2 ^ m / 2 := by
  have key : ∀ x : Fin ℓ → Bool,
      ∑ r : Fin m → Bool, ind (nwPredictor G D i r false x == G i x)
        = (∑ r : Fin m → Bool, ind (D (hybridStr G ((i : ℕ) + 1) x r)))
          - (∑ r : Fin m → Bool, ind (D (hybridStr G i x r))) + 2 ^ m / 2 := by
    intro x
    set F : (Fin m → Bool) → ℝ := fun r => ind (D (hybridStr G i x r)) with hF
    set v : Bool := G i x with hv
    -- rewrite the correctness indicator
    have hcorr : ∀ r : Fin m → Bool,
        ind (nwPredictor G D i r false x == G i x)
          = if r i = v then F r else 1 - F r := by
      intro r
      by_cases h : r i = v
      · simp only [nwPredictor, hF, ind, h]
        by_cases hD : D (hybridStr G i x r) <;> simp [hD, ← hv]
      · have h' : r i = !v := by
          cases hrv : r i <;> cases hvv : v <;> simp_all
        simp only [nwPredictor, hF, ind]
        by_cases hD : D (hybridStr G i x r) <;> simp [hD, h', ← hv]
    -- apply the averaging lemma to `g`
    have hg := sum_update_bool i (fun r => if r i = v then F r else 1 - F r)
    have hFsum := sum_update_bool i F
    have hupd : ∀ (b : Bool) (r : Fin m → Bool), (Function.update r i b) i = b := by
      intro b r; simp
    have hgb : ∀ b : Bool, ∑ r : Fin m → Bool,
        (if (Function.update r i b) i = v then F (Function.update r i b)
          else 1 - F (Function.update r i b))
        = if b = v then ∑ r : Fin m → Bool, F (Function.update r i b)
          else (2 : ℝ) ^ m - ∑ r : Fin m → Bool, F (Function.update r i b) := by
      intro b
      by_cases hb : b = v
      · simp [hb]
      · simp only [hupd, if_neg hb, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.card_univ]
    have hsumB : (∑ b : Bool, ∑ r : Fin m → Bool,
        (if (Function.update r i b) i = v then F (Function.update r i b)
          else 1 - F (Function.update r i b)))
        = (∑ r : Fin m → Bool, F (Function.update r i v))
          + ((2 : ℝ) ^ m - ∑ r : Fin m → Bool, F (Function.update r i (!v))) := by
      rw [Fintype.sum_bool, hgb true, hgb false]
      cases v <;> (simp; try ring)
    have hpair : (∑ r : Fin m → Bool, F (Function.update r i v))
        + (∑ r : Fin m → Bool, F (Function.update r i (!v))) = 2 * ∑ r : Fin m → Bool, F r := by
      rw [← hFsum, Fintype.sum_bool]
      cases v <;> (simp; try ring)
    have hsucc : (∑ r : Fin m → Bool, ind (D (hybridStr G ((i : ℕ) + 1) x r)))
        = ∑ r : Fin m → Bool, F (Function.update r i v) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hybridStr_succ]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ (univ : Finset (Fin m → Bool))) => hcorr r]
    have hgg : ∑ r : Fin m → Bool, (if r i = v then F r else 1 - F r)
        = (1 / 2 : ℝ) * ((∑ r : Fin m → Bool, F (Function.update r i v))
          + ((2 : ℝ) ^ m - ∑ r : Fin m → Bool, F (Function.update r i (!v)))) := by
      rw [← hsumB, hg]; ring
    rw [hgg, hsucc]
    have : (∑ r : Fin m → Bool, F (Function.update r i (!v)))
        = 2 * (∑ r : Fin m → Bool, F r) - ∑ r : Fin m → Bool, F (Function.update r i v) := by
      linarith [hpair]
    rw [this]
    ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset (Fin ℓ → Bool))) => key x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp [hybSum]
  ring

/-- The complemented predictor is correct exactly when the uncomplemented one is wrong. -/
lemma corr_true_eq (i : Fin m) :
    ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r true x == G i x)
      = 2 ^ ℓ * 2 ^ m
        - ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r false x == G i x) := by
  have hpt : ∀ (x : Fin ℓ → Bool) (r : Fin m → Bool),
      ind (nwPredictor G D i r true x == G i x)
        = 1 - ind (nwPredictor G D i r false x == G i x) := by
    intro x r
    have hnot : nwPredictor G D i r true x = !(nwPredictor G D i r false x) := by
      simp [nwPredictor]
    rw [hnot, ← ind_not]
    congr 1
    cases nwPredictor G D i r false x <;> cases G i x <;> simp
  calc ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r true x == G i x)
      = ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool,
          (1 - ind (nwPredictor G D i r false x == G i x)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => hpt x r
    _ = 2 ^ ℓ * 2 ^ m
        - ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool,
            ind (nwPredictor G D i r false x == G i x) := by
        simp [Finset.sum_sub_distrib, Finset.card_univ, Finset.sum_const]

lemma hybSum_zero : hybSum G D 0 = 2 ^ ℓ * ∑ y : Fin m → Bool, ind (D y) := by
  unfold hybSum
  have h0 : ∀ (x : Fin ℓ → Bool) (r : Fin m → Bool), hybridStr G 0 x r = r := by
    intro x r; funext j; simp [hybridStr]
  simp [h0, Finset.card_univ]

lemma hybSum_full : hybSum G D m = 2 ^ m * ∑ x : Fin ℓ → Bool, ind (D (fun i => G i x)) := by
  unfold hybSum
  have hm : ∀ (x : Fin ℓ → Bool) (r : Fin m → Bool), hybridStr G m x r = fun i => G i x := by
    intro x r; funext j; simp [hybridStr, j.isLt]
  simp [hm, Finset.card_univ, Finset.mul_sum]

end Core

/-- The hardness hypothesis below is satisfiable with `ε = 0`: for the identity generator
(`ℓ = m`, `G i x = x i`) every Nisan–Wigderson next-bit predictor succeeds with probability
exactly `1/2`, because the predictor never looks at the `i`-th seed bit. -/
lemma predProb_identity {m : ℕ} (D : (Fin m → Bool) → Bool) (i : Fin m) (r : Fin m → Bool)
    (c : Bool) : predProb (ℓ := m) (fun j x => x j) D i r c = 1 / 2 := by
  set G : Fin m → (Fin m → Bool) → Bool := fun j x => x j with hG
  set P : (Fin m → Bool) → Bool := fun x => nwPredictor G D i r c x with hP
  have hindep : ∀ (x : Fin m → Bool) (b : Bool), P (Function.update x i b) = P x := by
    intro x b
    have hstr : hybridStr G i (Function.update x i b) r = hybridStr G i x r := by
      funext j
      by_cases hj : (j : ℕ) < (i : ℕ)
      · have hne : j ≠ i := by
          intro h; subst h; omega
        simp [hybridStr, hj, hG, Function.update_of_ne hne]
      · simp [hybridStr, hj]
    simp [hP, nwPredictor, hstr]
  have key := sum_update_bool i (fun x : Fin m → Bool => ind (P x == G i x))
  have hleft : ∑ b : Bool, ∑ x : Fin m → Bool,
      ind (P (Function.update x i b) == G i (Function.update x i b)) = 2 ^ m := by
    rw [Finset.sum_comm]
    have hx : ∀ x : Fin m → Bool, ∑ b : Bool,
        ind (P (Function.update x i b) == G i (Function.update x i b)) = 1 := by
      intro x
      have : ∀ b : Bool, ind (P (Function.update x i b) == G i (Function.update x i b))
          = ind (P x == b) := by
        intro b; rw [hindep x b]; simp [hG]
      rw [Fintype.sum_bool, this true, this false]
      cases P x <;> simp [ind]
    rw [Finset.sum_congr rfl fun x _ => hx x]
    simp [Finset.card_univ]
  rw [hleft] at key
  unfold predProb
  rw [show (∑ x : Fin m → Bool, ind (nwPredictor G D i r c x == G i x))
      = ∑ x : Fin m → Bool, ind (P x == G i x) from rfl]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  field_simp
  linarith [key]

/-- **Nisan–Wigderson generator: security from hardness.**

Let `G 0, …, G (m-1)` be the component functions of a generator that maps a seed
`x : Fin ℓ → Bool` to the `m`-bit string `fun i => G i x` (in the Nisan–Wigderson
construction `G i x = f (x restricted to the i-th set of a combinatorial design)`).
Let `D` be any distinguisher.

Hardness hypothesis: no next-bit predictor of Nisan–Wigderson / Yao type — i.e. no function
obtained from `D` by hard-wiring the later random bits `r`, feeding it the earlier generator
bits, and possibly complementing the answer — predicts any output bit `G i` with advantage
more than `ε / m`.

Conclusion: `D` cannot distinguish the generator's output from a uniformly random `m`-bit
string with advantage more than `ε`; i.e. the generator derandomizes `D`. -/
theorem nisan_wigderson_prg {ℓ m : ℕ} (hm : 0 < m)
    (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool) (ε : ℝ)
    (hard : ∀ (i : Fin m) (r : Fin m → Bool) (c : Bool),
      predProb G D i r c ≤ 1 / 2 + ε / m) :
    |(∑ x : Fin ℓ → Bool, ind (D (fun i => G i x))) / 2 ^ ℓ
      - (∑ y : Fin m → Bool, ind (D y)) / 2 ^ m| ≤ ε := by
  have hT : (0 : ℝ) < 2 ^ ℓ * 2 ^ m := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the hardness hypothesis, averaged over the random string `r`
  have havg : ∀ (i : Fin m) (c : Bool),
      ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r c x == G i x)
        ≤ 2 ^ ℓ * 2 ^ m * (1 / 2 + ε / m) := by
    intro i c
    rw [Finset.sum_comm]
    have hone : ∀ r : Fin m → Bool,
        ∑ x : Fin ℓ → Bool, ind (nwPredictor G D i r c x == G i x)
          ≤ 2 ^ ℓ * (1 / 2 + ε / m) := by
      intro r
      have h := hard i r c
      unfold predProb at h
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ ℓ)] at h
      linarith
    calc ∑ r : Fin m → Bool, ∑ x : Fin ℓ → Bool, ind (nwPredictor G D i r c x == G i x)
        ≤ ∑ _r : Fin m → Bool, (2 : ℝ) ^ ℓ * (1 / 2 + ε / m) :=
          Finset.sum_le_sum fun r _ => hone r
      _ = 2 ^ ℓ * 2 ^ m * (1 / 2 + ε / m) := by simp [Finset.card_univ]; ring
  -- each hybrid step moves the acceptance count by at most `T * ε / m`
  have hstep : ∀ i : Fin m,
      |hybSum G D ((i : ℕ) + 1) - hybSum G D i| ≤ 2 ^ ℓ * 2 ^ m * (ε / m) := by
    intro i
    have h1 := havg i false
    have h2 := havg i true
    rw [corr_true_eq G D i] at h2
    rw [corr_eq G D i] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  -- telescoping over the `m` hybrids
  have htel : hybSum G D m - hybSum G D 0
      = ∑ i ∈ Finset.range m, (hybSum G D (i + 1) - hybSum G D i) :=
    (Finset.sum_range_sub (fun k => hybSum G D k) m).symm
  have hsum : |hybSum G D m - hybSum G D 0| ≤ 2 ^ ℓ * 2 ^ m * ε := by
    rw [htel]
    calc |∑ i ∈ Finset.range m, (hybSum G D (i + 1) - hybSum G D i)|
        ≤ ∑ i ∈ Finset.range m, |hybSum G D (i + 1) - hybSum G D i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range m, 2 ^ ℓ * 2 ^ m * (ε / m) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact hstep ⟨i, Finset.mem_range.mp hi⟩
      _ = 2 ^ ℓ * 2 ^ m * ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  -- rewrite the distinguishing advantage in terms of the extreme hybrids
  have hgoal : (∑ x : Fin ℓ → Bool, ind (D (fun i => G i x))) / 2 ^ ℓ
      - (∑ y : Fin m → Bool, ind (D y)) / 2 ^ m
      = (hybSum G D m - hybSum G D 0) / (2 ^ ℓ * 2 ^ m) := by
    rw [hybSum_full G D, hybSum_zero G D]
    field_simp
  rw [hgoal, abs_div, abs_of_pos hT, div_le_iff₀ hT]
  linarith [hsum]

end CS

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

