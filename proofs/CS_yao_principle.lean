/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The expected cost of the randomized algorithm given by the distribution `p` over
deterministic algorithms, on the (deterministic) input `j`. -/
def algCost (A : ι → κ → ℝ) (p : ι → ℝ) (j : κ) : ℝ := ∑ i, p i * A i j

/-- The expected cost of the deterministic algorithm `i` on a random input drawn from the
distribution `q` over inputs. -/
def inpCost (A : ι → κ → ℝ) (q : κ → ℝ) (i : ι) : ℝ := ∑ j, A i j * q j

/-- The worst-case expected cost of the randomized algorithm `p`: the *randomized cost*. -/
noncomputable def randCost [Nonempty κ] (A : ι → κ → ℝ) (p : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (algCost A p)

/-- The best expected cost achievable by a deterministic algorithm against the input
distribution `q`: the *distributional cost*. -/
noncomputable def distCost [Nonempty ι] (A : ι → κ → ℝ) (q : κ → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (inpCost A q)

/-- A convex combination is at most the maximum. -/
lemma sum_smul_le_sup' [Nonempty ι] {p x : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    ∑ i, p i * x i ≤ Finset.univ.sup' Finset.univ_nonempty x := by
  obtain ⟨h0, h1⟩ := hp
  calc ∑ i, p i * x i ≤ ∑ i, p i * Finset.univ.sup' Finset.univ_nonempty x :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Finset.le_sup' x (Finset.mem_univ i)) (h0 i)
    _ = 1 * Finset.univ.sup' Finset.univ_nonempty x := by rw [← Finset.sum_mul, h1]
    _ = _ := one_mul _

/-- The minimum is at most a convex combination. -/
lemma inf'_le_sum_smul [Nonempty ι] {p x : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    Finset.univ.inf' Finset.univ_nonempty x ≤ ∑ i, p i * x i := by
  obtain ⟨h0, h1⟩ := hp
  calc Finset.univ.inf' Finset.univ_nonempty x
      = 1 * Finset.univ.inf' Finset.univ_nonempty x := (one_mul _).symm
    _ = ∑ i, p i * Finset.univ.inf' Finset.univ_nonempty x := by rw [← Finset.sum_mul, h1]
    _ ≤ ∑ i, p i * x i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Finset.inf'_le x (Finset.mem_univ i)) (h0 i)

/-- Both ways of computing the expected cost of `p` against `q` agree. -/
lemma sum_inpCost_eq_sum_algCost (A : ι → κ → ℝ) (p : ι → ℝ) (q : κ → ℝ) :
    ∑ i, p i * inpCost A q i = ∑ j, algCost A p j * q j := by
  simp only [inpCost, algCost, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- The easy direction of Yao's principle: any distributional cost is a lower bound for any
randomized cost. -/
lemma distCost_le_randCost [Nonempty ι] [Nonempty κ] (A : ι → κ → ℝ) {p : ι → ℝ} {q : κ → ℝ}
    (hp : p ∈ stdSimplex ℝ ι) (hq : q ∈ stdSimplex ℝ κ) :
    distCost A q ≤ randCost A p := by
  calc distCost A q ≤ ∑ i, p i * inpCost A q i := inf'_le_sum_smul hp
    _ = ∑ j, algCost A p j * q j := sum_inpCost_eq_sum_algCost A p q
    _ = ∑ j, q j * algCost A p j := by
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ randCost A p := sum_smul_le_sup' hq

/-- **Ville's theorem of the alternative**, the key intermediate lemma.  If the column player
cannot make every entry of `A q` positive, then the row player has a mixed strategy `p` making
every entry of `pᵀ A` nonpositive. -/
theorem ville [Nonempty ι] [Nonempty κ] (A : ι → κ → ℝ)
    (h : ∀ q ∈ stdSimplex ℝ κ, ∃ i, inpCost A q i ≤ 0) :
    ∃ p ∈ stdSimplex ℝ ι, ∀ j, algCost A p j ≤ 0 := by
  classical
  -- The convex set of expected-cost vectors achievable by the column player, and the open
  -- positive orthant.
  set K : Set (ι → ℝ) := (fun q => inpCost A q) '' stdSimplex ℝ κ with hK
  set P : Set (ι → ℝ) := {x | ∀ i, 0 < x i} with hP
  have hPpi : P = Set.pi Set.univ fun _ : ι => Set.Ioi (0 : ℝ) := by ext x; simp [hP]
  have hPopen : IsOpen P := by
    rw [hPpi]; exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioi
  have hPconv : Convex ℝ P := by rw [hPpi]; exact convex_pi fun i _ => convex_Ioi 0
  have hKconv : Convex ℝ K := by
    rintro x ⟨q, hq, rfl⟩ y ⟨q', hq', rfl⟩ a b ha hb hab
    refine ⟨a • q + b • q', convex_stdSimplex ℝ κ hq hq' ha hb hab, ?_⟩
    funext i
    simp only [inpCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdisj : Disjoint P K := by
    rw [Set.disjoint_left]
    rintro x hxP ⟨q, hq, rfl⟩
    obtain ⟨i, hi⟩ := h q hq
    exact absurd (hxP i) (not_lt.mpr hi)
  -- Separate them by a continuous linear functional.
  obtain ⟨f, u, hfP, hfK⟩ := geometric_hahn_banach_open hPconv hPopen hKconv hdisj
  set c : ι → ℝ := fun i => f (Pi.single i (1 : ℝ)) with hc
  have hf : ∀ x : ι → ℝ, f x = ∑ i, x i * c i := by
    intro x
    have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp [hc]
  have hfP' : ∀ x : ι → ℝ, (∀ i, 0 < x i) → ∑ i, x i * c i < u := by
    intro x hx; rw [← hf]; exact hfP x hx
  have hfK' : ∀ q ∈ stdSimplex ℝ κ, u ≤ ∑ i, inpCost A q i * c i := by
    intro q hq; rw [← hf]; exact hfK _ ⟨q, hq, rfl⟩
  set S : ℝ := ∑ i, c i with hS
  -- Step 1: all coefficients of the separating functional are nonpositive.
  have hcnp : ∀ i, c i ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₀, hi₀⟩ := hcon
    set t : ℝ := max 1 ((u - S + 1) / c i₀) with ht
    have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
    have ht2 : (u - S + 1) / c i₀ ≤ t := le_max_right _ _
    have ht3 : u - S + 1 ≤ t * c i₀ := by rw [div_le_iff₀ hi₀] at ht2; linarith
    have hx : ∀ i, 0 < (fun i => 1 + if i = i₀ then t else 0) i := by
      intro i
      by_cases hi : i = i₀ <;> simp [hi] <;> linarith
    have hlt := hfP' _ hx
    have hsum : ∑ i, (1 + if i = i₀ then t else 0) * c i = S + t * c i₀ := by
      simp only [add_mul, Finset.sum_add_distrib, one_mul, ite_mul, zero_mul,
        Finset.sum_ite_eq' Finset.univ i₀]
      simp [hS]
    rw [hsum] at hlt
    linarith
  have hSnp : S ≤ 0 := Finset.sum_nonpos fun i _ => hcnp i
  -- Step 2: the separating constant is nonnegative.
  have hu : 0 ≤ u := by
    rcases eq_or_lt_of_le hSnp with hS0 | hSneg
    · have hlt := hfP' (fun _ => 1) fun i => zero_lt_one
      simp only [one_mul] at hlt
      rw [← hS] at hlt
      linarith
    · by_contra hu
      push_neg at hu
      set e : ℝ := u / (2 * S) with he
      have hepos : 0 < e := div_pos_of_neg_of_neg hu (by linarith)
      have hlt := hfP' (fun _ => e) fun i => hepos
      rw [show ∑ i : ι, e * c i = e * S by rw [← Finset.mul_sum], he, div_mul_eq_mul_div,
        mul_comm, show S * u / (2 * S) = u / 2 by field_simp] at hlt
      linarith
  -- Step 3: some coefficient is strictly negative.
  have hneg : ∃ i, c i < 0 := by
    by_contra hcon
    push_neg at hcon
    have hc0 : ∀ i, c i = 0 := fun i => le_antisymm (hcnp i) (hcon i)
    have h1 : (0 : ℝ) < u := by
      have := hfP' (fun _ => 1) fun i => zero_lt_one
      simpa [hc0] using this
    obtain ⟨q₀, hq₀⟩ : (stdSimplex ℝ κ).Nonempty := Set.Nonempty.of_subtype
    have h2 := hfK' q₀ hq₀
    simp only [hc0, mul_zero, Finset.sum_const_zero] at h2
    linarith
  -- Step 4: normalize `-c` into a mixed strategy for the row player.
  obtain ⟨i₁, hi₁⟩ := hneg
  set S' : ℝ := ∑ i, -c i with hS'
  have hS'pos : 0 < S' :=
    Finset.sum_pos' (fun i _ => neg_nonneg.mpr (hcnp i)) ⟨i₁, Finset.mem_univ _, by linarith⟩
  refine ⟨fun i => (-c i) / S', ⟨fun i => div_nonneg (neg_nonneg.mpr (hcnp i)) hS'pos.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hS', div_self hS'pos.ne']
  · intro j
    have hq : (Pi.single j (1 : ℝ) : κ → ℝ) ∈ stdSimplex ℝ κ := by
      refine ⟨fun k => ?_, by simp⟩
      rw [Pi.single_apply]; split <;> norm_num
    have hmain := hfK' _ hq
    have heval : ∀ i, inpCost A (Pi.single j (1 : ℝ) : κ → ℝ) i = A i j := by
      intro i; simp [inpCost, Pi.single_apply]
    simp only [heval] at hmain
    have hrw : algCost A (fun i => (-c i) / S') j = (-(∑ i, A i j * c i)) / S' := by
      simp only [algCost]
      rw [eq_div_iff hS'pos.ne', Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [hrw]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hS'pos.le

/-- **Yao's minimax principle**: for a finite cost matrix `A` indexed by deterministic
algorithms `ι` and inputs `κ`, the least worst-case expected cost of a randomized algorithm
equals the greatest, over input distributions, expected cost of the best deterministic
algorithm. -/
theorem yao_principle [Nonempty ι] [Nonempty κ] (A : ι → κ → ℝ) :
    sInf (randCost A '' stdSimplex ℝ ι) = sSup (distCost A '' stdSimplex ℝ κ) := by
  obtain ⟨p₀, hp₀⟩ : (stdSimplex ℝ ι).Nonempty := Set.Nonempty.of_subtype
  obtain ⟨q₀, hq₀⟩ : (stdSimplex ℝ κ).Nonempty := Set.Nonempty.of_subtype
  have hLne : (randCost A '' stdSimplex ℝ ι).Nonempty := ⟨_, ⟨p₀, hp₀, rfl⟩⟩
  have hRne : (distCost A '' stdSimplex ℝ κ).Nonempty := ⟨_, ⟨q₀, hq₀, rfl⟩⟩
  have hbb : BddBelow (randCost A '' stdSimplex ℝ ι) :=
    ⟨distCost A q₀, by rintro x ⟨p, hp, rfl⟩; exact distCost_le_randCost A hp hq₀⟩
  have hba : BddAbove (distCost A '' stdSimplex ℝ κ) :=
    ⟨randCost A p₀, by rintro x ⟨q, hq, rfl⟩; exact distCost_le_randCost A hp₀ hq⟩
  have hRL : sSup (distCost A '' stdSimplex ℝ κ) ≤ sInf (randCost A '' stdSimplex ℝ ι) := by
    refine csSup_le hRne ?_
    rintro x ⟨q, hq, rfl⟩
    refine le_csInf hLne ?_
    rintro y ⟨p, hp, rfl⟩
    exact distCost_le_randCost A hp hq
  refine le_antisymm ?_ hRL
  by_contra hlt
  push_neg at hlt
  set R := sSup (distCost A '' stdSimplex ℝ κ) with hR
  set L := sInf (randCost A '' stdSimplex ℝ ι) with hL
  set c : ℝ := (R + L) / 2 with hc
  have hRc : R < c := by simp only [hc]; linarith
  have hcL : c < L := by simp only [hc]; linarith
  have key : ∀ q ∈ stdSimplex ℝ κ, ∃ i, inpCost (fun i j => A i j - c) q i ≤ 0 := by
    intro q hq
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) (inpCost A q)
    refine ⟨i, ?_⟩
    have hdq : distCost A q ≤ R := le_csSup hba ⟨q, hq, rfl⟩
    have h1 : inpCost A q i ≤ R := by rw [← hi]; exact hdq
    have h2 : inpCost (fun i j => A i j - c) q i = inpCost A q i - c := by
      simp only [inpCost, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hq.2, mul_one]
    rw [h2]
    linarith
  obtain ⟨p, hp, hple⟩ := ville _ key
  have hpc : randCost A p ≤ c := by
    refine Finset.sup'_le _ _ fun j _ => ?_
    have := hple j
    have h2 : algCost (fun i j => A i j - c) p j = algCost A p j - c := by
      simp only [algCost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
    rw [h2] at this
    linarith
  have hLp : L ≤ randCost A p := csInf_le hbb ⟨p, hp, rfl⟩
  linarith

end CS

