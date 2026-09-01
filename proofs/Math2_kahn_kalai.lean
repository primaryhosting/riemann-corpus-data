import Mathlib
/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased weight of a subset `T` of the (finite) ground set. -/
noncomputable def wt (p : ℝ) (T : Finset α) : ℝ :=
  p ^ T.card * (1 - p) ^ (Fintype.card α - T.card)

/-- The `p`-biased measure of a family `F` of subsets of the ground set. -/
noncomputable def mu (p : ℝ) (F : Finset (Finset α)) : ℝ := ∑ T ∈ F, wt p T

/-- The up-closure of a family: all sets containing some member of `H`. -/
noncomputable def upClosure (H : Finset (Finset α)) : Finset (Finset α) :=
  Finset.univ.filter (fun T => ∃ S ∈ H, S ⊆ T)

/-- `G` covers `H` if every member of `H` contains a member of `G`. -/
def IsCover (G H : Finset (Finset α)) : Prop := ∀ S ∈ H, ∃ Z ∈ G, Z ⊆ S

/-- The `q`-cost of a family. -/
noncomputable def cost (q : ℝ) (G : Finset (Finset α)) : ℝ := ∑ Z ∈ G, q ^ Z.card

/-- `H` is `q`-small if it admits a cover of `q`-cost at most `1/2`. -/
def IsSmall (q : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ G : Finset (Finset α), IsCover G H ∧ cost q G ≤ 1 / 2

/-- `H` is `κ`-spread. -/
def IsSpread (κ : ℝ) (H : Finset (Finset α)) : Prop :=
  ∀ Z : Finset α, ((H.filter (fun S => Z ⊆ S)).card : ℝ) ≤ κ ^ Z.card * H.card

/-! ### Basic facts about the `p`-biased measure -/

lemma wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset α) : 0 ≤ wt p T := by
  unfold wt
  have : (0:ℝ) ≤ 1 - p := by linarith
  positivity

/-- The total `p`-weight of all sets containing a fixed set `A` is `p ^ |A|`. -/
lemma sum_wt_superset (p : ℝ) (A : Finset α) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset α => A ⊆ T), wt p T = p ^ A.card := by
  classical
  have key : ∑ T ∈ Finset.univ.filter (fun T : Finset α => A ⊆ T), wt p T
      = ∑ U ∈ (Aᶜ).powerset, p ^ A.card * (p ^ U.card * (1 - p) ^ (Aᶜ \ U).card) := by
    refine (Finset.sum_bij' (fun U _ => A ∪ U) (fun T _ => T \ A) ?_ ?_ ?_ ?_ ?_).symm
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.subset_union_left
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      simp only [Finset.mem_powerset]
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simp only [Finset.mem_compl]
      exact hx.2
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      have hdisj : Disjoint A U := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxA hxU
        have := hU hxU
        simp only [Finset.mem_compl] at this
        exact this hxA
      show (A ∪ U) \ A = U
      rw [Finset.union_sdiff_left]
      exact (Finset.sdiff_eq_self_iff_disjoint.mpr hdisj.symm)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact Finset.union_sdiff_of_subset hT
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      have hdisj : Disjoint A U := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxA hxU
        have := hU hxU
        simp only [Finset.mem_compl] at this
        exact this hxA
      have hcard : (A ∪ U).card = A.card + U.card := Finset.card_union_of_disjoint hdisj
      have hcompl : (Aᶜ \ U).card = Fintype.card α - (A.card + U.card) := by
        rw [Finset.card_sdiff_of_subset hU, Finset.card_compl]
        have h1 : A.card ≤ Fintype.card α := Finset.card_le_univ A
        have h2 : U.card ≤ (Aᶜ).card := Finset.card_le_card hU
        rw [Finset.card_compl] at h2
        omega
      unfold wt
      rw [hcard, hcompl, pow_add]
      ring
  rw [key, ← Finset.mul_sum]
  have : ∑ U ∈ (Aᶜ).powerset, p ^ U.card * (1 - p) ^ (Aᶜ \ U).card = (p + (1 - p)) ^ (Aᶜ).card := by
    have := Finset.prod_add (fun _ : α => p) (fun _ : α => (1 - p)) (Aᶜ)
    simpa using this.symm
  rw [this]
  simp

end Math2

