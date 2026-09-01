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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Finset Set

variable {A I : Type*} [Fintype A] [Fintype I]

/-- `distCost c μ a` is the expected cost of the *deterministic* algorithm `a`
when the input is drawn from the distribution `μ` on inputs. -/
def distCost (c : A → I → ℝ) (μ : I → ℝ) (a : A) : ℝ := ∑ i, μ i * c a i

/-- `randCost c q i` is the expected cost of the *randomized* algorithm given by the
distribution `q` over deterministic algorithms, on the (worst-case chosen) input `i`. -/
def randCost (c : A → I → ℝ) (q : A → ℝ) (i : I) : ℝ := ∑ a, q a * c a i

/-- The set of values `min_a E_{i ~ μ} c a i`, as `μ` ranges over input distributions. -/
def distValues (c : A → I → ℝ) : Set ℝ :=
  {r : ℝ | ∃ μ ∈ stdSimplex ℝ I, r = ⨅ a, distCost c μ a}

/-- The set of values `max_i E_{a ~ q} c a i`, as `q` ranges over distributions on algorithms. -/
def randValues (c : A → I → ℝ) : Set ℝ :=
  {r : ℝ | ∃ q ∈ stdSimplex ℝ A, r = ⨆ i, randCost c q i}

/-- The **distributional complexity** of the cost matrix `c`: the largest, over all input
distributions `μ`, of the best expected cost achievable by a deterministic algorithm. -/
noncomputable def distributionalComplexity (c : A → I → ℝ) : ℝ := sSup (distValues c)

/-- The **randomized complexity** of the cost matrix `c`: the smallest, over all randomized
algorithms `q`, of the worst-case (over inputs) expected cost. -/
noncomputable def randomizedComplexity (c : A → I → ℝ) : ℝ := sInf (randValues c)

lemma bddBelow_range_distCost (c : A → I → ℝ) (μ : I → ℝ) :
    BddBelow (Set.range (distCost c μ)) :=
  Set.Finite.bddBelow (Set.finite_range _)

lemma bddAbove_range_randCost (c : A → I → ℝ) (q : A → ℝ) :
    BddAbove (Set.range (randCost c q)) :=
  Set.Finite.bddAbove (Set.finite_range _)

section Basic

variable [Nonempty A] [Nonempty I]

omit [Nonempty A] [Nonempty I] in
/-- **Weak duality**: any deterministic algorithm's best expected cost against an input
distribution is at most the worst-case expected cost of any randomized algorithm. -/
theorem ciInf_distCost_le_ciSup_randCost (c : A → I → ℝ)
    {μ : I → ℝ} (hμ : μ ∈ stdSimplex ℝ I) {q : A → ℝ} (hq : q ∈ stdSimplex ℝ A) :
    (⨅ a, distCost c μ a) ≤ ⨆ i, randCost c q i := by
  have h1 : ∀ a, (⨅ a, distCost c μ a) ≤ distCost c μ a := fun a =>
    ciInf_le (bddBelow_range_distCost c μ) a
  have h2 : ∀ i, randCost c q i ≤ ⨆ i, randCost c q i := fun i =>
    le_ciSup (bddAbove_range_randCost c q) i
  have step1 : (⨅ a, distCost c μ a) ≤ ∑ a, q a * distCost c μ a := by
    calc (⨅ a, distCost c μ a) = ∑ a, q a * (⨅ a, distCost c μ a) := by
          rw [← Finset.sum_mul, hq.2, one_mul]
      _ ≤ ∑ a, q a * distCost c μ a :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h1 a) (hq.1 a)
  have swap : ∑ a, q a * distCost c μ a = ∑ i, μ i * randCost c q i := by
    simp only [distCost, randCost, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  have step2 : ∑ i, μ i * randCost c q i ≤ ⨆ i, randCost c q i := by
    calc ∑ i, μ i * randCost c q i ≤ ∑ i, μ i * (⨆ i, randCost c q i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h2 i) (hμ.1 i)
      _ = ⨆ i, randCost c q i := by rw [← Finset.sum_mul, hμ.2, one_mul]
  linarith [step1, step2, swap ▸ step1]

omit [Fintype A] [Nonempty A] in
lemma distValues_nonempty (c : A → I → ℝ) : (distValues c).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact ⟨_, ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, rfl⟩⟩

omit [Fintype I] [Nonempty I] in
lemma randValues_nonempty (c : A → I → ℝ) : (randValues c).Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨_, ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, rfl⟩⟩

omit [Nonempty I] in
lemma bddAbove_distValues (c : A → I → ℝ) : BddAbove (distValues c) := by
  obtain ⟨s, q, hq, rfl⟩ := randValues_nonempty c
  refine ⟨⨆ i, randCost c q i, ?_⟩
  rintro r ⟨μ, hμ, rfl⟩
  exact ciInf_distCost_le_ciSup_randCost c hμ hq

omit [Nonempty A] in
lemma bddBelow_randValues (c : A → I → ℝ) : BddBelow (randValues c) := by
  obtain ⟨s, μ, hμ, rfl⟩ := distValues_nonempty c
  refine ⟨⨅ a, distCost c μ a, ?_⟩
  rintro r ⟨q, hq, rfl⟩
  exact ciInf_distCost_le_ciSup_randCost c hμ hq

/-- The easy inequality of Yao's principle: distributional complexity is at most
randomized complexity. -/
theorem distributionalComplexity_le_randomizedComplexity (c : A → I → ℝ) :
    distributionalComplexity c ≤ randomizedComplexity c := by
  refine csSup_le (distValues_nonempty c) ?_
  rintro r ⟨μ, hμ, rfl⟩
  refine le_csInf (randValues_nonempty c) ?_
  rintro s ⟨q, hq, rfl⟩
  exact ciInf_distCost_le_ciSup_randCost c hμ hq

end Basic

section Strong

variable [Nonempty A] [Nonempty I]

/-- The linear map sending a distribution over algorithms to its vector of expected costs. -/
def randCostMap (c : A → I → ℝ) : (A → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun q := randCost c q
  map_add' q q' := by
    funext i; simp only [randCost, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  map_smul' t q := by
    funext i
    simp only [randCost, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

omit [Nonempty I] in
/-- A continuous linear functional on `I → ℝ` is given by its values on the basis vectors. -/
lemma strongDual_apply_eq_sum (f : StrongDual ℝ (I → ℝ)) (z : I → ℝ) :
    f z = ∑ i, z i * f (Pi.single i 1) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : (Pi.single i (z i) : I → ℝ) = z i • (Pi.single i 1 : I → ℝ) := by
    funext j
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  rw [hsingle, map_smul, smul_eq_mul]

/-- **Strong duality** (the hard direction of Yao's principle). -/
theorem randomizedComplexity_le_distributionalComplexity (c : A → I → ℝ) :
    randomizedComplexity c ≤ distributionalComplexity c := by
  classical
  by_contra hcon
  push_neg at hcon
  set D := distributionalComplexity c with hD
  set R := randomizedComplexity c with hR
  set v : ℝ := (D + R) / 2 with hv
  have hDv : D < v := by simp only [hv]; linarith
  have hvR : v < R := by simp only [hv]; linarith
  -- the compact convex set of achievable cost vectors of randomized algorithms
  set K : Set (I → ℝ) := (randCostMap c) '' (stdSimplex ℝ A) with hK
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ A).linear_image (randCostMap c)
  have hKcomp : IsCompact K :=
    (isCompact_stdSimplex A).image (randCostMap c).continuous_of_finiteDimensional
  -- the closed convex set of vectors all of whose coordinates are at most `v`
  set T : Set (I → ℝ) := ⋂ i, {z : I → ℝ | z i ≤ v} with hT
  have hTconv : Convex ℝ T := by
    refine convex_iInter fun i => ?_
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hsv : s * v + t * v = v := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  have hTclosed : IsClosed T :=
    isClosed_iInter fun i => isClosed_Iic.preimage (continuous_apply i)
  -- they are disjoint
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro x ⟨q, hq, rfl⟩ hxT
    have hle : R ≤ ⨆ i, randCost c q i :=
      csInf_le (bddBelow_randValues c) ⟨q, hq, rfl⟩
    have : v < ⨆ i, randCost c q i := lt_of_lt_of_le hvR hle
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup this
    have : (randCostMap c) q i ≤ v := by
      have := Set.mem_iInter.mp hxT i
      simpa using this
    exact absurd this (not_le.mpr hi)
  obtain ⟨f, u, w, hfK, huw, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp hTconv hTclosed hdisj
  set g : I → ℝ := fun i => f (Pi.single i 1) with hg
  have hrep : ∀ z : I → ℝ, f z = ∑ i, z i * g i := fun z => strongDual_apply_eq_sum f z
  set S : ℝ := ∑ i, g i with hS
  have hconstT : (fun _ : I => v) ∈ T := by
    refine Set.mem_iInter.mpr fun i => ?_
    simp
  have hfconst : f (fun _ : I => v) = v * S := by
    rw [hrep]
    rw [hS, Finset.mul_sum]
  have hwlt : w < v * S := hfconst ▸ hfT _ hconstT
  -- each coordinate of `g` is nonpositive
  have hgnonpos : ∀ i, g i ≤ 0 := by
    intro i
    by_contra hpos
    push_neg at hpos
    set lam : ℝ := (v * S - w + 1) / g i with hlam
    have hlampos : 0 < lam := by
      apply div_pos _ hpos
      linarith
    set z : I → ℝ := fun j => if j = i then v - lam else v with hz
    have hzT : z ∈ T := by
      refine Set.mem_iInter.mpr fun j => ?_
      simp only [Set.mem_setOf_eq, hz]
      split_ifs with h
      · linarith
      · exact le_refl v
    have hfz : f z = v * S - lam * g i := by
      rw [hrep]
      have : ∑ j, z j * g j = ∑ j, (v * g j - (if j = i then lam * g j else 0)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hz]
        split_ifs with h
        · ring
        · ring
      rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ i
        (fun j => lam * g j)]
      simp [hS]
    have hne : g i ≠ 0 := ne_of_gt hpos
    have hcalc : lam * g i = v * S - w + 1 := by
      rw [hlam]
      field_simp
    have := hfT z hzT
    rw [hfz, hcalc] at this
    linarith
  have hSnonpos : S ≤ 0 := Finset.sum_nonpos fun i _ => hgnonpos i
  -- `K` is nonempty, which forces `S < 0`
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have ha₀K : (randCostMap c) (Pi.single a₀ 1) ∈ K :=
    ⟨Pi.single a₀ 1, single_mem_stdSimplex ℝ a₀, rfl⟩
  have hSneg : S < 0 := by
    rcases lt_or_eq_of_le hSnonpos with h | h
    · exact h
    · exfalso
      have hsum : ∑ i, g i = 0 := by rw [← hS]; exact h
      have hgz : ∀ i, g i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hgnonpos j).mp hsum i
          (Finset.mem_univ i)
      have hf0 : ∀ z : I → ℝ, f z = 0 := by
        intro z; rw [hrep]; simp [hgz]
      have h1 : f ((randCostMap c) (Pi.single a₀ 1)) < u := hfK _ ha₀K
      have h2 : w < f (fun _ : I => v) := hfT _ hconstT
      rw [hf0] at h1 h2
      linarith
  -- build the optimal input distribution
  set μ : I → ℝ := fun i => g i / S with hμdef
  have hμsimplex : μ ∈ stdSimplex ℝ I := by
    constructor
    · intro i
      exact div_nonneg_of_nonpos (hgnonpos i) hSnonpos
    · simp only [hμdef]
      rw [← Finset.sum_div, ← hS, div_self (ne_of_lt hSneg)]
  have hkey : ∀ a : A, v ≤ distCost c μ a := by
    intro a
    have haK : (randCostMap c) (Pi.single a 1) ∈ K :=
      ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, rfl⟩
    have h1 : f ((randCostMap c) (Pi.single a 1)) < u := hfK _ haK
    have hcoord : ∀ i, (randCostMap c) (Pi.single a 1) i = c a i := by
      intro i
      simp [randCostMap, randCost, Finset.sum_ite_eq' Finset.univ a, Pi.single_apply]
    have h2 : f ((randCostMap c) (Pi.single a 1)) = ∑ i, c a i * g i := by
      rw [hrep]
      exact Finset.sum_congr rfl fun i _ => by rw [hcoord i]
    have h3 : ∑ i, c a i * g i < v * S := by linarith
    have h4 : distCost c μ a = (∑ i, c a i * g i) / S := by
      simp only [distCost, hμdef]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h4]
    rw [le_div_iff_of_neg hSneg]
    linarith
  have hmem : (⨅ a, distCost c μ a) ∈ distValues c := ⟨μ, hμsimplex, rfl⟩
  have hge : v ≤ ⨅ a, distCost c μ a := le_ciInf hkey
  have hle : (⨅ a, distCost c μ a) ≤ D := le_csSup (bddAbove_distValues c) hmem
  linarith

end Strong

/-- **Yao's minimax principle**: for any cost matrix `c` assigning to each deterministic
algorithm `a` and input `i` a cost `c a i`, the randomized complexity
(the minimum over distributions `q` on deterministic algorithms of the worst-case expected cost)
equals the distributional complexity
(the maximum over input distributions `μ` of the best expected cost of a deterministic
algorithm against `μ`). -/
theorem yao_principle {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]
    (c : A → I → ℝ) : randomizedComplexity c = distributionalComplexity c :=
  le_antisymm (randomizedComplexity_le_distributionalComplexity c)
    (distributionalComplexity_le_randomizedComplexity c)

/-- Sanity check for the definitions: if every algorithm costs `k` on every input, then the
randomized complexity is `k`. -/
theorem randomizedComplexity_const {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]
    (k : ℝ) : randomizedComplexity (fun (_ : A) (_ : I) => k) = k := by
  have hval : ∀ q ∈ stdSimplex ℝ A, (⨆ i : I, randCost (fun (_ : A) (_ : I) => k) q i) = k := by
    intro q hq
    have hq' : ∀ i : I, randCost (fun (_ : A) (_ : I) => k) q i = k := by
      intro i
      simp only [randCost, ← Finset.sum_mul, hq.2, one_mul]
    simp only [hq', ciSup_const]
  have hset : randValues (fun (_ : A) (_ : I) => k) = {k} := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hval q hq
    · rintro rfl
      obtain ⟨a⟩ := ‹Nonempty A›
      exact ⟨Pi.single a 1, single_mem_stdSimplex ℝ a,
        (hval _ (single_mem_stdSimplex ℝ a)).symm⟩
  rw [randomizedComplexity, hset, csInf_singleton]

/-- Sanity check for the definitions: if every algorithm costs `k` on every input, then the
distributional complexity is `k`. -/
theorem distributionalComplexity_const {A I : Type*} [Fintype A] [Fintype I] [Nonempty A]
    [Nonempty I] (k : ℝ) : distributionalComplexity (fun (_ : A) (_ : I) => k) = k := by
  rw [← yao_principle, randomizedComplexity_const]

end CS

