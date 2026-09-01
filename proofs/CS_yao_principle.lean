import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to be the very first command of a file, so this header
module docstring appears immediately after it.)

## Contents

Yao's minimax principle: for a finite set `A` of deterministic algorithms, a finite set `I` of
inputs, and a cost function `c : A → I → ℝ`, the optimal randomized complexity
(minimum over distributions `p` on `A` of the worst case over inputs of the expected cost)
equals the optimal distributional complexity (maximum over distributions `q` on `I` of the best
over deterministic algorithms of the expected cost).

The easy direction, `CS.distCost_le_randCost`, is the inequality that is actually used to prove
randomized lower bounds.  The converse uses the minimax theorem for finite two-player zero-sum
games, which is proved here from the geometric Hahn–Banach separation theorem
(`geometric_hahn_banach_open`) together with compactness of the standard simplex.
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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over
deterministic algorithms, run on the input `i`. -/
def randCostOn (c : A → I → ℝ) (p : A → ℝ) (i : I) : ℝ := ∑ a, p a * c a i

/-- The expected cost of the deterministic algorithm `a` on a random input drawn from `q`. -/
def distCostOn (c : A → I → ℝ) (q : I → ℝ) (a : A) : ℝ := ∑ i, q i * c a i

/-- The randomized complexity of the randomized algorithm `p`: the worst case over inputs of
the expected cost. -/
noncomputable def randCost (c : A → I → ℝ) (p : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (randCostOn c p)

/-- The distributional complexity of the input distribution `q`: the least expected cost of a
deterministic algorithm against `q`. -/
noncomputable def distCost (c : A → I → ℝ) (q : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (distCostOn c q)

omit [Nonempty A] [Fintype I] [Nonempty I] in
lemma sum_le_of_mem_stdSimplex {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (g : A → ℝ) (M : ℝ)
    (h : ∀ a, g a ≤ M) : ∑ a, p a * g a ≤ M := by
  calc ∑ a, p a * g a ≤ ∑ a, p a * M :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hp.1 a)
    _ = M := by rw [← Finset.sum_mul, hp.2, one_mul]

omit [Nonempty A] [Fintype I] [Nonempty I] in
lemma le_sum_of_mem_stdSimplex {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (g : A → ℝ) (m : ℝ)
    (h : ∀ a, m ≤ g a) : m ≤ ∑ a, p a * g a := by
  calc m = ∑ a, p a * m := by rw [← Finset.sum_mul, hp.2, one_mul]
    _ ≤ ∑ a, p a * g a :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hp.1 a)

variable (c : A → I → ℝ)

/-- The easy direction of Yao's principle: the distributional complexity of any input
distribution is a lower bound for the randomized complexity of any randomized algorithm. -/
theorem distCost_le_randCost {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A)
    {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) : distCost c q ≤ randCost c p := by
  have h1 : distCost c q ≤ ∑ a, p a * distCostOn c q a :=
    le_sum_of_mem_stdSimplex hp _ _ fun a => Finset.inf'_le _ (Finset.mem_univ a)
  have h2 : ∑ a, p a * distCostOn c q a = ∑ i, q i * randCostOn c p i := by
    simp only [distCostOn, randCostOn, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  have h3 : ∑ i, q i * randCostOn c p i ≤ randCost c p :=
    sum_le_of_mem_stdSimplex hq _ _ fun i => Finset.le_sup' _ (Finset.mem_univ i)
  linarith

omit [Nonempty A] in
lemma continuous_randCost : Continuous (randCost c) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  unfold randCostOn
  exact continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const

/-- An optimal randomized algorithm exists, by compactness of the simplex. -/
lemma exists_isMinOn_randCost :
    ∃ p ∈ stdSimplex ℝ A, ∀ p' ∈ stdSimplex ℝ A, randCost c p ≤ randCost c p' := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_stdSimplex A).exists_isMinOn
    ⟨Pi.single (Classical.arbitrary A) 1, single_mem_stdSimplex ℝ _⟩
    (continuous_randCost c).continuousOn
  exact ⟨p, hp, fun p' hp' => hmin hp'⟩

omit [Fintype I] [Nonempty A] [Nonempty I] in
lemma isLinearMap_randCostOn : IsLinearMap ℝ (fun p : A → ℝ => randCostOn c p) := by
  constructor
  · intro p p'; funext i; simp [randCostOn, add_mul, Finset.sum_add_distrib]
  · intro r p; funext i; simp [randCostOn, Finset.mul_sum, mul_assoc]

omit [Fintype I] [Nonempty A] [Nonempty I] in
lemma randCostOn_single (a : A) : randCostOn c (Pi.single a 1) = fun i => c a i := by
  funext i; simp [randCostOn, Pi.single_apply, Finset.sum_ite_eq']

/-- The minimax step: if no randomized algorithm has cost below `v`, then there is an input
distribution against which every deterministic algorithm costs at least `v`. -/
lemma exists_hard_distribution (v : ℝ)
    (hv : ∀ p ∈ stdSimplex ℝ A, v ≤ randCost c p) :
    ∃ q ∈ stdSimplex ℝ I, v ≤ distCost c q := by
  -- the compact convex set of achievable cost vectors, and the open convex "cheap" orthant
  set K : Set (I → ℝ) := (fun p : A → ℝ => randCostOn c p) '' (stdSimplex ℝ A) with hKdef
  set C : Set (I → ℝ) := Set.pi Set.univ (fun _ : I => Set.Iio v) with hCdef
  have hCopen : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Iio
  have hCconv : Convex ℝ C := convex_pi fun _ _ => convex_Iio v
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ A).is_linear_image (isLinearMap_randCostOn c)
  have hdisj : Disjoint C K := by
    rw [Set.disjoint_left]
    rintro y hy ⟨p, hp, rfl⟩
    have h1 : v ≤ Finset.univ.sup' Finset.univ_nonempty (randCostOn c p) := hv p hp
    have h2 : Finset.univ.sup' Finset.univ_nonempty (randCostOn c p) < v := by
      rw [Finset.sup'_lt_iff]
      exact fun i _ => hy i (Set.mem_univ i)
    linarith
  obtain ⟨f, u, hfC, hfK⟩ := geometric_hahn_banach_open hCconv hCopen hKconv hdisj
  -- coordinates of the separating functional
  set q : I → ℝ := fun i => f (Pi.single i 1) with hqdef
  have hf : ∀ y : I → ℝ, f y = ∑ i, y i * q i := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsi : (Pi.single i (y i) : I → ℝ) = y i • (Pi.single i 1 : I → ℝ) := by
      funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
    rw [hsi, map_smul]
    simp [hqdef]
  have hK0 : ∀ a : A, (fun i => c a i) ∈ K :=
    fun a => ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, randCostOn_single c a⟩
  have hlow : ∀ w : ℝ, w < v → f (fun _ : I => w) < u :=
    fun w hw => hfC _ fun i _ => hw
  have hhigh : ∀ a : A, u ≤ f (fun i => c a i) := fun a => hfK _ (hK0 a)
  -- the separating functional has nonnegative coefficients
  have hqnn : ∀ i, 0 ≤ q i := by
    intro i
    by_contra hneg
    push_neg at hneg
    have hS : f (fun _ : I => v - 1) < u := hlow (v - 1) (by linarith)
    set S := f (fun _ : I => v - 1) with hSdef
    set d : ℝ := -q i with hddef
    have hd : 0 < d := by rw [hddef]; linarith
    set t : ℝ := (u - S) / d + 1 with htdef
    have ht : 0 < t := by
      have : 0 < (u - S) / d := div_pos (by linarith) hd
      rw [htdef]; linarith
    have hy : ((fun _ : I => v - 1) - t • (Pi.single i 1 : I → ℝ)) ∈ C := by
      intro j _
      by_cases h : j = i
      · simp [h]; linarith
      · simp [h]
    have hlt := hfC _ hy
    rw [map_sub, map_smul] at hlt
    have hqi : f (Pi.single i 1 : I → ℝ) = q i := rfl
    rw [hqi] at hlt
    have htd : t * d = (u - S) + d := by rw [htdef]; field_simp
    simp only [smul_eq_mul] at hlt
    have hrw : S - t * q i = S + t * d := by rw [hddef]; ring
    linarith [hlt, htd]
  -- normalize the coefficients to an input distribution
  have hsnn : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => hqnn i
  have hs : 0 < ∑ i, q i := by
    rcases eq_or_lt_of_le hsnn with heq | hlt
    · exfalso
      have hz : ∀ i, q i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hqnn j).mp heq.symm i (Finset.mem_univ i)
      have hf0 : ∀ y : I → ℝ, f y = 0 := fun y => by rw [hf y]; simp [hz]
      have h1 : (0:ℝ) < u := by have := hlow (v - 1) (by linarith); rwa [hf0] at this
      have h2 : u ≤ 0 := by have := hhigh (Classical.arbitrary A); rwa [hf0] at this
      linarith
    · exact hlt
  set s := ∑ i, q i with hsdef
  have hvu : v * s ≤ u := by
    by_contra hcon
    push_neg at hcon
    set e := (v * s - u) / s with hedef
    have he : 0 < e := div_pos (by linarith) hs
    have h1 := hlow (v - e) (by linarith)
    rw [hf] at h1
    have h2 : ∑ i, (v - e) * q i = (v - e) * s := by rw [hsdef, Finset.mul_sum]
    rw [h2] at h1
    have h3 : e * s = v * s - u := by rw [hedef]; field_simp
    nlinarith [h1, h3]
  refine ⟨fun i => q i / s, ⟨fun i => div_nonneg (hqnn i) hs.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hsdef]; field_simp
  · apply Finset.le_inf'
    intro a _
    have h1 : u ≤ ∑ i, c a i * q i := by have := hhigh a; rwa [hf] at this
    have h2 : distCostOn c (fun i => q i / s) a = (∑ i, c a i * q i) / s := by
      rw [distCostOn, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, le_div_iff₀ hs]
    linarith

/-- The finite zero-sum game determined by `c` has a value: some real number `v` is
simultaneously the least randomized complexity and the greatest distributional complexity. -/
theorem exists_game_value :
    ∃ v : ℝ, IsLeast (randCost c '' stdSimplex ℝ A) v ∧
      IsGreatest (distCost c '' stdSimplex ℝ I) v := by
  obtain ⟨p₀, hp₀, hmin⟩ := exists_isMinOn_randCost c
  obtain ⟨q₀, hq₀, hge⟩ := exists_hard_distribution c (randCost c p₀) hmin
  refine ⟨randCost c p₀, ⟨⟨p₀, hp₀, rfl⟩, ?_⟩, ⟨⟨q₀, hq₀, ?_⟩, ?_⟩⟩
  · rintro w ⟨p, hp, rfl⟩
    exact hmin p hp
  · exact le_antisymm (distCost_le_randCost c hp₀ hq₀) hge
  · rintro w ⟨q, hq, rfl⟩
    exact distCost_le_randCost c hp₀ hq

/-- **Yao's minimax principle**.  For a finite set `A` of deterministic algorithms, a finite set
`I` of inputs and a cost function `c : A → I → ℝ`, the optimal randomized complexity — the
infimum over distributions `p` on algorithms of the worst-case expected cost — equals the optimal
distributional complexity — the supremum over distributions `q` on inputs of the least expected
cost of a deterministic algorithm.  Both are attained (see `CS.exists_game_value`). -/
theorem yao_principle (c : A → I → ℝ) :
    sInf (randCost c '' stdSimplex ℝ A) = sSup (distCost c '' stdSimplex ℝ I) := by
  obtain ⟨v, hleast, hgreatest⟩ := exists_game_value c
  rw [hleast.csInf_eq, hgreatest.csSup_eq]

end CS

