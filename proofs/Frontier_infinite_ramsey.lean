import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Filter

/-- **Infinite Ramsey theorem** for pairs and two colours:
every `2`-colouring `c` of the unordered pairs of natural numbers (encoded as a function
`c : ℕ → ℕ → Bool`, only evaluated on pairs `a < b`) admits an infinite set `S ⊆ ℕ` all of
whose pairs receive the same colour `k`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (k : Bool), S.Infinite ∧ ∀ a ∈ S, ∀ b ∈ S, a < b → c a b = k := by
  -- A nonprincipal ultrafilter on `ℕ`.
  set U : Ultrafilter ℕ := hyperfilter ℕ with hU
  -- `A k` is the set of points `a` whose "`k`-neighbourhood" is large.
  set A : Bool → Set ℕ := fun k => {a | {b | c a b = k} ∈ U} with hA
  have hcover : A true ∪ A false = Set.univ := by
    ext a
    simp only [hA, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases U.mem_or_compl_mem {b | c a b = true} with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have : {b | c a b = false} = {b | c a b = true}ᶜ := by
        ext b; simp
      rw [this]; exact h
  have huniv : (Set.univ : Set ℕ) ∈ U := Filter.univ_mem
  rw [← hcover] at huniv
  have hex : A true ∈ U ∨ A false ∈ U := (Ultrafilter.union_mem_iff).1 huniv
  obtain ⟨k, hk⟩ : ∃ k : Bool, A k ∈ U := by
    rcases hex with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  -- Key step: given a finite set `F` of points already chosen, all lying in `A k`,
  -- we can find a new point `b ∈ A k`, larger than all of `F`, joined to all of `F` in colour `k`.
  have key : ∀ F : Finset ℕ, ∃ b : ℕ, (∀ i ∈ F, i ∈ A k) →
      (b ∈ A k ∧ (∀ i ∈ F, c i b = k) ∧ ∀ i ∈ F, i < b) := by
    intro F
    by_cases hF : ∀ i ∈ F, i ∈ A k
    · have h1 : ∀ᶠ b in (U : Filter ℕ), b ∈ A k := hk
      have h2 : ∀ᶠ b in (U : Filter ℕ), ∀ i ∈ F, c i b = k := by
        rw [Filter.eventually_all_finset]
        intro i hi
        exact hF i hi
      have h3 : ∀ᶠ b in (U : Filter ℕ), ∀ i ∈ F, i < b := by
        have hcof : ∀ᶠ b in Filter.cofinite (α := ℕ), ∀ i ∈ F, i < b := by
          rw [Nat.cofinite_eq_atTop, Filter.eventually_all_finset]
          intro i _
          exact Filter.eventually_gt_atTop i
        exact hcof.filter_mono (by rw [hU]; exact Filter.hyperfilter_le_cofinite)
      obtain ⟨b, hb⟩ := ((h1.and h2).and h3).exists
      exact ⟨b, fun _ => ⟨hb.1.1, hb.1.2, hb.2⟩⟩
    · exact ⟨0, fun h => absurd h hF⟩
  choose next hnext using key
  -- Build the increasing sequence together with the finite sets of already chosen points.
  let g : ℕ → Finset ℕ := fun n => Nat.rec (∅ : Finset ℕ) (fun _ F => insert (next F) F) n
  let a : ℕ → ℕ := fun n => next (g n)
  have hg0 : g 0 = ∅ := rfl
  have hgs : ∀ n, g (n + 1) = insert (a n) (g n) := fun _ => rfl
  -- Invariant: every chosen point lies in `A k`.
  have hinv : ∀ n, ∀ i ∈ g n, i ∈ A k := by
    intro n
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
        intro i hi
        rw [hgs n, Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact (hnext (g n) ih).1
        · exact ih i hi
  have hstep : ∀ n, a n ∈ A k ∧ (∀ i ∈ g n, c i (a n) = k) ∧ ∀ i ∈ g n, i < a n :=
    fun n => hnext (g n) (hinv n)
  have hsub : ∀ m n, m ≤ n → g m ⊆ g n := by
    intro m n hmn
    induction n with
    | zero => simp [Nat.le_zero.mp hmn]
    | succ n ih =>
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · have := ih (Nat.lt_succ_iff.mp h)
          rw [hgs n]
          exact this.trans (Finset.subset_insert _ _)
        · have : m = n + 1 := le_antisymm hmn h
          subst this
          exact Finset.Subset.refl _
  have hmem : ∀ m n, m < n → a m ∈ g n := by
    intro m n hmn
    have : a m ∈ g (m + 1) := by rw [hgs m]; exact Finset.mem_insert_self _ _
    exact hsub (m + 1) n hmn this
  have hlt : ∀ m n, m < n → a m < a n := fun m n hmn => (hstep n).2.2 _ (hmem m n hmn)
  have hcol : ∀ m n, m < n → c (a m) (a n) = k := fun m n hmn => (hstep n).2.1 _ (hmem m n hmn)
  have hmono : StrictMono a := strictMono_nat_of_lt_succ (fun n => hlt n (n + 1) (Nat.lt_succ_self n))
  refine ⟨Set.range a, k, Set.infinite_range_of_injective hmono.injective, ?_⟩
  rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩ hxy
  have hmn : m < n := by
    by_contra h
    push_neg at h
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact absurd hxy (lt_irrefl _)
    · exact absurd hxy (not_lt.mpr (le_of_lt (hlt n m h')))
  exact hcol m n hmn

end Frontier

