import Mathlib

/-!
# Nondeterministic small-space machines (branching-program model)

This file sets up a model of nondeterministic space-bounded computation on
inputs of a fixed length `n`, in the style of nondeterministic branching
programs: a machine has a finite state set `S`, each state may read (query) one
bit of the input, and the successor states are given by a relation depending on
the state and the queried bit.  The *space* used by such a machine is
`log₂ |S|`, so polynomially many states corresponds to logarithmic space.

Machines are value-producing (`out : S → Option α`), which lets us build them
with monadic combinators (`pure`, `bind`, `guess`, `query`, `fail`).
-/

open scoped Classical

namespace CS

/-- A nondeterministic machine on inputs of length `n`, producing values in `α`.

`label s` says which input bit (if any) is read at state `s`; `next s b` is the
set of possible successors of `s` when the bit read has value `b`; `out s` is
the value output if the computation halts at `s`. -/
structure Mach (n : ℕ) (α : Type) : Type 1 where
  S : Type
  fintypeS : Fintype S
  start : S
  label : S → Option (Fin n)
  next : S → Bool → Set S
  out : S → Option α

attribute [instance] Mach.fintypeS

namespace Mach

variable {n : ℕ} {α β : Type}

/-- The bit visible at state `s` on input `x` (`false` if `s` reads nothing). -/
def bit (M : Mach n α) (x : Fin n → Bool) (s : M.S) : Bool :=
  (M.label s).elim false x

/-- One computation step of `M` on input `x`. -/
def step (M : Mach n α) (x : Fin n → Bool) (u v : M.S) : Prop :=
  v ∈ M.next u (M.bit x u)

/-- Reachability in the configuration graph of `M` on input `x`. -/
def reach (M : Mach n α) (x : Fin n → Bool) : M.S → M.S → Prop :=
  Relation.ReflTransGen (M.step x)

/-- The set of values `M` can output on input `x`. -/
def run (M : Mach n α) (x : Fin n → Bool) : Set α :=
  {a | ∃ v, M.reach x M.start v ∧ M.out v = some a}

/-- The number of states of `M` (its space is the logarithm of this). -/
def size (M : Mach n α) : ℕ := Fintype.card M.S

/-! ### Basic combinators -/

/-- The machine that immediately outputs `a`. -/
def ret (a : α) : Mach n α where
  S := Unit
  fintypeS := inferInstance
  start := ()
  label := fun _ => none
  next := fun _ _ => ∅
  out := fun _ => some a

/-- The machine with no accepting computation. -/
def fail : Mach n α where
  S := Unit
  fintypeS := inferInstance
  start := ()
  label := fun _ => none
  next := fun _ _ => ∅
  out := fun _ => none

/-- The machine that reads input bit `i` and outputs it. -/
def query (i : Fin n) : Mach n Bool where
  S := Option Bool
  fintypeS := inferInstance
  start := none
  label := fun s => match s with | none => some i | some _ => none
  next := fun s b => match s with | none => {some b} | some _ => ∅
  out := fun s => s

/-- The machine that nondeterministically outputs an element of `β`. -/
def guess (β : Type) [Fintype β] : Mach n β where
  S := Option β
  fintypeS := inferInstance
  start := none
  label := fun _ => none
  next := fun s _ => match s with | none => Set.range some | some _ => ∅
  out := fun s => s

/-- Sequential composition: run `M`, and on output `a` continue with `f a`. -/
def bnd (M : Mach n α) [Fintype α] (f : α → Mach n β) : Mach n β where
  S := M.S ⊕ (Σ a : α, (f a).S)
  fintypeS := by
    haveI : Fintype M.S := M.fintypeS
    haveI : ∀ a : α, Fintype (f a).S := fun a => (f a).fintypeS
    infer_instance
  start := Sum.inl M.start
  label := Sum.elim M.label (fun p => (f p.1).label p.2)
  next := fun u b => match u with
    | Sum.inl s => (Sum.inl '' (M.next s b)) ∪ {t | ∃ a, M.out s = some a ∧ t = Sum.inr ⟨a, (f a).start⟩}
    | Sum.inr p => (fun t => Sum.inr ⟨p.1, t⟩) '' ((f p.1).next p.2 b)
  out := Sum.elim (fun _ => none) (fun p => (f p.1).out p.2)

/-! ### Semantics of the combinators -/

@[simp] theorem run_ret (a : α) (x : Fin n → Bool) : (ret a : Mach n α).run x = {a} := by
  ext c
  constructor
  · rintro ⟨v, -, hv⟩
    simpa [ret] using hv.symm
  · rintro rfl
    exact ⟨(), Relation.ReflTransGen.refl, rfl⟩

@[simp] theorem run_fail (x : Fin n → Bool) : (fail : Mach n α).run x = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨v, -, hv⟩
  exact absurd hv (by simp [fail])

@[simp] theorem run_query (i : Fin n) (x : Fin n → Bool) :
    (query i).run x = {x i} := by
  ext c
  constructor
  · rintro ⟨v, hv, hout⟩
    rcases Relation.ReflTransGen.cases_head hv with h | ⟨w, hw, hrest⟩
    · exact absurd hout (by rw [← h]; simp [query])
    · have hw' : w = some (x i) := by
        simpa [query, step, bit, Mach.bit] using hw
      subst hw'
      rcases Relation.ReflTransGen.cases_head hrest with h | ⟨z, hz, -⟩
      · rw [← h] at hout; simpa [query] using hout.symm
      · exact absurd hz (by simp [query, step])
  · rintro rfl
    refine ⟨some (x i), Relation.ReflTransGen.single ?_, rfl⟩
    simp [query, step, Mach.bit]

@[simp] theorem run_guess (β : Type) [Fintype β] (x : Fin n → Bool) :
    (guess β : Mach n β).run x = Set.univ := by
  ext c
  simp only [Set.mem_univ, iff_true]
  refine ⟨some c, Relation.ReflTransGen.single ?_, rfl⟩
  simp [guess, step]

/-! ### Semantics of `bnd` -/

section Bind

variable (M : Mach n α) [Fintype α] (f : α → Mach n β) (x : Fin n → Bool)

theorem step_bnd_inl {u v : M.S} (h : M.step x u v) :
    (bnd M f).step x (Sum.inl u) (Sum.inl v) := by
  refine Or.inl ⟨v, h, rfl⟩

theorem step_bnd_inr {a : α} {u v : (f a).S} (h : (f a).step x u v) :
    (bnd M f).step x (Sum.inr ⟨a, u⟩) (Sum.inr ⟨a, v⟩) := by
  exact ⟨v, h, rfl⟩

theorem reach_bnd_inl {u v : M.S} (h : M.reach x u v) :
    (bnd M f).reach x (Sum.inl u) (Sum.inl v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (step_bnd_inl M f x hstep)

theorem reach_bnd_inr {a : α} {u v : (f a).S} (h : (f a).reach x u v) :
    (bnd M f).reach x (Sum.inr ⟨a, u⟩) (Sum.inr ⟨a, v⟩) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (step_bnd_inr M f x hstep)

/-- Description of the states reachable in `bnd M f`. -/
theorem reach_bnd_iff (w : (bnd M f).S) (h : (bnd M f).reach x (bnd M f).start w) :
    (∃ u, w = Sum.inl u ∧ M.reach x M.start u) ∨
      (∃ a u, w = Sum.inr ⟨a, u⟩ ∧ a ∈ M.run x ∧ (f a).reach x (f a).start u) := by
  induction h with
  | refl => exact Or.inl ⟨M.start, rfl, Relation.ReflTransGen.refl⟩
  | @tail v w _ hstep ih =>
      rcases ih with ⟨u, rfl, hu⟩ | ⟨a, u, rfl, ha, hu⟩
      · rcases hstep with hstep | hstep
        · obtain ⟨t, ht, rfl⟩ := hstep
          exact Or.inl ⟨t, rfl, hu.tail ht⟩
        · obtain ⟨a, hout, rfl⟩ := hstep
          exact Or.inr ⟨a, (f a).start, rfl, ⟨u, hu, hout⟩, Relation.ReflTransGen.refl⟩
      · obtain ⟨t, ht, rfl⟩ := hstep
        exact Or.inr ⟨a, t, rfl, ha, hu.tail ht⟩

theorem run_bnd : (bnd M f).run x = ⋃ a ∈ M.run x, (f a).run x := by
  ext b
  constructor
  · rintro ⟨w, hw, hout⟩
    rcases reach_bnd_iff M f x w hw with ⟨u, rfl, -⟩ | ⟨a, u, rfl, ha, hu⟩
    · exact absurd hout (by simp [bnd])
    · exact Set.mem_biUnion ha ⟨u, hu, hout⟩
  · intro hb
    simp only [Set.mem_iUnion, exists_prop] at hb
    obtain ⟨a, ⟨u, hu, hua⟩, ⟨v, hv, hvb⟩⟩ := hb
    refine ⟨Sum.inr ⟨a, v⟩, ?_, hvb⟩
    have h1 : (bnd M f).reach x (bnd M f).start (Sum.inl u) := reach_bnd_inl M f x hu
    have h2 : (bnd M f).step x (Sum.inl u) (Sum.inr ⟨a, (f a).start⟩) :=
      Or.inr ⟨a, hua, rfl⟩
    exact (h1.tail h2).trans (reach_bnd_inr M f x hv)

end Bind

/-! ### Sizes -/

@[simp] theorem size_ret (a : α) : (ret a : Mach n α).size = 1 := rfl
@[simp] theorem size_fail : (fail : Mach n α).size = 1 := rfl
@[simp] theorem size_query (i : Fin n) : (query i).size = 3 := by
  simp [size, query]
@[simp] theorem size_guess (β : Type) [Fintype β] :
    (guess β : Mach n β).size = Fintype.card β + 1 := by
  simp [size, guess]

theorem size_bnd (M : Mach n α) [Fintype α] (f : α → Mach n β) :
    (bnd M f).size = M.size + ∑ a : α, (f a).size := by
  classical
  haveI : Fintype M.S := M.fintypeS
  haveI : ∀ a : α, Fintype (f a).S := fun a => (f a).fintypeS
  have h : Fintype.card ((bnd M f).S) = Fintype.card (M.S ⊕ Σ a : α, (f a).S) := by
    congr 1 <;> exact Subsingleton.elim _ _
  have hp : ∀ (a : α) (i : Fintype (f a).S), @Fintype.card (f a).S i = (f a).size := by
    intro a i; simp only [size]; congr 1
  have hM : ∀ (i : Fintype M.S), @Fintype.card M.S i = M.size := by
    intro i; simp only [size]; congr 1
  simp only [size, hp, hM] at h ⊢
  rw [h, Fintype.card_sum, Fintype.card_sigma, hM, hp]
  simp only [hp, hM]

end Mach

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

