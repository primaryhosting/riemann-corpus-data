/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-!
## Setting

A weighted digraph on a finite vertex type `V` is given by a weight function
`w : V → V → ℕ∞`.  Weights live in `ℕ∞ = WithTop ℕ`, so they are automatically
nonnegative, and `w x y = ⊤` encodes "there is no edge from `x` to `y`".
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `RWalk w S s v l`: there is a walk from `s` to `v` of total weight `l`
all of whose vertices, **except possibly the final vertex `v`**, lie in `S`. -/
inductive RWalk (w : V → V → ℕ∞) (S : Finset V) (s : V) : V → ℕ∞ → Prop
  | nil : RWalk w S s s 0
  | cons {x v : V} {l : ℕ∞} : RWalk w S s x l → x ∈ S → RWalk w S s v (l + w x v)

/-- `Walk w s v l`: there is a walk from `s` to `v` of total weight `l`
(no restriction on the intermediate vertices). -/
def Walk (w : V → V → ℕ∞) (s v : V) (l : ℕ∞) : Prop := RWalk w Finset.univ s v l

/-- The graph distance from `s` to `v`: the infimum of the weights of all walks. -/
noncomputable def gdist (w : V → V → ℕ∞) (s v : V) : ℕ∞ := sInf {l | Walk w s v l}

omit [Fintype V] [DecidableEq V] in
theorem RWalk.mono {w : V → V → ℕ∞} {S T : Finset V} {s v : V} {l : ℕ∞}
    (hST : S ⊆ T) (h : RWalk w S s v l) : RWalk w T s v l := by
  induction h with
  | nil => exact RWalk.nil
  | cons _ hx ih => exact ih.cons (hST hx)

omit [DecidableEq V] in
theorem RWalk.toWalk {w : V → V → ℕ∞} {S : Finset V} {s v : V} {l : ℕ∞}
    (h : RWalk w S s v l) : Walk w s v l :=
  h.mono (Finset.subset_univ S)

omit [DecidableEq V] in
theorem Walk.nil' (w : V → V → ℕ∞) (s : V) : Walk w s s 0 := RWalk.nil

omit [DecidableEq V] in
theorem Walk.cons' {w : V → V → ℕ∞} {s x v : V} {l : ℕ∞} (h : Walk w s x l) :
    Walk w s v (l + w x v) := RWalk.cons h (Finset.mem_univ x)

/-!
## The algorithm

`dijkstraAux w n Q d` performs (at most) `n` rounds of Dijkstra's algorithm.
`Q` is the set of vertices not yet finalized, and `d` is the current tentative
distance array.  Each round selects a vertex `u ∈ Q` of minimal tentative
distance, removes it from `Q`, and relaxes all edges out of `u`.
-/

/-- One round of Dijkstra: relax all edges out of `u`. -/
noncomputable def relax (w : V → V → ℕ∞) (d : V → ℕ∞) (u : V) : V → ℕ∞ :=
  fun v => min (d v) (d u + w u v)

/-- The main loop of Dijkstra's algorithm, run for `n` rounds. -/
noncomputable def dijkstraAux (w : V → V → ℕ∞) :
    ℕ → Finset V → (V → ℕ∞) → (V → ℕ∞)
  | 0, _, d => d
  | (n + 1), Q, d =>
      if h : Q.Nonempty then
        dijkstraAux w n (Q.erase (Finset.exists_min_image Q d h).choose)
          (relax w d (Finset.exists_min_image Q d h).choose)
      else d

/-- **Dijkstra's algorithm**: the array of tentative distances from `s`,
after all vertices have been finalized. -/
noncomputable def dijkstra (w : V → V → ℕ∞) (s : V) : V → ℕ∞ :=
  dijkstraAux w (Fintype.card V) Finset.univ (fun v => if v = s then 0 else ⊤)

/-!
## The loop invariant
-/

/-- The loop invariant of Dijkstra's algorithm, where `S` is the set of
already-finalized vertices. -/
structure Inv (w : V → V → ℕ∞) (s : V) (S : Finset V) (d : V → ℕ∞) : Prop where
  /-- `d v` is a lower bound for all walks through `S`. -/
  lb : ∀ (v : V) (l : ℕ∞), RWalk w S s v l → d v ≤ l
  /-- `d v`, when finite, is realized by a walk through `S`. -/
  attained : ∀ (v : V), d v ≠ ⊤ → RWalk w S s v (d v)
  /-- For finalized vertices, `d v` is already the true distance. -/
  final : ∀ v ∈ S, ∀ (l : ℕ∞), Walk w s v l → d v ≤ l

theorem inv_init (w : V → V → ℕ∞) (s : V) :
    Inv w s (Finset.univ : Finset V)ᶜ (fun v => if v = s then 0 else ⊤) := by
  have hcompl : (Finset.univ : Finset V)ᶜ = (∅ : Finset V) := by simp
  rw [hcompl]
  constructor
  · intro v l h
    cases h with
    | nil => simp
    | cons _ hx => exact absurd hx (Finset.notMem_empty _)
  · intro v hv
    by_cases hvs : v = s
    · subst hvs; simpa using RWalk.nil
    · simp [hvs] at hv
  · intro v hv
    exact absurd hv (Finset.notMem_empty _)

/-- Key step: the minimal-tentative-distance unfinalized vertex already has the
correct distance. -/
theorem min_vertex_correct (w : V → V → ℕ∞) (s : V) (Q : Finset V) (d : V → ℕ∞)
    (hd : Inv w s Qᶜ d) (u : V) (hmin : ∀ v ∈ Q, d u ≤ d v) :
    ∀ (v : V) (l : ℕ∞), Walk w s v l → v ∈ Q → d u ≤ l := by
  intro v l h
  induction h with
  | nil =>
      intro hs
      exact le_trans (hmin _ hs) (hd.lb _ 0 RWalk.nil)
  | @cons x v l hxw _ ih =>
      intro hv
      by_cases hxS : x ∈ Qᶜ
      · have hdx : d x ≤ l := hd.final x hxS l hxw
        by_cases hdxtop : d x = ⊤
        · rw [hdxtop] at hdx
          have : l = ⊤ := top_le_iff.mp hdx
          simp [this]
        · have h1 : RWalk w Qᶜ s v (d x + w x v) := (hd.attained x hdxtop).cons hxS
          have h2 : d v ≤ d x + w x v := hd.lb _ _ h1
          calc d u ≤ d v := hmin _ hv
            _ ≤ d x + w x v := h2
            _ ≤ l + w x v := by gcongr
      · have hxQ : x ∈ Q := by simpa using hxS
        exact le_trans (ih hxQ) le_self_add

/-- One round of Dijkstra's algorithm preserves the loop invariant. -/
theorem Inv.step (w : V → V → ℕ∞) (s : V) (Q : Finset V) (d : V → ℕ∞)
    (hd : Inv w s Qᶜ d) (u : V) (huQ : u ∈ Q) (hmin : ∀ v ∈ Q, d u ≤ d v) :
    Inv w s (Q.erase u)ᶜ (relax w d u) := by
  rw [Finset.compl_erase]
  set S : Finset V := Qᶜ
  set d' : V → ℕ∞ := relax w d u with hd'
  -- `d u` is the true distance to `u`
  have hAu : ∀ (l : ℕ∞), Walk w s u l → d u ≤ l := fun l h =>
    min_vertex_correct w s Q d hd u hmin u l h huQ
  -- for already-finalized `x`, relaxation changes nothing
  have hfix : ∀ x ∈ S, d' x = d x := by
    intro x hx
    have : d x ≤ d u + w u x := by
      by_cases hdu : d u = ⊤
      · simp [hdu]
      · have h1 : Walk w s u (d u) := (hd.attained u hdu).toWalk
        exact hd.final x hx _ h1.cons'
    simp [hd', relax, min_eq_left this]
  have hdu' : d' u = d u := by
    simp [hd', relax]
  -- `d'` is realized by walks through `insert u S`
  have hatt : ∀ (v : V), d' v ≠ ⊤ → RWalk w (insert u S) s v (d' v) := by
    intro v hv
    by_cases hle : d v ≤ d u + w u v
    · have he : d' v = d v := by simp [hd', relax, min_eq_left hle]
      rw [he]
      rw [he] at hv
      exact (hd.attained v hv).mono (Finset.subset_insert u S)
    · have he : d' v = d u + w u v := by
        simp [hd', relax, min_eq_right (not_le.mp hle).le]
      rw [he]
      rw [he] at hv
      have hdu : d u ≠ ⊤ := by
        intro h; rw [h] at hv; simp at hv
      exact ((hd.attained u hdu).mono (Finset.subset_insert u S)).cons
        (Finset.mem_insert_self u S)
  -- the relaxation inequality along every edge out of `insert u S`
  have hrelax : ∀ x ∈ insert u S, ∀ (v : V), d' v ≤ d' x + w x v := by
    intro x hx v
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · rw [hdu']
      exact min_le_right _ _
    · rw [hfix x hxS]
      by_cases hdx : d x = ⊤
      · simp [hdx]
      · have h1 : RWalk w S s v (d x + w x v) := (hd.attained x hdx).cons hxS
        exact le_trans (min_le_left _ _) (hd.lb _ _ h1)
  refine ⟨?_, hatt, ?_⟩
  · intro v l h
    induction h with
    | nil => exact le_trans (min_le_left _ _) (hd.lb _ 0 RWalk.nil)
    | @cons x v l _ hx ih =>
        exact le_trans (hrelax x hx v) (by gcongr)
  · intro v hv l hl
    rcases Finset.mem_insert.mp hv with rfl | hvS
    · rw [hdu']; exact hAu l hl
    · rw [hfix v hvS]; exact hd.final v hvS l hl

/-- The main loop preserves and completes the invariant. -/
theorem dijkstraAux_inv (w : V → V → ℕ∞) (s : V) :
    ∀ (n : ℕ) (Q : Finset V) (d : V → ℕ∞), Q.card ≤ n → Inv w s Qᶜ d →
      Inv w s Finset.univ (dijkstraAux w n Q d) := by
  intro n
  induction n with
  | zero =>
      intro Q d hcard hd
      have hQ : Q = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hQ
      simpa [dijkstraAux] using hd
  | succ n ih =>
      intro Q d hcard hd
      rw [dijkstraAux]
      by_cases h : Q.Nonempty
      · rw [dif_pos h]
        obtain ⟨huQ, hmin⟩ := (Finset.exists_min_image Q d h).choose_spec
        set u := (Finset.exists_min_image Q d h).choose
        refine ih _ _ ?_ (Inv.step w s Q d hd u huQ hmin)
        have := Finset.card_erase_of_mem huQ
        omega
      · rw [dif_neg h]
        have hQ : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        subst hQ
        simpa using hd

/-!
## Correctness
-/

/-- **Dijkstra's algorithm is correct**: on a finite digraph with nonnegative
edge weights (valued in `ℕ∞`, with `⊤` meaning "no edge"), the array computed by
`dijkstra w s` is exactly the array of shortest-path distances from `s`, i.e.
for every vertex `v` it equals the infimum of the weights of all walks from `s`
to `v` (which is `⊤` when `v` is unreachable). -/
theorem dijkstra_correct (w : V → V → ℕ∞) (s : V) (v : V) :
    dijkstra w s v = gdist w s v := by
  have hinv : Inv w s Finset.univ (dijkstra w s) := by
    apply dijkstraAux_inv w s
    · exact le_of_eq (Finset.card_univ)
    · exact inv_init w s
  apply le_antisymm
  · apply le_sInf
    intro l hl
    exact hinv.lb v l hl
  · by_cases hv : dijkstra w s v = ⊤
    · rw [hv]; exact le_top
    · exact sInf_le (hinv.attained v hv)

/-- Restatement: the algorithm's output is a lower bound for every walk. -/
theorem dijkstra_le_of_walk (w : V → V → ℕ∞) (s v : V) (l : ℕ∞) (h : Walk w s v l) :
    dijkstra w s v ≤ l := by
  rw [dijkstra_correct]
  exact sInf_le h

/-- Restatement: when finite, the algorithm's output is realized by an actual walk. -/
theorem dijkstra_attained (w : V → V → ℕ∞) (s v : V) (h : dijkstra w s v ≠ ⊤) :
    Walk w s v (dijkstra w s v) := by
  have hinv : Inv w s Finset.univ (dijkstra w s) := by
    apply dijkstraAux_inv w s
    · exact le_of_eq (Finset.card_univ)
    · exact inv_init w s
  exact hinv.attained v h

end CS

