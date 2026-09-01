import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
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

set_option grind.warning false

namespace Math2

/-!
## The minor relation

A *minor model* of `G` inside `H` assigns to every vertex `v` of `G` a nonempty connected
set of vertices of `H` (its *branch set*), so that distinct branch sets are disjoint and
adjacent vertices of `G` have adjacent representatives in their branch sets.
`G` is a minor of `H` exactly when such a model exists.
-/

/-- A minor model of `G` inside `H`: a family of pairwise disjoint, nonempty, connected
branch sets in `H`, indexed by the vertices of `G`, joined by an edge of `H` whenever the
corresponding vertices of `G` are adjacent. -/
structure MinorModel {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  /-- The branch set attached to a vertex of `G`. -/
  branch : V → Set W
  /-- Branch sets are nonempty. -/
  branch_nonempty : ∀ v, (branch v).Nonempty
  /-- Branch sets of distinct vertices are disjoint. -/
  branch_disjoint : ∀ v w, v ≠ w → Disjoint (branch v) (branch w)
  /-- Each branch set induces a connected subgraph of `H`. -/
  branch_connected : ∀ v, (H.induce (branch v)).Connected
  /-- Adjacent vertices of `G` have adjacent representatives. -/
  branch_adj : ∀ v w, G.Adj v w → ∃ a ∈ branch v, ∃ b ∈ branch w, H.Adj a b

/-- `IsMinor G H` says that `G` is a minor of `H`. -/
def IsMinor {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Nonempty (MinorModel G H)

/-- A singleton set induces a connected subgraph. -/
lemma connected_induce_singleton {W : Type*} (H : SimpleGraph W) (w : W) :
    (H.induce ({w} : Set W)).Connected := by
  haveI : Nonempty ({w} : Set W) := ⟨⟨w, rfl⟩⟩
  refine ⟨fun a b => ?_⟩
  have hab : a = b := Subtype.ext ((a.2 : a.val = w).trans (b.2 : b.val = w).symm)
  exact hab ▸ SimpleGraph.Reachable.refl a

/-- An injective adjacency-preserving map exhibits `G` as a minor of `H`
(with singleton branch sets). -/
theorem IsMinor.of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (hf : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) : IsMinor G H := by
  refine ⟨{ branch := fun v => ({f v} : Set W)
            branch_nonempty := fun v => ⟨f v, rfl⟩
            branch_disjoint := ?_
            branch_connected := fun v => connected_induce_singleton H (f v)
            branch_adj := ?_ }⟩
  · intro v w hvw
    simpa [Set.disjoint_singleton] using fun h => hvw (f.injective h)
  · intro v w hvw
    exact ⟨f v, rfl, f w, rfl, hf v w hvw⟩

/-- Every graph is a minor of itself. -/
theorem IsMinor.refl {V : Type*} (G : SimpleGraph V) : IsMinor G G :=
  IsMinor.of_embedding (Function.Embedding.refl V) (fun _ _ h => h)

/-- Reindexing the source: if `A` maps into `A'` by an injective adjacency-preserving map and
`A'` is a minor of `X`, then `A` is a minor of `X`. -/
theorem IsMinor.of_source_map {V V' W : Type*} {A : SimpleGraph V} {A' : SimpleGraph V'}
    {X : SimpleGraph W} (g : V ↪ V') (hg : ∀ a b, A.Adj a b → A'.Adj (g a) (g b))
    (h : IsMinor A' X) : IsMinor A X := by
  obtain ⟨M⟩ := h
  exact ⟨{ branch := fun v => M.branch (g v)
           branch_nonempty := fun v => M.branch_nonempty _
           branch_disjoint := fun v w hvw => M.branch_disjoint _ _ fun hc => hvw (g.injective hc)
           branch_connected := fun v => M.branch_connected _
           branch_adj := fun v w hvw => M.branch_adj _ _ (hg v w hvw) }⟩

/-- Transporting the host graph along an embedding that reflects and preserves adjacency. -/
theorem IsMinor.of_target_embedding {V W W' : Type*} {A : SimpleGraph V} {H : SimpleGraph W}
    {H' : SimpleGraph W'} (f : W ↪ W') (hf : ∀ a b, H.Adj a b ↔ H'.Adj (f a) (f b))
    (h : IsMinor A H) : IsMinor A H' := by
  obtain ⟨M⟩ := h
  refine ⟨{ branch := fun v => f '' (M.branch v)
            branch_nonempty := fun v => (M.branch_nonempty v).image _
            branch_disjoint := fun v w hvw =>
              Set.disjoint_image_of_injective f.injective (M.branch_disjoint v w hvw)
            branch_connected := ?_
            branch_adj := ?_ }⟩
  · intro v
    have e : (H.induce (M.branch v)) ≃g (H'.induce (f '' M.branch v)) :=
      { toEquiv := Equiv.Set.image f (M.branch v) f.injective
        map_rel_iff' := fun {a b} => (hf a.1 b.1).symm }
    exact e.connected_iff.mp (M.branch_connected v)
  · intro v w hvw
    obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adj v w hvw
    exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, (hf a b).mp hab⟩

/-!
## Finite graphs on `Fin n`

Every finite graph is isomorphic to a graph on `Fin n`, so it is convenient to encode finite
graphs as pairs `⟨n, G⟩` with `G : SimpleGraph (Fin n)`.
-/

/-- A finite graph, encoded as a vertex count `n` together with a graph on `Fin n`. -/
def FinGraph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The order (number of vertices) of a finite graph. -/
def FinGraph.order (g : FinGraph) : ℕ := g.1

/-- The minor relation on finite graphs. -/
def FinGraph.IsMinor (g h : FinGraph) : Prop := Math2.IsMinor g.2 h.2

theorem FinGraph.isMinor_refl (g : FinGraph) : g.IsMinor g := Math2.IsMinor.refl g.2

/-- Finite graphs of order at most `k`, in the `Fin n` encoding, are well-quasi-ordered by the
minor relation. -/
theorem finGraph_wqo_of_order_le (k : ℕ) (G : ℕ → FinGraph) (hk : ∀ i, (G i).order ≤ k) :
    ∃ i j, i < j ∧ (G i).IsMinor (G j) := by
  -- Encode the sequence in a finite type and apply the pigeonhole principle.
  set F : ℕ → (Σ n : Fin (k + 1), SimpleGraph (Fin (n : ℕ))) := fun i =>
    ⟨⟨(G i).1, Nat.lt_succ_of_le (hk i)⟩, (G i).2⟩ with hF
  obtain ⟨i, j, hij, hFij⟩ := Finite.exists_ne_map_eq_of_infinite F
  have hGij : G i = G j := by
    have h1 : ((F i).1 : ℕ) = ((F j).1 : ℕ) := by rw [hFij]
    have h2 : HEq (F i).2 (F j).2 := (Sigma.ext_iff.mp hFij).2
    exact Sigma.ext h1 h2
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, by rw [hGij]; exact FinGraph.isMinor_refl (G j)⟩
  · exact ⟨j, i, h, by rw [hGij]; exact FinGraph.isMinor_refl (G j)⟩

/-!
## Well-quasi-ordering by minors

**Note on scope.** The full Robertson–Seymour graph minor theorem — that *all* finite graphs are
well-quasi-ordered by the minor relation — is the outcome of the twenty-paper Graph Minors series
and is far beyond what can currently be formalized. What is proved here is the classical special
case of the theorem for graphs of bounded order: for every `k`, the class of finite graphs with at
most `k` vertices is well-quasi-ordered by the minor relation, i.e. every infinite sequence of such
graphs contains an earlier member that is a minor of a later one. The graphs are allowed to live on
arbitrary (finite) vertex types; only a uniform bound `k` on the number of vertices is imposed.
-/

/-- **Robertson–Seymour, bounded-order case.** Finite graphs of order at most `k` are
well-quasi-ordered by the minor relation: for any sequence `G` of finite graphs, each with at most
`k` vertices, there are indices `i < j` such that `G i` is a minor of `G j`. -/
theorem robertson_seymour {V : ℕ → Type} [∀ i, Fintype (V i)] (k : ℕ)
    (G : ∀ i, SimpleGraph (V i)) (hk : ∀ i, Fintype.card (V i) ≤ k) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) := by
  -- Transport each graph to the vertex type `Fin (card (V i))`.
  set e : ∀ i, V i ≃ Fin (Fintype.card (V i)) := fun i => Fintype.equivFin (V i) with he
  set g : ℕ → FinGraph := fun i => ⟨Fintype.card (V i), (G i).map (e i).toEmbedding⟩ with hg
  obtain ⟨i, j, hij, hm⟩ := finGraph_wqo_of_order_le k g (fun i => hk i)
  refine ⟨i, j, hij, ?_⟩
  -- Pull the minor relation back along the two transports.
  have hsrc : IsMinor (G i) (g j).2 := by
    refine IsMinor.of_source_map (e i).toEmbedding (fun a b hab => ?_) hm
    exact SimpleGraph.map_adj_apply.mpr hab
  refine IsMinor.of_target_embedding (e j).symm.toEmbedding (fun a b => ?_) hsrc
  constructor
  · intro hab
    have := SimpleGraph.map_adj_apply (G := G j) (f := (e j).toEmbedding)
      (a := (e j).symm a) (b := (e j).symm b)
    simpa using this.mp (by simpa using hab)
  · intro hab
    have := SimpleGraph.map_adj_apply (G := G j) (f := (e j).toEmbedding)
      (a := (e j).symm a) (b := (e j).symm b)
    simpa using this.mpr hab

end Math2

