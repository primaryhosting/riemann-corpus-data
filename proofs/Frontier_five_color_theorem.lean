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

set_option grind.warning false

/-!
# Planar graphs and colourings

This file sets up a faithful (topological) notion of planarity for simple graphs — a
drawing of the graph in the plane `ℝ × ℝ` where vertices are distinct points and edges
are arcs meeting only at common endpoints — and proves a base case of the five colour
theorem.
-/

namespace SimpleGraph

variable {V : Type*}

/-- A drawing of a simple graph `G` in the plane: an injective placement of the vertices
as points of `ℝ × ℝ`, together with, for every edge, an arc (a continuous injective image
of the unit interval) joining the two endpoints, such that two distinct arcs meet only in
the images of their common endpoints, and a vertex point lies on an arc only if it is an
endpoint of the corresponding edge. -/
structure PlanarEmbedding (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  point : V → ℝ × ℝ
  /-- Distinct vertices get distinct points. -/
  point_inj : Function.Injective point
  /-- The set of points of the plane covered by the arc drawn for an edge. -/
  arc : Sym2 V → Set (ℝ × ℝ)
  /-- Each edge is drawn as an arc: a continuous injective image of `[0,1]` whose
  endpoints are the points of the two ends of the edge. -/
  arc_isArc : ∀ e ∈ G.edgeSet, ∃ f : unitInterval → ℝ × ℝ,
    Continuous f ∧ Function.Injective f ∧ Set.range f = arc e ∧
      Sym2.map point e = s(f 0, f 1)
  /-- Two distinct arcs meet only at points of common endpoints. -/
  arc_inter : ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e ≠ e' →
    arc e ∩ arc e' ⊆ point '' {v | v ∈ e ∧ v ∈ e'}
  /-- A vertex point lying on an arc must be an endpoint of that edge. -/
  point_mem_arc : ∀ e ∈ G.edgeSet, ∀ v : V, point v ∈ arc e → v ∈ e

/-- A simple graph is *planar* if it can be drawn in the plane. -/
def Planar (G : SimpleGraph V) : Prop := Nonempty (PlanarEmbedding G)

/-- Subgraphs of planar graphs are planar. -/
theorem Planar.mono {G H : SimpleGraph V} (hle : H ≤ G) (hG : G.Planar) : H.Planar := by
  obtain ⟨E⟩ := hG
  have hsub : H.edgeSet ⊆ G.edgeSet := edgeSet_mono hle
  exact ⟨{ point := E.point
           point_inj := E.point_inj
           arc := E.arc
           arc_isArc := fun e he => E.arc_isArc e (hsub he)
           arc_inter := fun e he e' he' hne => E.arc_inter e (hsub he) e' (hsub he') hne
           point_mem_arc := fun e he v hv => E.point_mem_arc e (hsub he) v hv }⟩

/-- The empty graph on a type that embeds in the plane is planar. -/
theorem planar_bot_of_injective (p : V → ℝ × ℝ) (hp : Function.Injective p) :
    (⊥ : SimpleGraph V).Planar :=
  ⟨{ point := p
     point_inj := hp
     arc := fun _ => ∅
     arc_isArc := fun e he => absurd he (by simp)
     arc_inter := fun e he => absurd he (by simp)
     point_mem_arc := fun e he => absurd he (by simp) }⟩

/-- A graph with a single edge is planar: this shows the notion of planarity above is not
vacuous (there really are planar graphs having edges). -/
theorem planar_single_edge : (⊤ : SimpleGraph (Fin 2)).Planar := by
  have hedge : ∀ e : Sym2 (Fin 2), e ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet → e = s(0, 1) := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [mem_edgeSet, top_adj] at he
      fin_cases u <;> fin_cases v <;> simp_all [Sym2.eq_swap]
  refine ⟨{ point := fun i => ((i : ℕ), 0)
            point_inj := ?_
            arc := fun _ => Set.range (fun t : unitInterval => ((t : ℝ), (0 : ℝ)))
            arc_isArc := ?_
            arc_inter := ?_
            point_mem_arc := ?_ }⟩
  · intro i j hij
    have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := congrArg Prod.fst hij
    exact Fin.ext (Nat.cast_injective this)
  · intro e he
    refine ⟨fun t : unitInterval => ((t : ℝ), (0 : ℝ)), ?_, ?_, rfl, ?_⟩
    · exact continuous_subtype_val.prodMk continuous_const
    · intro s t hst
      exact Subtype.ext (congrArg Prod.fst hst)
    · rw [hedge e he]
      norm_num [Sym2.map_pair_eq]
  · intro e he e' he' hne
    exact absurd ((hedge e he).trans (hedge e' he').symm) hne
  · intro e he v _
    rw [hedge e he]
    fin_cases v <;> simp

/-!
### Degenerate graphs and greedy colouring
-/

/-- `G.DegenerateLE k` says that every nonempty finite set of vertices contains a vertex
with at most `k` neighbours inside the set. Equivalently, `G` is `k`-degenerate. -/
def DegenerateLE (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, ((s.erase v).filter (fun w => G.Adj v w)).card ≤ k

/-- Any graph on at most `k + 1` vertices is `k`-degenerate. -/
theorem degenerateLE_of_card_le [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : Fintype.card V ≤ k + 1) : G.DegenerateLE k := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  have h1 : ((s.erase v).filter (fun w => G.Adj v w)).card ≤ (s.erase v).card :=
    Finset.card_filter_le _ _
  have h2 : (s.erase v).card ≤ (Finset.univ.erase v).card :=
    Finset.card_le_card (Finset.erase_subset_erase _ (Finset.subset_univ s))
  have h3 : (Finset.univ.erase v).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  omega

/-- Greedy colouring: on a finite vertex type, every set of vertices of a `k`-degenerate
graph carries a proper colouring with `k + 1` colours. -/
theorem exists_coloring_of_degenerateLE {G : SimpleGraph V} {k : ℕ} (h : G.DegenerateLE k)
    (s : Finset V) :
    ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hcard⟩ := h s hs
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    set N : Finset V := (s.erase v).filter (fun w => G.Adj v w) with hN
    have him : (N.image c).card ≤ k := le_trans (Finset.card_image_le) hcard
    obtain ⟨col, hcol⟩ : ∃ col : Fin (k + 1), col ∉ N.image c := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ N.image c := fun x _ => hcon x
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hmemN : ∀ w ∈ s, w ≠ v → G.Adj v w → c w ∈ N.image c := by
      intro w hw hwv hadj
      exact Finset.mem_image_of_mem c (Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hwv, hw⟩, hadj⟩)
    refine ⟨Function.update c v col, ?_⟩
    intro u hu w hw hadj
    have hne : u ≠ w := G.ne_of_adj hadj
    by_cases huv : u = v
    · subst huv
      have hwu : w ≠ u := fun h => hne h.symm
      rw [Function.update_self, Function.update_of_ne hwu]
      intro hEq
      exact hcol (hEq ▸ hmemN w hw hwu hadj)
    · by_cases hwv : w = v
      · subst hwv
        rw [Function.update_self, Function.update_of_ne huv]
        intro hEq
        exact hcol (hEq ▸ hmemN u hu huv hadj.symm)
      · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
        exact hc u (Finset.mem_erase.2 ⟨huv, hu⟩) w (Finset.mem_erase.2 ⟨hwv, hw⟩) hadj

/-- Every `k`-degenerate graph on a finite vertex type is `(k+1)`-colourable. -/
theorem Colorable_of_degenerateLE [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : G.DegenerateLE k) : G.Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := exists_coloring_of_degenerateLE h Finset.univ
  exact ⟨Coloring.mk c fun {u w} hadj =>
    hc u (Finset.mem_univ u) w (Finset.mem_univ w) hadj⟩

/-- Any graph on at most five vertices is 5-colourable.  (This is the base case of the
induction in the general five colour theorem.) -/
theorem colorable_five_of_card_le_five [Fintype V] {G : SimpleGraph V}
    (hcard : Fintype.card V ≤ 5) : G.Colorable 5 :=
  Colorable_of_degenerateLE (degenerateLE_of_card_le (k := 4) hcard)

end SimpleGraph

namespace Frontier

/-- **Five colour theorem (base case).**

Every planar graph which is `4`-degenerate — in particular, every planar graph with at
most five vertices — is 5-colourable.

The general five colour theorem states that *every* planar graph is 5-colourable; the
planarity hypothesis is what would, in the general proof, supply a vertex of small degree
together with the Kempe chain exchange argument.  In the base case proved here the
colouring is obtained greedily from the degeneracy hypothesis, so planarity is not used. -/
theorem five_color_theorem {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : G.Planar) (hdeg : G.DegenerateLE 4) : G.Colorable 5 :=
  SimpleGraph.Colorable_of_degenerateLE hdeg

/-- Every planar graph on at most five vertices is 5-colourable. -/
theorem five_color_theorem_card_le_five {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : G.Planar) (hcard : Fintype.card V ≤ 5) : G.Colorable 5 :=
  five_color_theorem G hplanar (SimpleGraph.degenerateLE_of_card_le (k := 4) hcard)

end Frontier

