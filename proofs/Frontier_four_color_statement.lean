/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
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

namespace Frontier

universe u v

/-- `IsArc p q A` says that the set `A ⊆ ℝ²` is a simple (Jordan) arc with endpoints `p` and `q`:
it is the image of an injective continuous map `[0,1] → ℝ²` sending `0 ↦ p` and `1 ↦ q`. -/
def IsArc (p q : ℝ × ℝ) (A : Set (ℝ × ℝ)) : Prop :=
  ∃ f : ℝ → ℝ × ℝ, ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
    f 0 = p ∧ f 1 = q ∧ A = f '' Set.Icc 0 1

/-- A simple graph is *planar* when it can be drawn in the plane without crossings: there is an
injective placement `pos` of the vertices as points of `ℝ²` and, for every edge, a simple arc
joining the images of its endpoints, such that

* an arc meets the set of vertex points only in the two endpoints of its edge, and
* two arcs coming from distinct edges meet only in the images of the vertices shared by the
  two edges.

This is the usual topological notion of a planar embedding (drawings in the plane, the sphere,
or with piecewise-linear arcs all give equivalent notions of planarity). -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ pos : V → ℝ × ℝ, ∃ arc : V → V → Set (ℝ × ℝ),
    Function.Injective pos ∧
    (∀ ⦃a b⦄, G.Adj a b → IsArc (pos a) (pos b) (arc a b)) ∧
    (∀ ⦃a b⦄, G.Adj a b → arc a b = arc b a) ∧
    (∀ ⦃a b⦄, G.Adj a b → ∀ c, pos c ∈ arc a b → c = a ∨ c = b) ∧
    (∀ ⦃a b c d⦄, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
      arc a b ∩ arc c d ⊆ pos '' ({a, b} ∩ {c, d}))

/-- Planarity is inherited along injective adjacency-preserving maps: if `H` maps into `G` by an
injective map that sends edges to edges, and `G` is planar, then so is `H`.  (In particular every
subgraph of a planar graph is planar.) -/
theorem IsPlanar.comap {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : W → V) (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (hG : IsPlanar G) : IsPlanar H := by
  obtain ⟨pos, arc, hinj, harc, hsymm, hvert, hcross⟩ := hG
  refine ⟨pos ∘ f, fun a b => arc (f a) (f b), hinj.comp hf, ?_, ?_, ?_, ?_⟩
  · exact fun a b hab => harc (hadj a b hab)
  · exact fun a b hab => hsymm (hadj a b hab)
  · intro a b hab c hc
    rcases hvert (hadj a b hab) (f c) hc with h | h
    · exact Or.inl (hf h)
    · exact Or.inr (hf h)
  · intro a b c d hab hcd hne
    have hne' : s(f a, f b) ≠ s(f c, f d) := by
      intro h
      apply hne
      rw [Sym2.eq_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hf h1, hf h2⟩
      · exact Or.inr ⟨hf h1, hf h2⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcross (hadj a b hab) (hadj c d hcd) hne' hx
    have himg : ({f a, f b} : Set V) ∩ {f c, f d} = f '' (({a, b} : Set W) ∩ {c, d}) := by
      rw [Set.image_inter hf, Set.image_pair, Set.image_pair]
    rw [himg] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨z, hz, by simp [Function.comp, hzy, hyx]⟩

/-- Every subgraph of a planar graph is planar. -/
theorem IsPlanar.subgraph {V : Type u} {G : SimpleGraph V} (G' : G.Subgraph)
    (hG : IsPlanar G) : IsPlanar G'.coe :=
  IsPlanar.comap Subtype.val Subtype.val_injective (fun _ _ h => G'.adj_sub h) hG

/-- **De Bruijn–Erdős / compactness for colourings.**  If every subgraph of `G` spanned by
finitely many vertices is `n`-colourable, then `G` is `n`-colourable.  This is a direct
consequence of `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`. -/
theorem colorable_of_forall_finite_subgraph {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Colorable n) : G.Colorable n :=
  SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
    (F := (⊤ : SimpleGraph (Fin n))) (fun G' hG' => (h G' hG').some)

/-- The statement of the four colour theorem (Appel–Haken): every planar graph, on an arbitrary
vertex type, admits a proper colouring with four colours. -/
def FourColorStatement : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The four colour statement restricted to graphs with finitely many vertices. -/
def FiniteFourColorStatement : Prop :=
  ∀ (V : Type u) [Finite V] (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- **Base case.** Any graph with at most four vertices is four-colourable; in particular this
settles the four colour statement for planar graphs on at most four vertices. -/
theorem colorable_four_of_card_le {V : Type u} [Fintype V] (hV : Fintype.card V ≤ 4)
    (G : SimpleGraph V) : G.Colorable 4 :=
  (SimpleGraph.colorable_of_fintype G).mono hV

/-- **Lean-checked reduction of the four colour statement to the finite case.**
If every *finite* planar graph is 4-colourable, then every planar graph whatsoever is
4-colourable.  The proof combines the compactness theorem for graph colourings
(`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`, i.e. De Bruijn–Erdős) with the fact
that subgraphs of planar graphs are planar. -/
theorem four_color_statement : FiniteFourColorStatement.{u} → FourColorStatement.{u} := by
  intro hfin V G hG
  refine colorable_of_forall_finite_subgraph fun G' hG' => ?_
  haveI : Finite G'.verts := hG'
  exact hfin _ _ (hG.subgraph G')

end Frontier

