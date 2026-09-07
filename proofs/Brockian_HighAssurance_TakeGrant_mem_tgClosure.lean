import Mathlib

/-!
# The Take–Grant authority-confinement theorem (de-jure model)

A machine-checked, non-vacuous, inductive formalization of the classical
**take–grant protection model** (Lipton–Snyder 1977; Bishop, *Computer Security*).

A *protection graph* is a finite set of directed, right-labelled edges over a
vertex set of subjects/objects (`ℕ`).  An edge `(x, y, r)` means "subject `x`
holds right `r` over vertex `y`" — i.e. a capability.  The two core de-jure
rewrite rules are:

* **take**  — if `x —take→ y` and `y —r→ z` then `x` may add `x —r→ z`;
* **grant** — if `x —grant→ y` and `x —r→ z` then `x` may add `y —r→ z`.

We prove the *soundness / safety* direction of authority confinement:
every edge appearing in any reachable protection graph is **tg-derivable**
from the initial graph, and consequently no rewrite sequence can ever create
authority that crosses an invariant of the take/grant rules.
-/

namespace Brockian.HighAssurance.TakeGrant

/-- The four de-jure rights of the take–grant protection model. -/
inductive Right
  | take | grant | read | write
  deriving DecidableEq, Repr

instance : Fintype Right where
  elems := {Right.take, Right.grant, Right.read, Right.write}
  complete := by intro x; cases x <;> decide

/-- A capability edge `(source, target, right)`. -/
abbrev Edge : Type := ℕ × ℕ × Right

/-- A protection graph state: a finite set of capability edges. -/
abbrev State : Type := Finset Edge

/-- One de-jure rewrite step of the take–grant model, guarded by the
    take/grant preconditions.  Each rule *adds* one derived capability. -/
inductive step : State → State → Prop
  | take {G : State} {x y z : ℕ} {r : Right}
      (hxy : (x, y, Right.take) ∈ G) (hyz : (y, z, r) ∈ G) :
      step G (insert (x, z, r) G)
  | grant {G : State} {x y z : ℕ} {r : Right}
      (hxy : (x, y, Right.grant) ∈ G) (hxz : (x, z, r) ∈ G) :
      step G (insert (y, z, r) G)

/-- Reachability: the reflexive–transitive closure of a single rewrite step. -/
abbrev Reachable : State → State → Prop := Relation.ReflTransGen step

/-!
## The take–grant closure as an inductive relation

`TgDerivable G0 e` holds iff the capability `e` is obtainable from the initial
graph `G0` by finitely many applications of the take and grant rules.  This is
the *least* set of edges containing `G0` and closed under both rules — the
honest, general "take–grant closure."
-/

/-- `e` is derivable from `G0` by the take/grant rules. -/
inductive TgDerivable (G0 : State) : Edge → Prop
  | base {e : Edge} (he : e ∈ G0) : TgDerivable G0 e
  | take {x y z : ℕ} {r : Right}
      (hxy : TgDerivable G0 (x, y, Right.take))
      (hyz : TgDerivable G0 (y, z, r)) :
      TgDerivable G0 (x, z, r)
  | grant {x y z : ℕ} {r : Right}
      (hxy : TgDerivable G0 (x, y, Right.grant))
      (hxz : TgDerivable G0 (x, z, r)) :
      TgDerivable G0 (y, z, r)

/-- **Authority confinement (soundness direction).**
    Every edge present in any reachable protection graph was derivable from the
    initial graph `G0` by the take/grant rules.  Proved by induction on the
    reachability relation. -/
theorem authority_confined (G0 G : State) (hreach : Reachable G0 G) :
    ∀ e ∈ G, TgDerivable G0 e := by
  induction hreach with
  | refl => intro e he; exact TgDerivable.base he
  | tail _ hstep ih =>
      intro e he
      cases hstep with
      | take hxy hyz =>
          rw [Finset.mem_insert] at he
          rcases he with rfl | h2
          · exact TgDerivable.take (ih _ hxy) (ih _ hyz)
          · exact ih _ h2
      | grant hxy hxz =>
          rw [Finset.mem_insert] at he
          rcases he with rfl | h2
          · exact TgDerivable.grant (ih _ hxy) (ih _ hxz)
          · exact ih _ h2

/-- The take–grant sharing predicate: `x` can ever acquire right `r` over `z`
    starting from `G0` exactly when `(x, z, r)` is tg-derivable. -/
def CanEverShare (G0 : State) (r : Right) (x z : ℕ) : Prop :=
  TgDerivable G0 (x, z, r)

/-- **Confinement corollary.**  If `x` cannot tg-derive right `r` over `z` in
    the initial graph, then no reachable state ever grants `x` that authority. -/
theorem confinement (G0 : State) (x z : ℕ) (r : Right)
    (hno : ¬ CanEverShare G0 r x z) :
    ∀ G, Reachable G0 G → (x, z, r) ∉ G := by
  intro G hG hmem
  exact hno (authority_confined G0 G hG _ hmem)

/-!
## A coloring invariant: authority never crosses a monochromatic partition

Both rules only ever connect vertices that are already linked through a shared
vertex, so any partition of the vertices that makes every initial edge
*monochromatic* is preserved by tg-derivation.  This yields a sharp, decidable
confinement test for concrete graphs (e.g. two disconnected "islands").
-/

/-- If every initial edge is monochromatic under a coloring `col`, then every
    tg-derivable edge is monochromatic too. -/
theorem tgDerivable_monochromatic (col : ℕ → ℕ) {G0 : State}
    (hmono : ∀ e ∈ G0, col e.1 = col e.2.1) :
    ∀ e, TgDerivable G0 e → col e.1 = col e.2.1 := by
  intro e he
  induction he with
  | base hx => exact hmono _ hx
  | take _ _ ih1 ih2 => exact ih1.trans ih2
  | grant _ _ ih1 ih2 => exact ih1.symm.trans ih2

/-- **Confinement via coloring.**  Two vertices of different color can never
    share authority in any reachable state. -/
theorem confinement_of_coloring (col : ℕ → ℕ) {G0 : State}
    (hmono : ∀ e ∈ G0, col e.1 = col e.2.1)
    {x z : ℕ} {r : Right} (hcol : col x ≠ col z) :
    ∀ G, Reachable G0 G → (x, z, r) ∉ G := by
  intro G hG hmem
  exact hcol
    (tgDerivable_monochromatic col hmono (x, z, r)
      (authority_confined G0 G hG _ hmem))

/-!
## A computable over-approximation: the vertex-confinement closure

`tgClosure G0` is the sound, computable over-approximation "all edges whose
endpoints are vertices of `G0`."  The take/grant rules never introduce a fresh
vertex, so this Finset is closed under `step` and contains every reachable
graph.  It is genuinely non-trivial: it provably excludes any edge pointing at
a vertex not already present in `G0`.
-/

/-- The vertices (sources and targets) occurring in `G0`. -/
def verts (G0 : State) : Finset ℕ :=
  G0.image (fun e => e.1) ∪ G0.image (fun e => e.2.1)

/-- The vertex-confinement closure of `G0`: every labelled edge over `verts G0`. -/
def tgClosure (G0 : State) : State :=
  verts G0 ×ˢ verts G0 ×ˢ (Finset.univ : Finset Right)

theorem mem_tgClosure {G0 : State} {a b : ℕ} {r : Right} :
    (a, b, r) ∈ tgClosure G0 ↔ a ∈ verts G0 ∧ b ∈ verts G0 := by
  simp only [tgClosure, Finset.mem_product, Finset.mem_univ, and_true]

theorem left_mem_verts {G0 : State} {a b : ℕ} {r : Right}
    (h : (a, b, r) ∈ G0) : a ∈ verts G0 := by
  simp only [verts, Finset.mem_union, Finset.mem_image]
  exact Or.inl ⟨(a, b, r), h, rfl⟩

theorem right_mem_verts {G0 : State} {a b : ℕ} {r : Right}
    (h : (a, b, r) ∈ G0) : b ∈ verts G0 := by
  simp only [verts, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨(a, b, r), h, rfl⟩

/-- `G0` is contained in its closure. -/
theorem subset_tgClosure (G0 : State) : G0 ⊆ tgClosure G0 := by
  intro e he
  obtain ⟨a, b, r⟩ := e
  rw [mem_tgClosure]
  exact ⟨left_mem_verts he, right_mem_verts he⟩

/-- **The closure is a step-invariant.**  One rewrite step out of the closure
    stays inside the closure. -/
theorem tgClosure_closed {G0 H : State} (h : step (tgClosure G0) H) :
    H ⊆ tgClosure G0 := by
  cases h with
  | take hxy hyz =>
      rw [Finset.insert_subset_iff]
      refine ⟨?_, Finset.Subset.refl _⟩
      rw [mem_tgClosure] at hxy hyz ⊢
      exact ⟨hxy.1, hyz.2⟩
  | grant hxy hxz =>
      rw [Finset.insert_subset_iff]
      refine ⟨?_, Finset.Subset.refl _⟩
      rw [mem_tgClosure] at hxy hxz ⊢
      exact ⟨hxy.2, hxz.2⟩

/-- **Reachable authority ⊆ the take–grant closure.**  Every reachable
    protection graph is contained in `tgClosure G0`. -/
theorem reachable_subset_tgClosure (G0 G : State) (hreach : Reachable G0 G) :
    G ⊆ tgClosure G0 := by
  induction hreach with
  | refl => exact subset_tgClosure G0
  | tail _ hstep ih =>
      cases hstep with
      | take hxy hyz =>
          rw [Finset.insert_subset_iff]
          refine ⟨?_, ih⟩
          have hx := (mem_tgClosure.1 (ih hxy)).1
          have hz := (mem_tgClosure.1 (ih hyz)).2
          exact mem_tgClosure.2 ⟨hx, hz⟩
      | grant hxy hxz =>
          rw [Finset.insert_subset_iff]
          refine ⟨?_, ih⟩
          have hy := (mem_tgClosure.1 (ih hxy)).2
          have hz := (mem_tgClosure.1 (ih hxz)).2
          exact mem_tgClosure.2 ⟨hy, hz⟩

/-!
## Non-vacuity witnesses (concrete, decidable)
-/

/-- (a) The take rule genuinely propagates a right: from `1 —take→ 2` and
    `2 —read→ 10`, a single step derives the *new* capability `1 —read→ 10`. -/
theorem take_propagates :
    ∃ (G0 G : State) (e : Edge), step G0 G ∧ e ∈ G ∧ e ∉ G0 := by
  refine ⟨{(1, 2, Right.take), (2, 10, Right.read)},
          insert (1, 10, Right.read) {(1, 2, Right.take), (2, 10, Right.read)},
          (1, 10, Right.read), ?_, ?_, ?_⟩
  · exact step.take (x := 1) (y := 2) (z := 10) (r := Right.read) (by decide) (by decide)
  · exact Finset.mem_insert_self _ _
  · decide

/-- A two-island demonstration graph.  Island A = `{1,2,10}` with
    `1 —take→ 2`, `2 —read→ 10`.  Island B = `{3,4,20}` with `3 —grant→ 4`,
    `3 —write→ 20`.  The islands share no vertex. -/
def demoGraph : State :=
  {(1, 2, Right.take), (2, 10, Right.read), (3, 4, Right.grant), (3, 20, Right.write)}

/-- Island coloring: island B vertices get color `1`, everything else color `0`. -/
def island (n : ℕ) : ℕ := if n = 3 ∨ n = 4 ∨ n = 20 then 1 else 0

/-- (b) **Confinement blocks disconnected subjects.**  Subject `1` (island A)
    can never obtain any read capability over object `20` (island B) — in *any*
    reachable state — because the two live in different color classes.  The
    hypotheses are discharged by `decide` on the concrete graph. -/
theorem confinement_witness :
    ∀ G, Reachable demoGraph G → (1, 20, Right.read) ∉ G :=
  confinement_of_coloring island (by decide) (by decide)

/-- (c) **Integrity is non-trivial: an off-closure edge is provably
    unreachable.**  No reachable state grants subject `1` any capability over a
    vertex `999` that never appears in the initial graph, since that edge lies
    outside the take–grant closure. -/
theorem off_closure_unreachable :
    ∀ G, Reachable demoGraph G → (1, 999, Right.read) ∉ G := by
  intro G hG hmem
  have hin : (1, 999, Right.read) ∈ tgClosure demoGraph :=
    reachable_subset_tgClosure _ _ hG hmem
  have hout : (1, 999, Right.read) ∉ tgClosure demoGraph := by decide
  exact hout hin

/-- The vertex-confinement closure is a *sound but strict* over-approximation:
    `(1, 20, read)` lies inside `tgClosure demoGraph` (both endpoints are
    graph vertices), yet `confinement_witness` shows it is nonetheless
    unreachable — the sharp bound comes from the coloring invariant. -/
theorem closure_is_strict_over_approximation :
    (1, 20, Right.read) ∈ tgClosure demoGraph := by decide

end Brockian.HighAssurance.TakeGrant
