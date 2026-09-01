/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

variable {V : Type*}

/-- `endv u l` is the last vertex of the walk that starts at `u` and then visits the
vertices of `l` in order. -/
def endv : V → List V → V
  | u, [] => u
  | _, v :: l => endv v l

/-- `cost w u l` is the total weight of the walk starting at `u` and then visiting the
vertices of `l` in order.  A weight of `⊤` means "no edge". -/
noncomputable def cost (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | u, v :: l => w u v + cost w v l

/-- The graph distance from `s` to `t`: the infimum of the weights of all walks from
`s` to `t` (`⊤` if there is no such walk). -/
noncomputable def gdist (w : V → V → ℝ≥0∞) (s t : V) : ℝ≥0∞ :=
  ⨅ l ∈ {l : List V | endv s l = t}, cost w s l

@[simp] lemma endv_append_singleton (u v : V) (l : List V) :
    endv u (l ++ [v]) = v := by
  induction l generalizing u with
  | nil => simp [endv]
  | cons y t ih => simpa [endv] using ih y

lemma cost_append_singleton (w : V → V → ℝ≥0∞) (u v : V) (l : List V) :
    cost w u (l ++ [v]) = cost w u l + w (endv u l) v := by
  induction l generalizing u with
  | nil => simp [cost, endv]
  | cons y t ih =>
      simp only [List.cons_append, cost, endv, ih y, add_assoc]

lemma gdist_le_cost (w : V → V → ℝ≥0∞) (s t : V) (l : List V) (hl : endv s l = t) :
    gdist w s t ≤ cost w s l := by
  refine iInf₂_le_of_le l ?_ le_rfl
  simpa using hl

@[simp] lemma gdist_self (w : V → V → ℝ≥0∞) (s : V) : gdist w s s = 0 := by
  have : gdist w s s ≤ cost w s [] := gdist_le_cost w s s [] rfl
  simpa [cost] using this

/-- The triangle-type inequality: extending a walk to `u` by the edge `u → v`. -/
lemma gdist_le_gdist_add_edge (w : V → V → ℝ≥0∞) (s u v : V) :
    gdist w s v ≤ gdist w s u + w u v := by
  rw [show gdist w s u = ⨅ l ∈ {l : List V | endv s l = u}, cost w s l from rfl,
    ENNReal.iInf_add]
  refine le_iInf fun l => ?_
  by_cases hl : endv s l = u
  · have h1 : gdist w s v ≤ cost w s (l ++ [v]) :=
      gdist_le_cost w s v _ (endv_append_singleton s v l)
    rw [cost_append_singleton, hl] at h1
    simpa [hl] using h1
  · simp [hl]

variable [DecidableEq V]

/-- The invariant maintained by Dijkstra's algorithm: `S` is the set of settled
vertices, `d` the tentative distances. -/
structure Inv (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) : Prop where
  zero : d s = 0
  ub : ∀ v, gdist w s v ≤ d v
  settled : ∀ v ∈ S, d v = gdist w s v
  relaxed : ∀ u ∈ S, ∀ x ∉ S, d x ≤ gdist w s u + w u x

/-- Key lemma: any walk that starts inside `S` and ends outside `S` costs at least the
current minimal tentative distance outside `S`. -/
lemma key (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) (u₀ : V)
    (h4 : ∀ u ∈ S, ∀ x ∉ S, d x ≤ gdist w s u + w u x)
    (hmin : ∀ x ∉ S, d u₀ ≤ d x) :
    ∀ (l : List V) (u : V), u ∈ S → endv u l ∉ S → d u₀ ≤ gdist w s u + cost w u l := by
  intro l
  induction l with
  | nil => intro u hu hend; exact absurd hu (by simpa [endv] using hend)
  | cons y t ih =>
      intro u hu hend
      simp only [endv] at hend
      by_cases hy : y ∈ S
      · have h1 : d u₀ ≤ gdist w s y + cost w y t := ih y hy hend
        have h2 : gdist w s y ≤ gdist w s u + w u y := gdist_le_gdist_add_edge w s u y
        calc d u₀ ≤ gdist w s y + cost w y t := h1
          _ ≤ (gdist w s u + w u y) + cost w y t := by gcongr
          _ = gdist w s u + cost w u (y :: t) := by simp [cost, add_assoc]
      · have h1 : d u₀ ≤ d y := hmin y hy
        have h2 : d y ≤ gdist w s u + w u y := h4 u hu y hy
        calc d u₀ ≤ gdist w s u + w u y := h1.trans h2
          _ ≤ gdist w s u + (w u y + cost w y t) := by gcongr; exact le_self_add
          _ = gdist w s u + cost w u (y :: t) := by simp [cost]

/-- The vertex chosen by Dijkstra's algorithm is settled correctly. -/
lemma pick_eq_gdist (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) (u₀ : V)
    (hinv : Inv w s S d) (hu₀ : u₀ ∉ S) (hmin : ∀ x ∉ S, d u₀ ≤ d x) :
    d u₀ = gdist w s u₀ := by
  refine le_antisymm ?_ (hinv.ub u₀)
  rw [gdist]
  refine le_iInf₂ fun l hl => ?_
  have hl' : endv s l = u₀ := hl
  by_cases hs : s ∈ S
  · have := key w s S d u₀ hinv.relaxed hmin l s hs (by rw [hl']; exact hu₀)
    simpa using this
  · calc d u₀ ≤ d s := hmin s hs
      _ = 0 := hinv.zero
      _ ≤ cost w s l := zero_le _

/-- One step of Dijkstra's algorithm preserves the invariant. -/
lemma Inv.step (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) (u₀ : V)
    (hinv : Inv w s S d) (hu₀ : u₀ ∉ S) (hmin : ∀ x ∉ S, d u₀ ≤ d x) :
    Inv w s (insert u₀ S) (fun v => min (d v) (d u₀ + w u₀ v)) := by
  have hu₀d : d u₀ = gdist w s u₀ := pick_eq_gdist w s S d u₀ hinv hu₀ hmin
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hinv.zero]
  · intro v
    refine le_min (hinv.ub v) ?_
    rw [hu₀d]
    exact gdist_le_gdist_add_edge w s u₀ v
  · intro v hv
    have hge : gdist w s v ≤ d u₀ + w u₀ v := by
      rw [hu₀d]; exact gdist_le_gdist_add_edge w s u₀ v
    rcases Finset.mem_insert.mp hv with h | h
    · subst h
      have : d v ≤ d v + w v v := le_self_add
      simp only [min_eq_left this]
      exact hu₀d
    · have hdv : d v = gdist w s v := hinv.settled v h
      have hle : d v ≤ d u₀ + w u₀ v := hdv ▸ hge
      simp only [min_eq_left hle]
      exact hdv
  · intro u hu x hx
    have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp hu with h | h
    · subst h
      exact min_le_right _ _ |>.trans (by rw [hu₀d])
    · exact (min_le_left _ _).trans (hinv.relaxed u h x hxS)

end CS

