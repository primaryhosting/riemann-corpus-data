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

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph Finset

/-- `Arrows N s t` says that every simple graph on at least `N` vertices contains
either a clique of size `s` or an independent set of size `t`
(i.e. `N → (s, t)` in the arrow notation for Ramsey numbers). -/
def Arrows (N s t : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    N ≤ Fintype.card V → ¬ (G.CliqueFree s ∧ Gᶜ.CliqueFree t)

/-! ### Basic transfer lemmas for induced subgraphs -/

lemma induce_compl {V : Type*} (G : SimpleGraph V) (A : Set V) :
    (SimpleGraph.induce A G)ᶜ = SimpleGraph.induce A Gᶜ := by
  ext a b; simp [Subtype.ext_iff]

lemma cliqueFree_induce {V : Type*} {G : SimpleGraph V} {n : ℕ} (A : Set V)
    (h : G.CliqueFree n) : (SimpleGraph.induce A G).CliqueFree n :=
  h.comap (SimpleGraph.Embedding.induce A)

lemma isNClique_of_induce {V : Type*} {G : SimpleGraph V} {A : Set V} {n : ℕ}
    {T : Finset A} (h : (SimpleGraph.induce A G).IsNClique n T) :
    G.IsNClique n (T.map (Function.Embedding.subtype _)) := by
  refine ⟨?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.coe_subtype] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact h.1 ha hb (by simpa [Subtype.ext_iff] using hxy)
  · simpa using h.2

/-- To establish `Arrows N s t` it suffices to treat vertex sets of size exactly `N`. -/
lemma arrows_of_card_eq {N s t : ℕ}
    (h : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = N → G.CliqueFree s → Gᶜ.CliqueFree t → False) :
    Arrows N s t := by
  rintro V _ G hcard ⟨h1, h2⟩
  classical
  obtain ⟨A, -, hA⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset V)) (n := N) (by simpa using hcard)
  exact h ↥(↑A : Set V) (SimpleGraph.induce (↑A : Set V) G) (by simp [hA])
    (cliqueFree_induce _ h1) (by rw [induce_compl]; exact cliqueFree_induce _ h2)

/-! ### Base cases -/

/-- `R(2, t) ≤ t`. -/
lemma arrows_two_left (t : ℕ) : Arrows t 2 t := by
  rintro V _ G hcard ⟨h1, h2⟩
  rw [SimpleGraph.cliqueFree_two] at h1
  subst h1
  classical
  obtain ⟨A, -, hA⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset V)) (n := t) (by simpa using hcard)
  refine h2 A ⟨?_, hA⟩
  intro x _ y _ hxy
  simpa using hxy

/-- `R(s, 2) ≤ s`. -/
lemma arrows_two_right (s : ℕ) : Arrows s s 2 := by
  rintro V _ G hcard ⟨h1, h2⟩
  rw [SimpleGraph.cliqueFree_two, compl_eq_bot] at h2
  subst h2
  classical
  obtain ⟨A, -, hA⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset V)) (n := s) (by simpa using hcard)
  refine h1 A ⟨?_, hA⟩
  intro x _ y _ hxy
  simpa using hxy

/-! ### The two extension lemmas -/

variable {V : Type}

/-- If `v` has a set `A` of at least `m` neighbours and `Arrows m s (t+1)` holds,
then `G` has an `(s+1)`-clique or `Gᶜ` has a `(t+1)`-clique. -/
lemma red_extend {m s t : ℕ} (harr : Arrows m s (t + 1))
    (G : SimpleGraph V) (v : V) (A : Finset V) (hA : ∀ x ∈ A, G.Adj v x) (hcard : m ≤ A.card)
    (h1 : G.CliqueFree (s + 1)) (h2 : Gᶜ.CliqueFree (t + 1)) : False := by
  classical
  have hB : (SimpleGraph.induce (↑A : Set V) G)ᶜ.CliqueFree (t + 1) := by
    rw [induce_compl]; exact cliqueFree_induce _ h2
  have hcard' : m ≤ Fintype.card ↥(↑A : Set V) := by simpa using hcard
  have hA' : ¬ (SimpleGraph.induce (↑A : Set V) G).CliqueFree s := fun hx =>
    harr _ _ hcard' ⟨hx, hB⟩
  rw [SimpleGraph.CliqueFree] at hA'
  push_neg at hA'
  obtain ⟨T, hT⟩ := hA'
  have hT' : G.IsNClique s (T.map (Function.Embedding.subtype _)) := isNClique_of_induce hT
  have hv : ∀ b ∈ T.map (Function.Embedding.subtype (fun x => x ∈ (↑A : Set V))), G.Adj v b := by
    intro b hb
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
    obtain ⟨x, -, rfl⟩ := hb
    exact hA _ (Finset.mem_coe.mp x.2)
  exact h1 _ (hT'.insert hv)

/-- If `v` has a set `A` of at least `n` non-neighbours (all distinct from `v`) and
`Arrows n (s+1) t` holds, then `G` has an `(s+1)`-clique or `Gᶜ` has a `(t+1)`-clique. -/
lemma blue_extend {n s t : ℕ} (harr : Arrows n (s + 1) t)
    (G : SimpleGraph V) (v : V) (A : Finset V) (hA : ∀ x ∈ A, x ≠ v ∧ ¬ G.Adj v x)
    (hcard : n ≤ A.card)
    (h1 : G.CliqueFree (s + 1)) (h2 : Gᶜ.CliqueFree (t + 1)) : False := by
  classical
  have hB : (SimpleGraph.induce (↑A : Set V) G).CliqueFree (s + 1) := cliqueFree_induce _ h1
  have hcard' : n ≤ Fintype.card ↥(↑A : Set V) := by simpa using hcard
  have hA' : ¬ (SimpleGraph.induce (↑A : Set V) G)ᶜ.CliqueFree t := fun hx =>
    harr _ _ hcard' ⟨hB, hx⟩
  rw [induce_compl, SimpleGraph.CliqueFree] at hA'
  push_neg at hA'
  obtain ⟨T, hT⟩ := hA'
  have hT' : Gᶜ.IsNClique t (T.map (Function.Embedding.subtype _)) := isNClique_of_induce hT
  have hv : ∀ b ∈ T.map (Function.Embedding.subtype (fun x => x ∈ (↑A : Set V))), Gᶜ.Adj v b := by
    intro b hb
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
    obtain ⟨x, -, rfl⟩ := hb
    obtain ⟨hne, hnadj⟩ := hA _ (Finset.mem_coe.mp x.2)
    exact ⟨fun h => hne h.symm, hnadj⟩
  exact h2 _ (hT'.insert hv)

/-! ### The Erdős–Szekeres recursion -/

lemma arrows_step {m n s t : ℕ} (hpos : 0 < m + n)
    (hm : Arrows m s (t + 1)) (hn : Arrows n (s + 1) t) :
    Arrows (m + n) (s + 1) (t + 1) := by
  rintro V _ G hcard ⟨h1, h2⟩
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  set A : Finset V := univ.filter (fun x => G.Adj v x) with hAdef
  set B : Finset V := univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hBdef
  have hsplit : A.card + B.card + 1 = Fintype.card V := by
    have h0 : A.card + (univ.filter (fun x => ¬ G.Adj v x)).card = Fintype.card V := by
      rw [hAdef]
      simpa using Finset.card_filter_add_card_filter_not
        (s := (univ : Finset V)) (p := fun x => G.Adj v x)
    have h1' : (univ.filter (fun x => ¬ G.Adj v x)) = insert v B := by
      ext x
      by_cases hx : x = v
      · subst hx; simp [hBdef]
      · simp [hBdef, hx]
    have h2' : v ∉ B := by simp [hBdef]
    rw [h1', Finset.card_insert_of_notMem h2'] at h0
    omega
  by_cases hA : m ≤ A.card
  · exact red_extend hm G v A (fun x hx => by simpa [hAdef] using hx) hA h1 h2
  · refine blue_extend hn G v B (fun x hx => by simpa [hBdef] using hx) (by omega) h1 h2

/-! ### `R(3,3) ≤ 6` -/

lemma arrows_6_3_3 : Arrows 6 3 3 :=
  arrows_step (by omega) (arrows_two_left 3) (arrows_two_right 3)

/-! ### `R(3,4) ≤ 9` -/

lemma arrows_9_3_4 : Arrows 9 3 4 := by
  apply arrows_of_card_eq
  intro V _ G hcard h1 h2
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  -- Every vertex has degree exactly 3.
  have hdeg : ∀ v : V, G.degree v = 3 := by
    intro v
    set A : Finset V := univ.filter (fun x => G.Adj v x) with hAdef
    set B : Finset V := univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hBdef
    have hdegA : G.degree v = A.card := by
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    have hsplit : A.card + B.card + 1 = Fintype.card V := by
      have h0 : A.card + (univ.filter (fun x => ¬ G.Adj v x)).card = Fintype.card V := by
        rw [hAdef]
        simpa using Finset.card_filter_add_card_filter_not
          (s := (univ : Finset V)) (p := fun x => G.Adj v x)
      have h1' : (univ.filter (fun x => ¬ G.Adj v x)) = insert v B := by
        ext x
        by_cases hx : x = v
        · subst hx; simp [hBdef]
        · simp [hBdef, hx]
      have h2' : v ∉ B := by simp [hBdef]
      rw [h1', Finset.card_insert_of_notMem h2'] at h0
      omega
    have hub : A.card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      exact red_extend (m := 4) (s := 2) (t := 3) (arrows_two_left 4) G v A
        (fun x hx => by simpa [hAdef] using hx) (by omega) h1 h2
    have hlb : 3 ≤ A.card := by
      by_contra hlt
      push_neg at hlt
      exact blue_extend (n := 6) (s := 2) (t := 3) arrows_6_3_3 G v B
        (fun x hx => by simpa [hBdef] using hx) (by omega) h1 h2
    omega
  -- Handshake: the degree sum is odd, contradiction.
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard] at hsum
  omega

/-! ### `R(3,5) ≤ 14` -/

lemma arrows_14_3_5 : Arrows 14 3 5 :=
  arrows_step (by omega) (arrows_two_left 5) arrows_9_3_4

/-! ### The lower bound: a triangle-free graph on 13 vertices with independence number 4 -/

/-- Adjacency in the circulant graph `C₁₃(1,5)` on `ℤ/13`, written on natural numbers. -/
def adjN (a b : ℕ) : Prop :=
  (a + 13 - b) % 13 = 1 ∨ (a + 13 - b) % 13 = 5 ∨
  (a + 13 - b) % 13 = 8 ∨ (a + 13 - b) % 13 = 12

instance (a b : ℕ) : Decidable (adjN a b) := by unfold adjN; infer_instance

/-- Adjacency of the circulant graph on `Fin 13`. -/
def R13Adj (a b : Fin 13) : Prop := adjN a.val b.val

instance : DecidableRel R13Adj := fun a b => inferInstanceAs (Decidable (adjN a.val b.val))

/-- The circulant graph `C₁₃(1,5)`: it is triangle-free and has independence number `4`. -/
def R13 : SimpleGraph (Fin 13) where
  Adj := R13Adj
  symm := by intro a b; revert a b; decide
  loopless := ⟨by decide⟩

instance : DecidableRel R13.Adj := inferInstanceAs (DecidableRel R13Adj)

lemma R13_no_triangle : ∀ a b c : Fin 13, R13Adj a b → R13Adj b c → ¬ R13Adj a c := by decide

lemma R13_cliqueFree_three : R13.CliqueFree 3 := by
  intro T hT
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT.2
  have h := hT.1
  simp only [Finset.coe_insert, Finset.coe_singleton] at h
  exact R13_no_triangle a b c (h (by simp) (by simp) hab) (h (by simp) (by simp) hbc)
    (h (by simp) (by simp) hac)

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
lemma no_indep5 : ∀ e < 13, ∀ d < e, ∀ c < d, ∀ b < c, ∀ a < b,
    adjN a b ∨ adjN a c ∨ adjN a d ∨ adjN a e ∨ adjN b c ∨ adjN b d ∨ adjN b e ∨
      adjN c d ∨ adjN c e ∨ adjN d e := by decide

lemma R13_compl_cliqueFree_five : R13ᶜ.CliqueFree 5 := by
  intro T hT
  set f := T.orderIsoOfFin hT.2
  have hmem : ∀ i : Fin 5, ((f i : Fin 13)) ∈ T := fun i => (f i).2
  have hmono : ∀ i j : Fin 5, i < j → ((f i : Fin 13) : ℕ) < ((f j : Fin 13) : ℕ) :=
    fun i j hij => (OrderIso.lt_iff_lt f).mpr hij
  have hnadj : ∀ i j : Fin 5, i ≠ j → ¬ R13Adj (f i : Fin 13) (f j : Fin 13) := by
    intro i j hij
    have hne : ((f i : Fin 13)) ≠ ((f j : Fin 13)) := by
      intro h
      exact hij (f.injective (Subtype.ext h))
    exact (hT.1 (hmem i) (hmem j) hne).2
  have h := no_indep5 ((f 4 : Fin 13) : ℕ) (f 4 : Fin 13).2
    ((f 3 : Fin 13) : ℕ) (hmono 3 4 (by decide))
    ((f 2 : Fin 13) : ℕ) (hmono 2 3 (by decide))
    ((f 1 : Fin 13) : ℕ) (hmono 1 2 (by decide))
    ((f 0 : Fin 13) : ℕ) (hmono 0 1 (by decide))
  rcases h with h|h|h|h|h|h|h|h|h|h
  · exact hnadj 0 1 (by decide) h
  · exact hnadj 0 2 (by decide) h
  · exact hnadj 0 3 (by decide) h
  · exact hnadj 0 4 (by decide) h
  · exact hnadj 1 2 (by decide) h
  · exact hnadj 1 3 (by decide) h
  · exact hnadj 1 4 (by decide) h
  · exact hnadj 2 3 (by decide) h
  · exact hnadj 2 4 (by decide) h
  · exact hnadj 3 4 (by decide) h

/-! ### The Ramsey number `R(3,5) = 14` -/

/-- **`R(3,5) = 14`**: `14` is the least `N` such that every graph on at least `N`
vertices contains a triangle or an independent set of size `5`. -/
theorem ramsey_3_5 : IsLeast {N : ℕ | Arrows N 3 5} 14 := by
  constructor
  · exact arrows_14_3_5
  · intro N hN
    by_contra hlt
    push_neg at hlt
    exact hN (Fin 13) R13 (by simp only [Fintype.card_fin]; omega)
      ⟨R13_cliqueFree_three, R13_compl_cliqueFree_five⟩

end Math

