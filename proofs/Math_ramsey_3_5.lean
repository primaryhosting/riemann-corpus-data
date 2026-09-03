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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Math

open SimpleGraph Finset

/-! ## Local Ramsey statements

We work inside a fixed graph `G` and consider finite sets `W` of vertices. -/

section Local

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `RamseyOn G s t W` says that the vertex set `W` contains an `s`-clique of `G`
or an `t`-element independent set of `G` (an `t`-clique of the complement). -/
def RamseyOn (G : SimpleGraph V) (s t : ℕ) (W : Finset V) : Prop :=
  (∃ S ⊆ W, G.IsNClique s S) ∨ (∃ S ⊆ W, Gᶜ.IsNClique t S)

lemma RamseyOn.mono {s t : ℕ} {W W' : Finset V} (h : W ⊆ W') :
    RamseyOn G s t W → RamseyOn G s t W' := by
  rintro (⟨S, hS, hc⟩ | ⟨S, hS, hc⟩)
  · exact Or.inl ⟨S, hS.trans h, hc⟩
  · exact Or.inr ⟨S, hS.trans h, hc⟩

/-- The neighbours of `v` inside `W`. -/
def nbrIn (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v : V) : Finset V :=
  W.filter (fun u => G.Adj v u)

/-- The non-neighbours of `v` inside `W`, excluding `v` itself. -/
def nonNbrIn (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v : V) : Finset V :=
  (W.erase v).filter (fun u => ¬ G.Adj v u)

lemma nbrIn_subset {W : Finset V} {v : V} : nbrIn G W v ⊆ W := filter_subset _ _

lemma nonNbrIn_subset {W : Finset V} {v : V} : nonNbrIn G W v ⊆ W :=
  (filter_subset _ _).trans (erase_subset _ _)

lemma mem_nbrIn {W : Finset V} {v u : V} : u ∈ nbrIn G W v ↔ u ∈ W ∧ G.Adj v u := by
  simp [nbrIn]

lemma mem_nonNbrIn {W : Finset V} {v u : V} :
    u ∈ nonNbrIn G W v ↔ (u ∈ W ∧ u ≠ v) ∧ ¬ G.Adj v u := by
  simp [nonNbrIn, and_comm]

lemma nbrIn_eq_erase {W : Finset V} {v : V} :
    nbrIn G W v = (W.erase v).filter (fun u => G.Adj v u) := by
  ext u
  simp only [nbrIn, mem_filter, mem_erase]
  constructor
  · rintro ⟨hu, ha⟩
    exact ⟨⟨fun h => G.irrefl (h ▸ ha), hu⟩, ha⟩
  · rintro ⟨⟨_, hu⟩, ha⟩
    exact ⟨hu, ha⟩

lemma card_nbrIn_add_card_nonNbrIn {W : Finset V} {v : V} (hv : v ∈ W) :
    (nbrIn G W v).card + (nonNbrIn G W v).card + 1 = W.card := by
  have hpos : 0 < W.card := card_pos.2 ⟨v, hv⟩
  have := Finset.card_filter_add_card_filter_not (s := W.erase v) (p := fun u => G.Adj v u)
  rw [nbrIn_eq_erase, nonNbrIn]
  rw [card_erase_of_mem hv] at this
  omega

/-- If `W` contains no triangle then the neighbourhood of `v` inside `W` is independent. -/
lemma isClique_compl_nbrIn {W : Finset V} {v : V} (hv : v ∈ W)
    (h3 : ∀ S ⊆ W, ¬ G.IsNClique 3 S) : Gᶜ.IsClique (nbrIn G W v : Set V) := by
  intro a ha b hb hab
  rw [mem_coe, mem_nbrIn] at ha hb
  refine (G.compl_adj a b).2 ⟨hab, fun hadj => ?_⟩
  refine h3 {v, a, b} ?_ (is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩)
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hv
  · exact ha.1
  · exact hb.1

/-- An independent set among the non-neighbours of `v` can be extended by `v`. -/
lemma indep_insert {W : Finset V} {v : V} (hv : v ∈ W) {S : Finset V}
    (hS : S ⊆ nonNbrIn G W v) {k : ℕ} (h : Gᶜ.IsNClique k S) :
    ∃ T ⊆ W, Gᶜ.IsNClique (k + 1) T := by
  refine ⟨insert v S, ?_, h.insert ?_⟩
  · intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact hv
    · exact nonNbrIn_subset (hS hx)
  · intro b hb
    have hb' := mem_nonNbrIn.1 (hS hb)
    exact (G.compl_adj v b).2 ⟨fun h => hb'.1.2 h.symm, hb'.2⟩

/-- Handshake lemma, relative to a finite vertex set. -/
lemma even_sum_card_nbrIn (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    Even (∑ v ∈ W, (nbrIn G W v).card) := by
  induction W using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hstep : ∀ v ∈ s, (nbrIn G (insert a s) v).card
        = (nbrIn G s v).card + (if G.Adj v a then 1 else 0) := by
      intro v _
      simp only [nbrIn, Finset.filter_insert]
      by_cases h : G.Adj v a
      · simp only [if_pos h]
        rw [Finset.card_insert_of_notMem (fun hmem => ha (Finset.mem_filter.1 hmem).1)]
      · simp only [if_neg h, add_zero]
    have ha' : (nbrIn G (insert a s) a).card = (nbrIn G s a).card := by
      simp only [nbrIn, Finset.filter_insert, if_neg (G.irrefl : ¬ G.Adj a a)]
    have hcount : ∑ v ∈ s, (if G.Adj v a then 1 else 0) = (nbrIn G s a).card := by
      rw [← Finset.card_filter]
      congr 1
      apply Finset.filter_congr
      intro x _
      simp [G.adj_comm x a]
    rw [Finset.sum_insert ha, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ha', hcount]
    obtain ⟨k, hk⟩ := ih
    exact ⟨(nbrIn G s a).card + k, by omega⟩

/-- Unpacking the negation of `RamseyOn`. -/
lemma not_ramseyOn {s t : ℕ} {W : Finset V} (h : ¬ RamseyOn G s t W) :
    (∀ S ⊆ W, ¬ G.IsNClique s S) ∧ (∀ S ⊆ W, ¬ Gᶜ.IsNClique t S) :=
  ⟨fun S hS hc => h (Or.inl ⟨S, hS, hc⟩), fun S hS hc => h (Or.inr ⟨S, hS, hc⟩)⟩

/-- `R(3,3) ≤ 6`, locally. -/
lemma ramsey_three_three (W : Finset V) (hW : 6 ≤ W.card) : RamseyOn G 3 3 W := by
  by_contra hcon
  obtain ⟨h3, h3'⟩ := not_ramseyOn hcon
  obtain ⟨v, hv⟩ := card_pos.1 (show 0 < W.card by omega)
  have hsplit := card_nbrIn_add_card_nonNbrIn (G := G) hv
  rcases le_or_gt 3 (nbrIn G W v).card with hA | hA
  · obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hA
    refine h3' S (hS.trans nbrIn_subset) ⟨?_, hcard⟩
    exact (isClique_compl_nbrIn hv h3).subset (by exact_mod_cast hS)
  · have hB : 3 ≤ (nonNbrIn G W v).card := by omega
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hB
    by_cases hcl : G.IsClique (S : Set V)
    · exact h3 S (hS.trans nonNbrIn_subset) ⟨hcl, hcard⟩
    · rw [G.isClique_iff, Set.Pairwise] at hcl
      push_neg at hcl
      obtain ⟨a, ha, b, hb, hab, hnadj⟩ := hcl
      have hpair : Gᶜ.IsNClique 2 ({a, b} : Finset V) := by
        refine ⟨?_, card_pair hab⟩
        simp only [coe_insert, coe_singleton]
        exact isClique_pair.2 (fun _ => (G.compl_adj a b).2 ⟨hab, hnadj⟩)
      have hsub : ({a, b} : Finset V) ⊆ nonNbrIn G W v := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hS (mem_coe.1 ha)
        · rw [mem_singleton] at hx
          subst hx
          exact hS (mem_coe.1 hb)
      obtain ⟨T, hT, hTc⟩ := indep_insert hv hsub hpair
      exact h3' T hT hTc

/-- `R(3,4) ≤ 9`, locally. -/
lemma ramsey_three_four (W : Finset V) (hW : 9 ≤ W.card) : RamseyOn G 3 4 W := by
  obtain ⟨W', hW', hcard⟩ := exists_subset_card_eq hW
  refine RamseyOn.mono hW' ?_
  by_contra hcon
  obtain ⟨h3, h4⟩ := not_ramseyOn hcon
  have key : ∀ v ∈ W', (nbrIn G W' v).card = 3 := by
    intro v hv
    have hsplit := card_nbrIn_add_card_nonNbrIn (G := G) hv
    have hle : (nbrIn G W' v).card ≤ 3 := by
      by_contra hc
      push_neg at hc
      obtain ⟨S, hS, hs⟩ := exists_subset_card_eq (show 4 ≤ (nbrIn G W' v).card by omega)
      exact h4 S (hS.trans nbrIn_subset)
        ⟨(isClique_compl_nbrIn hv h3).subset (by exact_mod_cast hS), hs⟩
    have hge : 3 ≤ (nbrIn G W' v).card := by
      by_contra hc
      push_neg at hc
      have hB : 6 ≤ (nonNbrIn G W' v).card := by omega
      rcases ramsey_three_three (G := G) (nonNbrIn G W' v) hB with ⟨S, hS, hcl⟩ | ⟨S, hS, hcl⟩
      · exact h3 S (hS.trans nonNbrIn_subset) hcl
      · obtain ⟨T, hT, hTc⟩ := indep_insert hv hS hcl
        exact h4 T hT hTc
    omega
  have hsum : ∑ v ∈ W', (nbrIn G W' v).card = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hcard]
    rfl
  have heven := even_sum_card_nbrIn G W'
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

/-- `R(3,5) ≤ 14`, locally. -/
lemma ramsey_three_five (W : Finset V) (hW : 14 ≤ W.card) : RamseyOn G 3 5 W := by
  by_contra hcon
  obtain ⟨h3, h5⟩ := not_ramseyOn hcon
  obtain ⟨v, hv⟩ := card_pos.1 (show 0 < W.card by omega)
  have hsplit := card_nbrIn_add_card_nonNbrIn (G := G) hv
  have hA : (nbrIn G W v).card ≤ 4 := by
    by_contra hc
    push_neg at hc
    obtain ⟨S, hS, hs⟩ := exists_subset_card_eq (show 5 ≤ (nbrIn G W v).card by omega)
    exact h5 S (hS.trans nbrIn_subset)
      ⟨(isClique_compl_nbrIn hv h3).subset (by exact_mod_cast hS), hs⟩
  have hB : 9 ≤ (nonNbrIn G W v).card := by omega
  rcases ramsey_three_four (G := G) (nonNbrIn G W v) hB with ⟨S, hS, hc⟩ | ⟨S, hS, hc⟩
  · exact h3 S (hS.trans nonNbrIn_subset) hc
  · obtain ⟨T, hT, hTc⟩ := indep_insert hv hS hc
    exact h5 T hT hTc

end Local

/-! ## The extremal graph on 13 vertices -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
def adj13 (i j : Fin 13) : Bool := ((i.val + 13 - j.val) % 13) ∈ [1, 5, 8, 12]

/-- The circulant graph `C₁₃(1,5)`: it is triangle-free and has independence number `4`. -/
def G13 : SimpleGraph (Fin 13) where
  Adj i j := adj13 i j
  symm := by intro i j; revert i j; decide
  loopless := ⟨by decide⟩

instance : DecidableRel G13.Adj := fun i j => inferInstanceAs (Decidable (adj13 i j = true))

/-- `C₁₃(1,5)` has no triangle (checked by exhaustion over triples). -/
lemma adj13_no_triangle : ∀ i j k : Fin 13, ¬ (adj13 i j ∧ adj13 j k ∧ adj13 i k) := by decide

/-- Any five vertices of `C₁₃(1,5)` contain an edge (checked by exhaustion). -/
lemma adj13_no_indep_five : ∀ a b c d e : Fin 13, a < b → b < c → c < d → d < e →
    (adj13 a b || adj13 a c || adj13 a d || adj13 a e || adj13 b c || adj13 b d || adj13 b e
      || adj13 c d || adj13 c e || adj13 d e) = true := by
  decide +kernel

lemma G13_cliqueFree_three : G13.CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.1 hS.2
  have h := SimpleGraph.is3Clique_triple_iff.1 hS
  exact adj13_no_triangle a b c ⟨h.1, h.2.2, h.2.1⟩

lemma G13_compl_cliqueFree_five : G13ᶜ.CliqueFree 5 := by
  intro S hS
  obtain ⟨hcl, hcard⟩ := hS
  set f := S.orderIsoOfFin hcard with hf
  have hmono : ∀ i j : Fin 5, i < j → ((f i : Fin 13) < (f j : Fin 13)) :=
    fun i j hij => f.lt_iff_lt.2 hij
  have key : ∀ i j : Fin 5, i ≠ j → adj13 (f i : Fin 13) (f j : Fin 13) ≠ true := by
    intro i j hij hadj
    have hne : (f i : Fin 13) ≠ (f j : Fin 13) := fun h =>
      hij (f.injective (Subtype.ext h))
    have := hcl (Finset.mem_coe.2 (f i).2) (Finset.mem_coe.2 (f j).2) hne
    exact ((G13.compl_adj _ _).1 this).2 hadj
  have h := adj13_no_indep_five (f 0) (f 1) (f 2) (f 3) (f 4)
    (hmono 0 1 (by decide)) (hmono 1 2 (by decide)) (hmono 2 3 (by decide))
    (hmono 3 4 (by decide))
  simp only [Bool.or_eq_true, or_assoc] at h
  rcases h with h|h|h|h|h|h|h|h|h|h <;> exact key _ _ (by decide) h

/-! ## The Ramsey number -/

/-- `IsRamseyNum s t n` says that every graph on `n` vertices contains an `s`-clique or
an independent set of size `t`. -/
def IsRamseyNum (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t

/-- **The Ramsey number `R(3,5)` equals `14`**: `14` is the least `n` such that every
two-colouring of the edges of `Kₙ` contains a red triangle or a blue `K₅`. -/
theorem ramsey_3_5 : IsLeast {n | IsRamseyNum 3 5 n} 14 := by
  constructor
  · intro G
    classical
    rcases ramsey_three_five (G := G) Finset.univ (by simp) with ⟨S, _, hc⟩ | ⟨S, _, hc⟩
    · exact Or.inl (fun h => h S hc)
    · exact Or.inr (fun h => h S hc)
  · intro n hn
    by_contra hlt
    push_neg at hlt
    have hle : n ≤ 13 := by omega
    set f : Fin n ↪ Fin 13 := Fin.castLEEmb hle with hfdef
    have hcf3 : (SimpleGraph.comap f G13).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap f G13) G13_cliqueFree_three
    have hemb : (SimpleGraph.comap f G13)ᶜ ↪g G13ᶜ := by
      refine ⟨f, ?_⟩
      intro a b
      simp [SimpleGraph.comap_adj, f.injective.ne_iff]
    have hcf5 : ((SimpleGraph.comap f G13)ᶜ).CliqueFree 5 :=
      SimpleGraph.CliqueFree.comap hemb G13_compl_cliqueFree_five
    rcases hn (SimpleGraph.comap f G13) with h | h
    · exact h hcf3
    · exact h hcf5

end Math

