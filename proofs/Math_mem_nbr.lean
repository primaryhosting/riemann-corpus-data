import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option autoImplicit false

namespace Math

open Finset SimpleGraph

/-!
## Formulation

A two-colouring of the edges of the complete graph on `Fin n` is encoded by a simple graph `G`:
the edges of `G` are the "red" edges and the edges of the complement `Gᶜ` are the "blue" ones.
`RamseyProp n r b` says that every such colouring contains a red `r`-clique or a blue `b`-clique.
The Ramsey number `R(r, b)` is the least `n` for which `RamseyProp n r b` holds.

The final result, `Math.ramsey_3_5`, states that `R(3,5) = 14`, i.e. `14` is the least element
of `{n | RamseyProp n 3 5}`.
-/

/-- `RamseyProp n r b` holds when every simple graph on `Fin n` contains a clique of size `r`
or an independent set of size `b` (i.e. a clique of size `b` in the complement). -/
def RamseyProp (n r b : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique r s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique b s)

/-! ## Neighbourhoods inside a finite set of vertices -/

open scoped Classical in
/-- The set of neighbours of `v` inside the finite set `s`. -/
noncomputable def nbr {V : Type*} (G : SimpleGraph V) (s : Finset V) (v : V) : Finset V :=
  s.filter (fun w => G.Adj v w)

variable {V : Type*} {G : SimpleGraph V} {s : Finset V} {v : V}

lemma mem_nbr {w : V} : w ∈ nbr G s v ↔ w ∈ s ∧ G.Adj v w := by
  classical
  simp [nbr]

lemma nbr_subset : nbr G s v ⊆ s := fun _ hw => (mem_nbr.1 hw).1

lemma coe_nbr_subset : (↑(nbr G s v) : Set V) ⊆ (↑s : Set V) := by
  exact_mod_cast nbr_subset

/-- Inside `s`, the neighbours of `v`, the non-neighbours of `v` and `v` itself
account for all of `s`. -/
lemma card_nbr_add_card_nbr_compl (hv : v ∈ s) :
    (nbr G s v).card + (nbr Gᶜ s v).card + 1 = s.card := by
  classical
  have hdisj : Disjoint (nbr G s v) (nbr Gᶜ s v) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact (mem_nbr.1 ha').2.2 (mem_nbr.1 ha).2
  have hunion : (nbr G s v) ∪ (nbr Gᶜ s v) = s.erase v := by
    ext w
    simp only [Finset.mem_union, mem_nbr, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro (⟨hw, h⟩ | ⟨hw, h1, _⟩)
      · exact ⟨fun hh => G.ne_of_adj h hh.symm, hw⟩
      · exact ⟨fun hh => h1 hh.symm, hw⟩
    · rintro ⟨hne, hw⟩
      by_cases h : G.Adj v w
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, ⟨fun hh => hne hh.symm, h⟩⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem hv] at hcard
  have hpos : 1 ≤ s.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

/-- If `G` has no triangle inside `s`, the neighbourhood of `v` is a clique of the complement,
so it is small whenever the complement has no large clique. -/
lemma card_nbr_lt {k : ℕ} (h3 : G.CliqueFreeOn (↑s) 3) (hk : Gᶜ.CliqueFreeOn (↑s) k)
    (hv : v ∈ s) : (nbr G s v).card < k := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcon
  refine hk (t := t) ?_ ⟨?_, htc⟩
  · intro a ha
    exact nbr_subset (hts ha)
  · intro a ha b hb hab
    have ha' := mem_nbr.1 (hts ha)
    have hb' := mem_nbr.1 (hts hb)
    refine ⟨hab, ?_⟩
    intro hGab
    refine h3 (t := ({v, a, b} : Finset V)) ?_ ?_
    · intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact ha'.1
      · exact hb'.1
    · exact SimpleGraph.is3Clique_triple_iff.2 ⟨ha'.2, hb'.2, hGab⟩

/-- A blue clique inside the blue neighbourhood of `v`, together with `v`, is a bigger
blue clique. -/
lemma cliqueFreeOn_nbr_compl {k : ℕ} (hk : Gᶜ.CliqueFreeOn (↑s) (k + 1)) (hv : v ∈ s) :
    Gᶜ.CliqueFreeOn (↑(nbr Gᶜ s v)) k := by
  classical
  intro t ht hclique
  have hvt : v ∉ t := fun hvt => (mem_nbr.1 (ht hvt)).2.1 rfl
  refine hk (t := insert v t) ?_ ?_
  · intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact hv
    · exact nbr_subset (ht hx)
  · exact hclique.insert (fun b hb => (mem_nbr.1 (ht hb)).2)

/-! ## A handshake lemma for a finite set of vertices -/

/-- The sum over `v ∈ s` of the number of neighbours of `v` inside `s` is even:
each edge inside `s` is counted from both of its ends. -/
lemma even_sum_card_nbr (G : SimpleGraph V) (s : Finset V) :
    Even (∑ v ∈ s, (nbr G s v).card) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
    have hself : nbr G (insert a t) a = nbr G t a := by
      ext w
      simp only [mem_nbr, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hw, h⟩
        · exact absurd rfl (G.ne_of_adj h)
        · exact ⟨hw, h⟩
      · rintro ⟨hw, h⟩; exact ⟨Or.inr hw, h⟩
    have hstep : ∀ v ∈ t, (nbr G (insert a t) v).card
        = (nbr G t v).card + (if G.Adj v a then 1 else 0) := by
      intro v _
      by_cases h : G.Adj v a
      · have heq : nbr G (insert a t) v = insert a (nbr G t v) := by
          ext w
          simp only [mem_nbr, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hw, h'⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hw, h'⟩
          · rintro (rfl | ⟨hw, h'⟩)
            · exact ⟨Or.inl rfl, h⟩
            · exact ⟨Or.inr hw, h'⟩
        rw [heq, Finset.card_insert_of_notMem (fun hh => hat (mem_nbr.1 hh).1), if_pos h]
      · have heq : nbr G (insert a t) v = nbr G t v := by
          ext w
          simp only [mem_nbr, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hw, h'⟩
            · exact absurd h' h
            · exact ⟨hw, h'⟩
          · rintro ⟨hw, h'⟩; exact ⟨Or.inr hw, h'⟩
        rw [heq, if_neg h, Nat.add_zero]
    rw [Finset.sum_insert hat, hself, Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    have hcount : (∑ v ∈ t, if G.Adj v a then 1 else 0) = (nbr G t a).card := by
      rw [show (nbr G t a) = t.filter (fun w => G.Adj a w) from rfl, Finset.card_filter]
      exact Finset.sum_congr rfl (fun v _ => by simp [SimpleGraph.adj_comm])
    rw [hcount]
    have hre : (nbr G t a).card + ((∑ v ∈ t, (nbr G t v).card) + (nbr G t a).card)
        = 2 * (nbr G t a).card + (∑ v ∈ t, (nbr G t v).card) := by ring
    rw [hre]
    exact (even_two_mul _).add ih

/-! ## The upper bounds `R(3,3) ≤ 6`, `R(3,4) ≤ 9` and `R(3,5) ≤ 14` -/

/-- `R(3,3) ≤ 6`: a set of vertices containing no red triangle and no blue triangle
has at most `5` elements. -/
lemma ramsey_33_le (h3 : G.CliqueFreeOn (↑s) 3) (h3' : Gᶜ.CliqueFreeOn (↑s) 3) : s.card ≤ 5 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp
  · have h1 := card_nbr_lt h3 h3' hv
    have h2 := card_nbr_lt (G := Gᶜ) h3' (by rwa [compl_compl]) hv
    have h4 := card_nbr_add_card_nbr_compl (G := G) (s := s) (v := v) hv
    omega

/-- `R(3,4) ≤ 9`: a set of vertices containing no red triangle and no blue `4`-clique
has at most `8` elements.  On `9` vertices every red degree would have to be exactly `3`,
which is impossible by the handshake lemma. -/
lemma ramsey_34_le (h3 : G.CliqueFreeOn (↑s) 3) (h4 : Gᶜ.CliqueFreeOn (↑s) 4) : s.card ≤ 8 := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ s, (nbr G s v).card < 4 ∧ (nbr Gᶜ s v).card ≤ 5 ∧
      (nbr G s v).card + (nbr Gᶜ s v).card + 1 = s.card := by
    intro v hv
    refine ⟨card_nbr_lt h3 h4 hv, ?_, card_nbr_add_card_nbr_compl hv⟩
    refine ramsey_33_le (G := G) (s := nbr Gᶜ s v) ?_ ?_
    · exact SimpleGraph.CliqueFreeOn.subset G coe_nbr_subset h3
    · exact cliqueFreeOn_nbr_compl (k := 3) h4 hv
  obtain ⟨v0, hv0⟩ := Finset.card_pos.1 (show 0 < s.card by omega)
  have h9 : s.card = 9 := by have := key v0 hv0; omega
  have hdeg : ∀ v ∈ s, (nbr G s v).card = 3 := by
    intro v hv
    have := key v hv
    omega
  have hsum : (∑ v ∈ s, (nbr G s v).card) = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, h9]
    rfl
  obtain ⟨r, hr⟩ := even_sum_card_nbr G s
  omega

/-- `R(3,5) ≤ 14`: a set of vertices containing no red triangle and no blue `5`-clique
has at most `13` elements. -/
lemma ramsey_35_le (h3 : G.CliqueFreeOn (↑s) 3) (h5 : Gᶜ.CliqueFreeOn (↑s) 5) : s.card ≤ 13 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp
  · have h1 := card_nbr_lt h3 h5 hv
    have h2 : (nbr Gᶜ s v).card ≤ 8 := by
      refine ramsey_34_le (G := G) (s := nbr Gᶜ s v) ?_ ?_
      · exact SimpleGraph.CliqueFreeOn.subset G coe_nbr_subset h3
      · exact cliqueFreeOn_nbr_compl (k := 4) h5 hv
    have h4 := card_nbr_add_card_nbr_compl (G := G) (s := s) (v := v) hv
    omega

/-! ## The lower bound: the circulant graph `C₁₃(1,5)`

It is triangle free and its complement contains no `5`-clique, i.e. its independence
number is `4`.  The two finite verifications are carried out by Boolean computations
over `List.range 13`, checked by the kernel. -/

/-- Adjacency in the circulant graph `C₁₃(1,5)`, as a Boolean function of the residues:
`i` and `j` are adjacent iff they differ by `±1` or `±5` modulo `13`. -/
def adjb (i j : ℕ) : Bool :=
  let d := (i + 13 - j) % 13
  d == 1 || d == 5 || d == 8 || d == 12

lemma of_all13 {p : ℕ → Bool} (h : ((List.range 13).all p) = true) {i : ℕ} (hi : i < 13) :
    p i = true := List.all_eq_true.1 h i (List.mem_range.2 hi)

/-- Symmetry of `adjb` on residues `< 13`. -/
def symCheck : Bool :=
  (List.range 13).all fun i => (List.range 13).all fun j => !adjb i j || adjb j i

/-- Irreflexivity of `adjb` on residues `< 13`. -/
def irrCheck : Bool := (List.range 13).all fun i => !adjb i i

theorem symOK : symCheck = true := by decide

theorem irrOK : irrCheck = true := by decide

/-- The circulant graph `C₁₃(1,5)` on `Fin 13`. -/
def G13 : SimpleGraph (Fin 13) where
  Adj i j := adjb i.val j.val = true
  symm := by
    intro i j h
    have h2 := of_all13 (of_all13 symOK i.isLt) j.isLt
    simp only [] at h2
    simp [h] at h2
    exact h2
  loopless := ⟨by
    intro i h
    have h2 := of_all13 irrOK i.isLt
    simp [h] at h2⟩

lemma G13_adj_iff {i j : Fin 13} : G13.Adj i j ↔ adjb i.val j.val = true := Iff.rfl

/-- There is no triangle among residues `< 13`. -/
def triCheck : Bool :=
  (List.range 13).all fun a => (List.range 13).all fun b => (List.range 13).all fun c =>
    (a == b) || (a == c) || (b == c) || !adjb a b || !adjb a c || !adjb b c

theorem triOK : triCheck = true := by decide

/-- Among any five residues `a < b < c < d < e` below `13` some two are adjacent. -/
def ind5Check : Bool :=
  (List.range 13).all fun a => (List.range 13).all fun b => !(decide (a < b)) ||
    (List.range 13).all fun c => !(decide (b < c)) ||
      (List.range 13).all fun d => !(decide (c < d)) ||
        (List.range 13).all fun e => !(decide (d < e)) ||
          adjb a b || adjb a c || adjb a d || adjb a e || adjb b c || adjb b d ||
            adjb b e || adjb c d || adjb c e || adjb d e

theorem ind5OK : ind5Check = true := by decide

lemma G13_no_triangle (a b c : Fin 13) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (G13.Adj a b ∧ G13.Adj a c ∧ G13.Adj b c) := by
  rintro ⟨h1, h2, h3⟩
  rw [G13_adj_iff] at h1 h2 h3
  have h := of_all13 (of_all13 (of_all13 triOK a.isLt) b.isLt) c.isLt
  simp only [] at h
  simp [h1, h2, h3, Fin.val_eq_val, hab, hac, hbc] at h

lemma G13_no_indep5 (a b c d e : Fin 13) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) :
    G13.Adj a b ∨ G13.Adj a c ∨ G13.Adj a d ∨ G13.Adj a e ∨ G13.Adj b c ∨ G13.Adj b d ∨
      G13.Adj b e ∨ G13.Adj c d ∨ G13.Adj c e ∨ G13.Adj d e := by
  rw [Fin.lt_def] at h1 h2 h3 h4
  have k := of_all13 (of_all13 ind5OK a.isLt) b.isLt
  simp only [h1, decide_true, Bool.not_true, Bool.false_or] at k
  have k2 := of_all13 k c.isLt
  simp only [h2, decide_true, Bool.not_true, Bool.false_or] at k2
  have k3 := of_all13 k2 d.isLt
  simp only [h3, decide_true, Bool.not_true, Bool.false_or] at k3
  have k4 := of_all13 k3 e.isLt
  simp only [h4, decide_true, Bool.not_true, Bool.false_or] at k4
  simp only [G13_adj_iff]
  simp only [Bool.or_eq_true] at k4
  tauto

/-- `C₁₃(1,5)` is triangle free. -/
lemma G13_cliqueFree_3 : G13.CliqueFree 3 := by
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hs.2
  exact G13_no_triangle x y z hxy hxz hyz (SimpleGraph.is3Clique_triple_iff.1 hs)

/-- `C₁₃(1,5)` has no independent set of size `5`. -/
lemma G13_compl_cliqueFree_5 : G13ᶜ.CliqueFree 5 := by
  intro s hs
  set f := s.orderEmbOfFin hs.2
  have hmem : ∀ i, f i ∈ s := fun i => Finset.orderEmbOfFin_mem s hs.2 i
  have hlt : ∀ i j : Fin 5, i < j → f i < f j := fun i j h => f.lt_iff_lt.2 h
  have hadj : ∀ i j : Fin 5, i ≠ j → G13ᶜ.Adj (f i) (f j) := by
    intro i j h
    exact hs.1 (Finset.mem_coe.2 (hmem i)) (Finset.mem_coe.2 (hmem j))
      (fun e => h (f.injective e))
  rcases G13_no_indep5 (f 0) (f 1) (f 2) (f 3) (f 4) (hlt 0 1 (by decide))
      (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide)) with
    h | h | h | h | h | h | h | h | h | h
  · exact ((hadj 0 1 (by decide)).2) h
  · exact ((hadj 0 2 (by decide)).2) h
  · exact ((hadj 0 3 (by decide)).2) h
  · exact ((hadj 0 4 (by decide)).2) h
  · exact ((hadj 1 2 (by decide)).2) h
  · exact ((hadj 1 3 (by decide)).2) h
  · exact ((hadj 1 4 (by decide)).2) h
  · exact ((hadj 2 3 (by decide)).2) h
  · exact ((hadj 2 4 (by decide)).2) h
  · exact ((hadj 3 4 (by decide)).2) h

/-! ## The two halves of the theorem -/

/-- Every red/blue colouring of the edges of `K₁₄` has a red triangle or a blue `5`-clique. -/
lemma ramseyProp_14 : RamseyProp 14 3 5 := by
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨hr, hb⟩ := hcon
  have h3 : G.CliqueFreeOn (↑(Finset.univ : Finset (Fin 14))) 3 :=
    fun t _ ht => hr t ht
  have h5 : Gᶜ.CliqueFreeOn (↑(Finset.univ : Finset (Fin 14))) 5 :=
    fun t _ ht => hb t ht
  have hle := ramsey_35_le h3 h5
  simp [Finset.card_univ] at hle

/-- For `n ≤ 13` there is a colouring of `Kₙ` with no red triangle and no blue `5`-clique,
namely (the restriction of) the circulant graph `C₁₃(1,5)`. -/
lemma not_ramseyProp_of_le_13 {n : ℕ} (hn : n ≤ 13) : ¬ RamseyProp n 3 5 := by
  intro h
  set f : Fin n ↪ Fin 13 := Fin.castLEEmb hn
  set G : SimpleGraph (Fin n) := SimpleGraph.comap f G13 with hG
  have emb1 : G ↪g G13 := SimpleGraph.Embedding.comap f G13
  have emb2 : Gᶜ ↪g G13ᶜ := by
    refine ⟨f, ?_⟩
    intro a b
    simp [hG, SimpleGraph.comap, f.injective.ne_iff]
  rcases h G with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact (G13_cliqueFree_3.comap emb1) t ht
  · exact (G13_compl_cliqueFree_5.comap emb2) t ht

/-- **The Ramsey number `R(3,5)` is `14`**: every two-colouring of the edges of the complete
graph on `14` vertices contains a red triangle or a blue `5`-clique, and `14` is the least
number of vertices with this property. -/
theorem ramsey_3_5 : IsLeast {n : ℕ | RamseyProp n 3 5} 14 := by
  constructor
  · exact ramseyProp_14
  · intro n hn
    by_contra hlt
    exact not_ramseyProp_of_le_13 (by omega) hn

end Math

