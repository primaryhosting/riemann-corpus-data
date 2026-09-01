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

namespace Math

/-- `RamseyProp s t n` says that for every graph `G` on `n` vertices (equivalently, every
two-colouring of the edges of the complete graph on `n` vertices) either `G` contains a clique
of size `s`, or the complement of `G` contains a clique of size `t` (i.e. `G` contains an
independent set of size `t`). -/
def RamseyProp (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t

/-- The two-colour Ramsey number `R(s, t)`: the least `n` such that `RamseyProp s t n` holds. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := sInf {n | RamseyProp s t n}

/-- `RamseyProp` is monotone in the number of vertices. -/
theorem RamseyProp.mono {s t m n : ℕ} (h : m ≤ n) (hm : RamseyProp s t m) :
    RamseyProp s t n := by
  intro G
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have hcompl : (SimpleGraph.comap (⇑(Fin.castLEEmb h)) G)ᶜ
      = SimpleGraph.comap (⇑(Fin.castLEEmb h)) Gᶜ := by
    ext a b; simp [SimpleGraph.comap]
  rcases hm (SimpleGraph.comap (⇑(Fin.castLEEmb h)) G) with hk | hk
  · exact hk (h1.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb h) G))
  · exact hk (hcompl ▸ h2.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb h) Gᶜ))

/-- In a triangle-free graph, every set of at least `6` vertices contains an independent set
of size `3`.  (This is the content of `R(3,3) ≤ 6`.) -/
theorem exists_indep_three {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (htri : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (s : Finset V) (hs : 6 ≤ s.card) :
    ∃ t ⊆ s, t.card = 3 ∧ ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hs' : 5 ≤ (s.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hcount := Finset.card_filter_add_card_filter_not (s := s.erase v) (fun x => G.Adj v x)
  by_cases hA : 3 ≤ ((s.erase v).filter (fun x => G.Adj v x)).card
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA
    refine ⟨t, ?_, htc, ?_⟩
    · intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hts hx)).1
    · intro a ha b hb _ hadj
      exact htri v a b (Finset.mem_filter.mp (hts ha)).2 (Finset.mem_filter.mp (hts hb)).2 hadj
  · have hB : 3 ≤ ((s.erase v).filter (fun x => ¬ G.Adj v x)).card := by omega
    obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hB
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp huc
    have key : ∀ x y : V, x ≠ y → x ∈ ({a, b, c} : Finset V) → y ∈ ({a, b, c} : Finset V) →
        ¬ G.Adj x y → ∃ t ⊆ s, t.card = 3 ∧ ∀ p ∈ t, ∀ q ∈ t, p ≠ q → ¬ G.Adj p q := by
      intro x y hxy hx hy hnadj
      have hx' := Finset.mem_filter.mp (hus hx)
      have hy' := Finset.mem_filter.mp (hus hy)
      have hxv : x ≠ v := (Finset.mem_erase.mp hx'.1).1
      have hyv : y ≠ v := (Finset.mem_erase.mp hy'.1).1
      refine ⟨{v, x, y}, ?_, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hv
        · exact (Finset.mem_erase.mp hx'.1).2
        · exact (Finset.mem_erase.mp hy'.1).2
      · rw [Finset.card_insert_of_notMem (by simp [Ne.symm hxv, Ne.symm hyv]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      · intro p hp q hq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
          simp_all <;>
          first
            | exact hx'.2
            | exact hy'.2
            | exact fun h => hx'.2 h.symm
            | exact fun h => hy'.2 h.symm
            | exact hnadj
            | exact fun h => hnadj h.symm
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · exact key b c hbc (by simp) (by simp) (fun h => htri a b c h1 h2 h)
      · exact key a c hac (by simp) (by simp) h2
    · exact key a b hab (by simp) (by simp) h1

/-- Upper bound: `R(3,4) ≤ 9`. -/
theorem ramseyProp_three_four_nine : RamseyProp 3 4 9 := by
  intro G
  by_contra hc
  push_neg at hc
  obtain ⟨hT, hI⟩ := hc
  classical
  have htri : ∀ a b c : Fin 9, G.Adj a b → G.Adj a c → G.Adj b c → False := by
    intro a b c h1 h2 h3
    exact hT {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
  have hind : ∀ t : Finset (Fin 9), t.card = 4 →
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b) → False := by
    intro t ht hpw
    exact hI t ⟨fun a ha b hb hab => ⟨hab, hpw a ha b hb hab⟩, ht⟩
  -- No vertex has degree `≥ 4`: its neighbourhood would be an independent set of size `4`.
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push_neg at hlt
    have h4 : 4 ≤ (G.neighborFinset v).card := hlt
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h4
    refine hind t htc ?_
    intro a ha b hb _ hadj
    exact htri v a b (SimpleGraph.mem_neighborFinset .. |>.mp (hts ha))
      (SimpleGraph.mem_neighborFinset .. |>.mp (hts hb)) hadj
  -- No vertex has degree `≤ 2`: the `≥ 6` non-neighbours contain an independent set of size `3`,
  -- which together with the vertex gives an independent set of size `4`.
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    have hdv : (G.neighborFinset v).card = G.degree v := rfl
    have hcard : 6 ≤ (Finset.univ \ insert v (G.neighborFinset v)).card := by
      have h1 := Finset.card_insert_le v (G.neighborFinset v)
      have h2 := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (insert v (G.neighborFinset v)))
      have h3 : (Finset.univ : Finset (Fin 9)).card = 9 := by simp
      omega
    obtain ⟨t, hts, htc, hpw⟩ := exists_indep_three G htri _ hcard
    have hmem : ∀ x ∈ t, x ≠ v ∧ ¬ G.Adj v x := by
      intro x hx
      have hx' := hts hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        SimpleGraph.mem_neighborFinset, not_or] at hx'
      exact hx'
    have hvt : v ∉ t := fun h => (hmem v h).1 rfl
    refine hind (insert v t) ?_ ?_
    · rw [Finset.card_insert_of_notMem hvt, htc]
    · intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact (hmem b hb).2
      · rcases hb with rfl | hb
        · exact fun h => (hmem a ha).2 h.symm
        · exact hpw a ha b hb hab
  -- Hence the graph is `3`-regular on `9` vertices, contradicting the handshake lemma.
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp at hsum
  omega

/-- The circulant graph `C₈(1,4)` (the Wagner graph): vertices `Fin 8`, with `a` joined to `b`
iff `b - a ∈ {1, 4, 7}`. -/
def wagner : SimpleGraph (Fin 8) where
  Adj a b := b - a = 1 ∨ b - a = 7 ∨ b - a = 4
  symm := by unfold Symmetric; decide
  loopless := ⟨by decide⟩

instance : DecidableRel wagner.Adj := fun a b => by
  show Decidable (b - a = 1 ∨ b - a = 7 ∨ b - a = 4); infer_instance

instance (n : ℕ) : Decidable (wagner.CliqueFree n) := by
  unfold SimpleGraph.CliqueFree; infer_instance

instance (n : ℕ) : Decidable ((wagnerᶜ).CliqueFree n) := by
  unfold SimpleGraph.CliqueFree; infer_instance

set_option maxRecDepth 100000 in
theorem wagner_cliqueFree_three : wagner.CliqueFree 3 := by decide

set_option maxRecDepth 100000 in
theorem wagner_compl_cliqueFree_four : (wagnerᶜ).CliqueFree 4 := by decide

/-- Lower bound: `R(3,4) > 8`, witnessed by the Wagner graph. -/
theorem not_ramseyProp_three_four_eight : ¬ RamseyProp 3 4 8 := by
  intro h
  rcases h wagner with h | h
  · exact h wagner_cliqueFree_three
  · exact h wagner_compl_cliqueFree_four

/-- **The Ramsey number `R(3,4)` equals `9`.** -/
theorem ramsey_3_4 : ramseyNumber 3 4 = 9 := by
  have hne : {n : ℕ | RamseyProp 3 4 n}.Nonempty := ⟨9, ramseyProp_three_four_nine⟩
  refine le_antisymm (Nat.sInf_le ramseyProp_three_four_nine) ?_
  by_contra hlt
  push_neg at hlt
  rw [ramseyNumber] at hlt
  have hmem : RamseyProp 3 4 (sInf {n : ℕ | RamseyProp 3 4 n}) := Nat.sInf_mem hne
  exact not_ramseyProp_three_four_eight (hmem.mono (by omega))

end Math

