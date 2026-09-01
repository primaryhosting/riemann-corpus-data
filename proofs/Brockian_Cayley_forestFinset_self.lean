import Mathlib

namespace Brockian.Cayley

open Finset

/-!
# Cayley's formula

The number of labeled trees on `n` vertices is `n ^ (n - 2)`.

The proof goes through *rooted forests*, encoded as "parent functions": a rooted forest on a
vertex set `A` with set of roots `S ⊆ A` is a function `f : V → V` which fixes everything
outside `A \ S`, maps `A \ S` into `A`, and such that iterating `f` from any vertex of `A`
eventually lands in `S`.

The main counting statement is
`|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)`,
proved by induction on `|A|` (deleting a root and summing over the set of its children).

Specialising to `A = univ` and `S = {0}` in `Fin n` and putting rooted forests with a single
root in bijection with trees gives Cayley's formula.
-/

/-! ### Rooted forests, encoded by parent functions -/

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsForest A S f` says that `f` is the parent function of a rooted forest on the vertex
set `A` whose set of roots is `S`. -/
structure IsForest (A S : Finset V) (f : V → V) : Prop where
  /-- Vertices which are not non-root vertices of the forest are fixed. -/
  fixed : ∀ v, v ∉ A \ S → f v = v
  /-- The parent of a non-root vertex is a vertex. -/
  maps : ∀ v ∈ A \ S, f v ∈ A
  /-- Iterating the parent function eventually reaches a root. -/
  reaches : ∀ v ∈ A, ∃ m, f^[m] v ∈ S

/-- The finset of rooted forests on `A` with roots `S`, encoded by parent functions. -/
noncomputable def forestFinset (A S : Finset V) : Finset (V → V) :=
  @Finset.filter _ (IsForest A S) (Classical.decPred _) Finset.univ

@[simp] lemma mem_forestFinset {A S : Finset V} {f : V → V} :
    f ∈ forestFinset A S ↔ IsForest A S f := by
  classical
  simp [forestFinset]

/-- If all vertices are roots, the only forest is the identity. -/
lemma forestFinset_self (A : Finset V) : forestFinset A A = {id} := by
  ext f
  simp only [mem_forestFinset, Finset.mem_singleton]
  constructor
  · intro hf
    ext v
    exact hf.fixed v (by simp)
  · rintro rfl
    exact ⟨fun v _ => rfl, fun v hv => by simp at hv, fun v hv => ⟨0, hv⟩⟩

/-- With no roots and at least one vertex there is no forest. -/
lemma forestFinset_empty_roots {A : Finset V} (hA : A.Nonempty) : forestFinset A ∅ = ∅ := by
  ext f
  simp only [mem_forestFinset, Finset.notMem_empty, iff_false]
  rintro ⟨-, -, hreaches⟩
  obtain ⟨v, hv⟩ := hA
  obtain ⟨m, hm⟩ := hreaches v hv
  exact Finset.notMem_empty _ hm

/-! #### The two transport lemmas for reachability -/

omit [Fintype V] in
/-- Pushing reachability forward when the edges into `r` are cut. -/
lemma exists_iterate_mem_of_cut {f g : V → V} {C S S' : Finset V} {r : V}
    (hagree : ∀ v, v ∉ C → f v = g v) (hC : ∀ v ∈ C, f v = r) (hr : r ∈ S)
    (hS' : ∀ w ∈ S', w ∈ S ∨ w ∈ C) :
    ∀ (m : ℕ) (v : V), g^[m] v ∈ S' → ∃ m', f^[m'] v ∈ S := by
  -- First prove a helper: f^[k] v = g^[k] v as long as g^[i] v ∉ C for all i ≤ k
  have hagreem : ∀ k v, (∀ i ≤ k, g^[i] v ∉ C) → f^[k] v = g^[k] v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro v h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hgk : g^[k] v ∉ C := h k (Nat.le_succ k)
      rw [ih v (fun i hi => h i (Nat.le_succ_of_le hi)), hagree (g^[k] v) hgk]
  intro m v hgS'
  by_cases halt : ∀ i ≤ m, g^[i] v ∉ C
  · -- All iterates up to m are outside C, so f^[m] v = g^[m] v
    have hfmgm : f^[m] v = g^[m] v := hagreem m v halt
    by_cases hS : g^[m] v ∈ S
    · exact ⟨m, hfmgm ▸ hS⟩
    · have hCm : g^[m] v ∈ C := by simpa [hS] using hS' _ hgS'
      have hCm' : f^[m] v ∈ C := by rw [hfmgm]; exact hCm
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', show f (f^[m] v) = r from hC _ hCm']; exact hr⟩
  · -- Some iterate g^[i] v ∈ C for i ≤ m
    push_neg at halt
    -- Find the first i where g^[i] v ∈ C
    let i := Nat.find halt
    have hi_bound : i ≤ m := (Nat.find_spec halt).1
    have hi_mem : g^[i] v ∈ C := (Nat.find_spec halt).2
    -- All earlier iterates are outside C
    have hi_min : ∀ j < i, g^[j] v ∉ C := fun j hj h =>
      (Nat.find_min halt hj ⟨(Nat.le_of_lt hj).trans hi_bound, h⟩)
    -- So f^[i] v = g^[i] v (using agreem for i-1, then one more step)
    have hf_eq : f^[i] v = g^[i] v := by
      rcases i with ⟨ ⟩
      · simp
      · rename_i k
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hi_min' : ∀ j < k + 1, g^[j] v ∉ C := hi_min
        have hgik : g^[k] v ∉ C := hi_min' k (Nat.lt_succ_self k)
        rw [hagreem k v (fun j hj => hi_min' j (Nat.lt_of_le_of_lt hj (Nat.lt_succ_self k))),
            hagree (g^[k] v) hgik]
    -- Now use hf_eq and hi_mem to get f^[i+1] v = r ∈ S
    exact ⟨i + 1, by rw [Function.iterate_succ_apply', hf_eq]; rw [hC _ hi_mem]; exact hr⟩

omit [Fintype V] in
/-- Pulling reachability back when the edges into `r` are cut. -/
lemma exists_iterate_mem_of_cut' {f g : V → V} {C S S' : Finset V} {r : V}
    (hagree : ∀ v, v ∉ C → g v = f v) (hCS' : C ⊆ S') (hSr : ∀ w ∈ S, w ≠ r → w ∈ S')
    (hne : ∀ v, v ≠ r → v ∉ S → v ∉ C → f v ≠ r) :
    ∀ (m : ℕ) (v : V), v ≠ r → f^[m] v ∈ S → ∃ m', g^[m'] v ∈ S' := by
  intro m v hv hfm
  -- Key fact: if all iterates up to n are outside C, then g^[n] v = f^[n] v
  have iter_eq : ∀ n w, (∀ j < n, f^[j] w ∉ C) → g^[n] w = f^[n] w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro w h
      simp only [Function.iterate_succ_apply']
      rw [ih _ fun j hj => h j (Nat.lt_succ_of_lt hj)]
      apply hagree
      exact h n (Nat.lt_succ_self n)
  -- Use classical choice to find the minimum k where f^[k] v ∈ S ∪ C
  have hex : ∃ k, k ≤ m ∧ f^[k] v ∈ S ∪ C := ⟨m, le_refl m, Finset.mem_union_left _ hfm⟩
  let k := Nat.find hex
  have hkP : k ≤ m ∧ f^[k] v ∈ S ∪ C := Nat.find_spec hex
  have hk_le : k ≤ m := hkP.1
  have hksC : f^[k] v ∈ S ∪ C := hkP.2
  -- All previous iterates are outside S ∪ C
  have hbefore : ∀ j < k, f^[j] v ∉ S ∪ C := fun j hj hmem => Nat.find_min hex hj ⟨by omega, hmem⟩
  use k
  -- Since j < k implies f^[j] v ∉ C, we have g^[k] v = f^[k] v
  rw [iter_eq k v fun j hj => by
    intro hfjc
    exact hbefore j hj (by simp [Finset.mem_union]; right; exact hfjc)]
  -- Now g^[k] v = f^[k] v ∈ S ∪ C
  have hksC' := Finset.mem_union.mp hksC
  rcases hksC' with hktS | hktC
  · -- f^[k] v ∈ S
    by_cases hktr : f^[k] v = r
    · -- f^[k] v = r, contradiction with minimality of k
      -- Use strong induction to show this leads to v = r
      exfalso
      have : v = r := by
        have hall : ∀ n ≤ k, f^[n] v = r → v = r := by
          intro n hn hnr
          induction n using Nat.strong_induction_on with
          | _ m ih =>
            by_cases hm0 : m = 0
            · simp [hm0] at hnr
              exact hnr
            · have hm_pos : m > 0 := Nat.pos_of_ne_zero hm0
              have hfnm1 : f (f^[m-1] v) = r := by
                have heq : f^[m] v = f (f^[m-1] v) := by
                  conv_lhs => rw [show m = Nat.succ (m - 1) by omega]
                  exact Function.iterate_succ_apply' f (m - 1) v
                rw [← heq]; exact hnr
              have := hne (f^[m-1] v)
              by_cases hfm1 : f^[m-1] v = r
              · exact ih (m - 1) (by omega) (by omega) hfm1
              · have hfm1_not_S : f^[m-1] v ∉ S := fun h => hbefore (m - 1) (by omega) (Finset.mem_union_left _ h)
                have hfm1_not_C : f^[m-1] v ∉ C := fun h => hbefore (m - 1) (by omega) (Finset.mem_union_right _ h)
                exact absurd hfnm1 (this hfm1 hfm1_not_S hfm1_not_C)
        exact hall k (le_refl k) hktr
      exact hv this
    · exact hSr _ hktS hktr
  · -- f^[k] v ∈ C ⊆ S'
    exact hCS' hktC

/-! #### Cutting the edges into a root -/

/-- Cut the edges going into the root `r`: the children `C` of `r` become roots. -/
def cut (C : Finset V) (f : V → V) : V → V := fun v => if v ∈ C then v else f v

/-- Reattach the vertices of `C` to the root `r`. -/
def uncut (C : Finset V) (r : V) (g : V → V) : V → V := fun v => if v ∈ C then r else g v

/-- The set of children of the root `r` in the forest `f`. -/
def children (A S : Finset V) (r : V) (f : V → V) : Finset V := (A \ S).filter (fun v => f v = r)

omit [Fintype V] in
lemma children_subset {A S : Finset V} {r : V} {f : V → V} : children A S r f ⊆ A \ S :=
  Finset.filter_subset _ _

omit [Fintype V] in
lemma isForest_cut {A S : Finset V} {r : V} (hr : r ∈ S) {f : V → V}
    (hf : IsForest A S f) :
    IsForest (A.erase r) (S.erase r ∪ children A S r f) (cut (children A S r f) f) := by
  set C := children A S r f with hCdef
  have hmemC : ∀ v, v ∈ C ↔ (v ∈ A ∧ v ∉ S ∧ f v = r) := by
    intro v
    simp [hCdef, children, Finset.mem_filter, Finset.mem_sdiff, and_assoc]
  have hset : ∀ v, v ∈ (A.erase r) \ (S.erase r ∪ C) ↔ (v ∈ A ∧ v ∉ S ∧ v ∉ C) := by
    intro v
    constructor
    · intro h
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or] at h
      exact ⟨h.1.2, fun hvS => h.2.1 ⟨h.1.1, hvS⟩, h.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      have hvr : v ≠ r := fun hh => h2 (hh ▸ hr)
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or]
      exact ⟨⟨hvr, h1⟩, fun hcon => h2 hcon.2, h3⟩
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · by_cases hvC : v ∈ C
    · simp [cut, hvC]
    · have : v ∉ A \ S := by
        intro hcon
        exact hv ((hset v).2 ⟨(Finset.mem_sdiff.mp hcon).1, (Finset.mem_sdiff.mp hcon).2, hvC⟩)
      simp [cut, hvC, hf.fixed v this]
  · obtain ⟨hvA, hvS, hvC⟩ := (hset v).1 hv
    have hfv : f v ∈ A := hf.maps v (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩)
    have hne : f v ≠ r := fun hcon => hvC ((hmemC v).2 ⟨hvA, hvS, hcon⟩)
    simp only [cut, if_neg hvC]
    exact Finset.mem_erase.2 ⟨hne, hfv⟩
  · have hvA : v ∈ A := Finset.mem_of_mem_erase hv
    have hvr : v ≠ r := (Finset.mem_erase.mp hv).1
    obtain ⟨m, hm⟩ := hf.reaches v hvA
    refine exists_iterate_mem_of_cut' (f := f) (g := cut C f) (C := C) (S := S)
      (S' := S.erase r ∪ C) (r := r) ?_ ?_ ?_ ?_ m v hvr hm
    · intro w hw
      simp [cut, hw]
    · exact Finset.subset_union_right
    · intro w hwS hwr
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwr, hwS⟩)
    · intro w hwr hwS hwC hcon
      by_cases hwA : w ∈ A
      · exact hwC ((hmemC w).2 ⟨hwA, hwS, hcon⟩)
      · rw [hf.fixed w (fun hcon2 => hwA (Finset.mem_sdiff.mp hcon2).1)] at hcon
        exact hwr hcon

omit [Fintype V] in
lemma isForest_uncut {A S C : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) (hCA : C ⊆ A \ S)
    {g : V → V} (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : IsForest A S (uncut C r g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hvC : v ∉ C := fun h => hv (hCA h)
    simp [uncut, hvC]
    by_cases hvA : v ∈ A
    · by_cases hvS : v ∈ S
      · have hvnearerase : v ∉ A.erase r \ (S.erase r ∪ C) := by
          simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
          tauto
        exact hg.fixed v hvnearerase
      · exfalso; simp_all
    · have hvnearerase : v ∉ A.erase r := fun h => hvA (Finset.mem_of_mem_erase h)
      exact hg.fixed v (by simp_all)
  · intro v hv
    simp at hv
    by_cases hvC : v ∈ C
    · simp [uncut, hvC]; exact hSA hr
    · simp [uncut, hvC]
      have hvne : v ≠ r := fun h => hv.2 (h.symm ▸ hr)
      have hvAerase : v ∈ A.erase r := by simp [hv.1, hvne]
      have hvnotin : v ∉ S.erase r ∪ C := by simp_all [Finset.mem_union]
      exact Finset.mem_of_mem_erase (hg.maps v (Finset.mem_sdiff.mpr ⟨hvAerase, hvnotin⟩))
  · intro v hv
    by_cases hvS : v ∈ S
    · exact ⟨0, hvS⟩
    · -- v ∉ S, so we use exists_iterate_mem_of_cut
      have hvAerase : v ∈ A.erase r := by simp [hv]; intro hvr; exact hvS (hvr ▸ hr)
      obtain ⟨k, hk⟩ := hg.reaches v hvAerase
      -- the `uncut` function agrees with `g` off `C`, and sends `C` to the root `r`
      refine exists_iterate_mem_of_cut (f := uncut C r g) (g := g) (C := C) (S := S)
        (S' := S.erase r ∪ C) (r := r) (fun x hx => by simp [uncut, hx])
        (fun x hx => by simp [uncut, hx]) hr (fun w hw => ?_) k v hk
      rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl (Finset.mem_of_mem_erase hw)
      · exact Or.inr hw

omit [Fintype V] in
lemma children_uncut {A S C : Finset V} {r : V} (hr : r ∈ S) (hCA : C ⊆ A \ S) {g : V → V}
    (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : children A S r (uncut C r g) = C := by
  ext v
  simp [children, uncut]
  constructor
  · intro ⟨hvAS, hv⟩
    by_cases hvC : v ∈ C
    · exact hvC
    · simp [hvC] at hv
      -- v ∈ (A.erase r) \ (S.erase r ∪ C) so g v ∈ A.erase r, but g v = r
      have hvr : v ≠ r := fun h => hvAS.2 (h ▸ hr)
      have hv_in : v ∈ (A.erase r) \ (S.erase r ∪ C) := by
        simp [hvAS, hvC, hvr]
      have := hg.maps v hv_in
      simp [hv] at this
  · intro hvC
    have hvAS : v ∈ A ∧ v ∉ S := Finset.mem_sdiff.mp (hCA hvC)
    refine ⟨hvAS, ?_⟩
    simp [hvC]

omit [Fintype V] in
lemma cut_uncut {A S C : Finset V} {r : V} {g : V → V}
    (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : cut C (uncut C r g) = g := by
  ext v
  simp only [cut, uncut]
  split_ifs with hv
  · have hv_root : v ∈ S.erase r ∪ C := Finset.mem_union.mpr (Or.inr hv)
    have : v ∉ (A.erase r) \ (S.erase r ∪ C) := by simp [hv_root]
    exact (hg.fixed v this).symm
  · rfl

omit [Fintype V] in
lemma uncut_cut (A S : Finset V) (r : V) (f : V → V) :
    uncut (children A S r f) r (cut (children A S r f) f) = f := by
  funext v
  simp only [cut, uncut]
  by_cases hv : v ∈ children A S r f <;> simp [hv]
  · exact Eq.symm (Finset.mem_filter.mp hv |>.2)

/-- For a fixed set `C` of children of `r`, cutting is a bijection between the forests on `A`
with roots `S` whose set of children of `r` is `C`, and the forests on `A.erase r` with
roots `S.erase r ∪ C`. -/
lemma card_fiber_eq {A S C : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) (hCA : C ⊆ A \ S) :
    ((forestFinset A S).filter (fun f => children A S r f = C)).card
      = (forestFinset (A.erase r) (S.erase r ∪ C)).card := by
  refine Finset.card_nbij' (cut C) (uncut C r) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset] at hf
    have h := isForest_cut hr hf.1
    rw [hf.2] at h
    simpa using h
  · intro g hg
    simp only [Finset.mem_coe, mem_forestFinset] at hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset]
    exact ⟨isForest_uncut hr hSA hCA hg, children_uncut hr hCA hg⟩
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset] at hf
    have h := uncut_cut A S r f
    rw [hf.2] at h
    exact h
  · intro g hg
    simp only [Finset.mem_coe, mem_forestFinset] at hg
    exact cut_uncut hg

/-- Deleting a root `r` splits the forests on `A` with roots `S` according to the set `C` of
children of `r`. -/
lemma card_forestFinset_split {A S : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) :
    (forestFinset A S).card
      = ∑ C ∈ (A \ S).powerset, (forestFinset (A.erase r) (S.erase r ∪ C)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun f => children A S r f) (t := (A \ S).powerset)
    (fun f _ => Finset.mem_coe.2 (Finset.mem_powerset.mpr children_subset))]
  exact Finset.sum_congr rfl fun C hC => card_fiber_eq hr hSA (Finset.mem_powerset.mp hC)

/-! #### The binomial identity -/

lemma sum_choose_pow (m q : ℕ) :
    ∑ i ∈ Finset.range (m + 1), m.choose i * q ^ (m - i) = (q + 1) ^ m := by
  rw [add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have h1 : m + 1 - 1 - i = m - i := by omega
  have h2 : m - (m - i) = i := by omega
  rw [h1, h2, Nat.choose_symm (by omega)]
  simp [mul_comm]

lemma sum_choose_mul_pow (m q : ℕ) :
    ∑ i ∈ Finset.range (m + 1), m.choose i * (i * q ^ (m - i)) = m * (q + 1) ^ (m - 1) := by
  cases m with
  | zero => simp
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [zero_mul, mul_zero, add_zero, Nat.add_sub_cancel, ← sum_choose_pow k q,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have h1 : k + 1 - (t + 1) = k - t := by omega
    rw [h1]
    calc (k + 1).choose (t + 1) * ((t + 1) * q ^ (k - t))
        = ((k + 1).choose (t + 1) * (t + 1)) * q ^ (k - t) := by ring
      _ = ((k + 1) * k.choose t) * q ^ (k - t) := by rw [← Nat.add_one_mul_choose_eq]
      _ = (k + 1) * (k.choose t * q ^ (k - t)) := by ring

lemma sum_aux (j m q : ℕ) :
    ∑ i ∈ Finset.range (m + 1), m.choose i * ((j + i) * q ^ (m - i))
      = j * (q + 1) ^ m + m * (q + 1) ^ (m - 1) := by
  have h : ∀ i, m.choose i * ((j + i) * q ^ (m - i))
      = j * (m.choose i * q ^ (m - i)) + m.choose i * (i * q ^ (m - i)) := by
    intro i; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_choose_pow, sum_choose_mul_pow]

lemma sum_binom_aux (j m : ℕ) :
    (j + 1 + m) * ∑ i ∈ Finset.range (m + 1), m.choose i * ((j + i) * (j + m) ^ (m - i))
      = (j + 1) * ((j + m) * (j + 1 + m) ^ m) := by
  rw [sum_aux, show j + m + 1 = j + 1 + m from by ring]
  cases m with
  | zero => simp
  | succ k =>
    rw [show k + 1 - 1 = k from rfl, pow_succ]
    ring

lemma card_forestFinset_aux : ∀ (n : ℕ) (A S : Finset V), A.card = n → S ⊆ A →
    A.card * (forestFinset A S).card = S.card * A.card ^ (A.card - S.card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A S hA hSA
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rcases A.eq_empty_or_nonempty with rfl | hA'
    · simp
    · rw [forestFinset_empty_roots hA']
      simp
  · by_cases hAS : S = A
    · subst hAS
      rw [forestFinset_self]
      simp
    · obtain ⟨r, hr⟩ := hS
      have hrA : r ∈ A := hSA hr
      have hlt : S.card < A.card := Finset.card_lt_card (lt_of_le_of_ne hSA hAS)
      obtain ⟨j, hj⟩ : ∃ j, S.card = j + 1 :=
        ⟨S.card - 1, by have := Finset.card_pos.mpr ⟨r, hr⟩; omega⟩
      set m := (A \ S).card with hm
      have hmA : A.card = j + 1 + m := by
        have := Finset.card_sdiff_add_card_eq_card hSA
        omega
      have hm1 : 1 ≤ m := by omega
      have hAe : (A.erase r).card = j + m := by
        rw [Finset.card_erase_of_mem hrA, hmA]; omega
      have key : (j + m) * (forestFinset A S).card
          = ∑ C ∈ (A \ S).powerset, ((j + C.card) * (j + m) ^ (m - C.card)) := by
        rw [card_forestFinset_split hr hSA, Finset.mul_sum]
        refine Finset.sum_congr rfl fun C hC => ?_
        have hCA : C ⊆ A \ S := Finset.mem_powerset.mp hC
        have hCcard : C.card ≤ m := hm ▸ Finset.card_le_card hCA
        have hdisj : Disjoint (S.erase r) C := by
          refine Finset.disjoint_left.2 fun a ha haC => ?_
          exact (Finset.mem_sdiff.mp (hCA haC)).2 (Finset.mem_of_mem_erase ha)
        have hsub : S.erase r ∪ C ⊆ A.erase r := by
          refine Finset.union_subset (Finset.erase_subset_erase _ hSA) fun a ha => ?_
          have ha' := Finset.mem_sdiff.mp (hCA ha)
          exact Finset.mem_erase.2 ⟨fun h => ha'.2 (h ▸ hr), ha'.1⟩
        have hcards : (S.erase r ∪ C).card = j + C.card := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hr, hj]
          omega
        have h := ih (A.erase r).card (by omega) (A.erase r) (S.erase r ∪ C) rfl hsub
        rw [hAe, hcards] at h
        rw [h]
        congr 2
        omega
      rw [Finset.sum_powerset_apply_card (fun i => (j + i) * (j + m) ^ (m - i))] at key
      simp only [smul_eq_mul, ← hm] at key
      have main := sum_binom_aux j m
      rw [← key] at main
      have h2 : (j + m) * ((j + 1 + m) * (forestFinset A S).card)
          = (j + m) * ((j + 1) * (j + 1 + m) ^ m) := by
        calc (j + m) * ((j + 1 + m) * (forestFinset A S).card)
            = (j + 1 + m) * ((j + m) * (forestFinset A S).card) := by ring
          _ = (j + 1) * ((j + m) * (j + 1 + m) ^ m) := main
          _ = (j + m) * ((j + 1) * (j + 1 + m) ^ m) := by ring
      have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < j + m) h2
      rw [hmA, hj, show j + 1 + m - (j + 1) = m by omega]
      exact h3

/-- **The number of rooted forests.** -/
theorem card_forestFinset (A S : Finset V) (hSA : S ⊆ A) :
    A.card * (forestFinset A S).card = S.card * A.card ^ (A.card - S.card) :=
  card_forestFinset_aux A.card A S rfl hSA

end Forest

/-! ### From trees to rooted forests -/

section Graph

variable {N : ℕ} {G : SimpleGraph (Fin (N + 1))}

/-- The unique path from `v` to `0` in a tree. -/
noncomputable def treePath (hG : G.IsTree) (v : Fin (N + 1)) : G.Walk v 0 :=
  (hG.existsUnique_path v 0).choose

lemma treePath_isPath (hG : G.IsTree) (v : Fin (N + 1)) : (treePath hG v).IsPath :=
  (hG.existsUnique_path v 0).choose_spec.1

lemma treePath_unique (hG : G.IsTree) {v : Fin (N + 1)} (q : G.Walk v 0) (hq : q.IsPath) :
    q = treePath hG v :=
  (hG.existsUnique_path v 0).choose_spec.2 q hq

/-- The parent of `v` in a tree rooted at `0`: the second vertex of the unique path to `0`. -/
noncomputable def parent (hG : G.IsTree) (v : Fin (N + 1)) : Fin (N + 1) := (treePath hG v).snd

lemma parent_adj (hG : G.IsTree) {v : Fin (N + 1)} (hv : v ≠ 0) : G.Adj v (parent hG v) :=
  SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne hv)

lemma parent_zero (hG : G.IsTree) : parent hG 0 = 0 := by
  unfold parent treePath
  have h := (hG.existsUnique_path 0 0).choose_spec
  have padj : (default : G.Walk 0 0).IsPath := by simp
  have e := (h.2 default padj).symm
  simp only [e]
  rfl

lemma length_treePath_parent (hG : G.IsTree) {v : Fin (N + 1)} (hv : v ≠ 0) :
    (treePath hG (parent hG v)).length < (treePath hG v).length := by
  have hnil : ¬ (treePath hG v).Nil := SimpleGraph.Walk.not_nil_of_ne hv
  have h : (treePath hG v).tail = treePath hG (parent hG v) :=
    treePath_unique hG _ (treePath_isPath hG v).tail
  have hl := SimpleGraph.Walk.length_tail_add_one hnil
  rw [h] at hl
  -- `omega` is not used here: the two occurrences of the walk length differ in an
  -- implicit vertex argument (`parent hG v` vs `(treePath hG v).snd`), which is
  -- definitionally but not syntactically equal.
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hl.le

lemma treePath_length_pos (hG : G.IsTree) {v : Fin (N + 1)} (hv : v ≠ 0) :
    0 < (treePath hG v).length :=
  SimpleGraph.Walk.not_nil_iff_lt_length.mp (SimpleGraph.Walk.not_nil_of_ne hv)

lemma parent_reaches_aux (hG : G.IsTree) : ∀ (k : ℕ) (v : Fin (N + 1)),
    (treePath hG v).length ≤ k → ∃ m, (parent hG)^[m] v = 0 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    by_cases h0 : v = 0
    · exact ⟨0, by simp [h0]⟩
    · exact absurd (treePath_length_pos hG h0) (by omega)
  | succ k ih =>
    intro v hv
    by_cases h0 : v = 0
    · exact ⟨0, by simp [h0]⟩
    · have hlt := length_treePath_parent hG h0
      obtain ⟨m, hm⟩ := ih (parent hG v) (by omega)
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

lemma parent_reaches (hG : G.IsTree) (v : Fin (N + 1)) : ∃ m, (parent hG)^[m] v = 0 :=
  parent_reaches_aux hG _ v le_rfl

lemma isForest_parent (hG : G.IsTree) :
    IsForest (Finset.univ : Finset (Fin (N + 1))) {0} (parent hG) := by
  refine ⟨fun v hv => ?_, fun v _ => Finset.mem_univ _, fun v _ => ?_⟩
  · simp only [Finset.sdiff_singleton_eq_erase, Finset.mem_erase, Finset.mem_univ, and_true,
      not_not] at hv
    subst hv
    exact parent_zero hG
  · obtain ⟨m, hm⟩ := parent_reaches hG v
    exact ⟨m, by simp [hm]⟩

/-- If `p (p v) = v` then the orbit of `v` under `p` is `{v, p v}`. -/
lemma iterate_eq_of_two_cycle {V : Type*} {p : V → V} {v : V} (h : p (p v) = v) (m : ℕ) :
    p^[m] v = v ∨ p^[m] v = p v := by
  have heven : ∀ k, p^[k + k] v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc p^[k + 1 + (k + 1)] v
          = p^[k + k + 2] v := by ring_nf
        _ = p^[k + k + 1 + 1] v := by ring_nf
        _ = p (p^[k + k + 1] v) := by rw [Function.iterate_succ']; rfl
        _ = p (p (p^[k + k] v)) := by rw [Function.iterate_succ']; rfl
        _ = p (p v) := by rw [ih]
        _ = v := h
  have hodd : ∀ k, p^[2 * k + 1] v = p v := by
    intro k
    rw [Function.iterate_succ']
    show p (p^[2 * k] v) = p v
    have : 2 * k = k + k := by ring
    rw [this, heven k]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; rw [hk]; exact heven k
  · right; rw [hk]; exact hodd k

/-- In a rooted forest with a single root `0`, the parent function has no `2`-cycle. -/
lemma not_two_cycle {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) {v : Fin (N + 1)} (hv : v ≠ 0)
    (h : p (p v) = v) : False := by
  obtain ⟨m, hm⟩ := hp.reaches v (Finset.mem_univ v)
  rw [Finset.mem_singleton] at hm
  have hp0 : p 0 = 0 := hp.fixed 0 (by simp)
  rcases iterate_eq_of_two_cycle h m with h' | h'
  · exact hv (h' ▸ hm)
  · have : p v = 0 := h' ▸ hm
    rw [this, hp0] at h
    exact hv h.symm

lemma parent_ne_self {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) {v : Fin (N + 1)} (hv : v ≠ 0) :
    p v ≠ v := fun hc => not_two_cycle hp hv (by rw [hc, hc])

/-- The map `v ↦ s(v, p v)` is injective away from the root, for a rooted forest `p`. -/
lemma injOn_edge_of_isForest {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    Set.InjOn (fun v => s(v, p v)) {v : Fin (N + 1) | v ≠ 0} := by
  intro v hv w hw h
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exact absurd (by rw [h2, h1] : p (p v) = v) (fun hc => (not_two_cycle hp hv hc).elim)

lemma ncard_edges_image {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    ((fun v => s(v, p v)) '' {v : Fin (N + 1) | v ≠ 0}).ncard = N := by
  rw [Set.InjOn.ncard_image (injOn_edge_of_isForest hp)]
  have h : {v : Fin (N + 1) | v ≠ 0} = ↑((Finset.univ : Finset (Fin (N + 1))).erase 0) := by
    ext v; simp
  rw [h, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- The edges of a tree are exactly the edges from a vertex to its parent. -/
lemma edgeSet_eq_of_isTree (hG : G.IsTree) :
    G.edgeSet = (fun v => s(v, parent hG v)) '' {v : Fin (N + 1) | v ≠ 0} := by
  have hsub : (fun v => s(v, parent hG v)) '' {v : Fin (N + 1) | v ≠ 0} ⊆ G.edgeSet := by
    rintro e ⟨v, hv, rfl⟩
    exact parent_adj hG hv
  have hcard : G.edgeSet.ncard = N := by
    have h := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
    rw [Nat.card_coe_set_eq] at h
    simpa using h
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [hcard, ncard_edges_image (isForest_parent hG)]

lemma tree_parent_injective :
    Function.Injective (fun T : {G : SimpleGraph (Fin (N + 1)) // G.IsTree} => parent T.2) := by
  rintro ⟨G₁, h₁⟩ ⟨G₂, h₂⟩ h
  simp only at h
  refine Subtype.ext ?_
  rw [← SimpleGraph.edgeSet_inj, edgeSet_eq_of_isTree h₁, edgeSet_eq_of_isTree h₂, h]

/-! ### From rooted forests to trees -/

/-- The graph associated with a parent function. -/
def graphOf (p : Fin (N + 1) → Fin (N + 1)) : SimpleGraph (Fin (N + 1)) :=
  SimpleGraph.fromRel (fun v w => v ≠ 0 ∧ p v = w)

lemma graphOf_adj {p : Fin (N + 1) → Fin (N + 1)} {v w : Fin (N + 1)} :
    (graphOf p).Adj v w ↔ v ≠ w ∧ ((v ≠ 0 ∧ p v = w) ∨ (w ≠ 0 ∧ p w = v)) := by
  simp [graphOf, SimpleGraph.fromRel]

lemma graphOf_adj_parent {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) {v : Fin (N + 1)} (hv : v ≠ 0) :
    (graphOf p).Adj v (p v) :=
  graphOf_adj.mpr ⟨fun hc => parent_ne_self hp hv hc.symm, Or.inl ⟨hv, rfl⟩⟩

lemma graphOf_reachable_zero {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    ∀ (m : ℕ) (v : Fin (N + 1)), p^[m] v = 0 → (graphOf p).Reachable v 0 := by
  intro m
  induction m with
  | zero =>
    intro v hv
    simp only [Function.iterate_zero, id_eq] at hv
    subst hv
    rfl
  | succ m ih =>
    intro v hv
    by_cases h0 : v = 0
    · subst h0; rfl
    · have hpv : p^[m] (p v) = 0 := by rw [← Function.iterate_succ_apply]; exact hv
      exact ((graphOf_adj_parent hp h0).reachable).trans (ih (p v) hpv)

lemma graphOf_reachable_zero' {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) (v : Fin (N + 1)) :
    (graphOf p).Reachable v 0 := by
  obtain ⟨m, hm⟩ := hp.reaches v (Finset.mem_univ v)
  exact graphOf_reachable_zero hp m v (by simpa using hm)

lemma graphOf_connected {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) : (graphOf p).Connected := by
  haveI : Nonempty (Fin (N + 1)) := ⟨0⟩
  exact SimpleGraph.Connected.mk fun u v =>
    (graphOf_reachable_zero' hp u).trans (graphOf_reachable_zero' hp v).symm

lemma edgeSet_graphOf {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    (graphOf p).edgeSet = (fun v => s(v, p v)) '' {v : Fin (N + 1) | v ≠ 0} := by
  ext e
  induction e using Sym2.ind with
  | _ v w =>
  simp only [SimpleGraph.mem_edgeSet, graphOf_adj, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hne, ⟨hv0, rfl⟩ | ⟨hw0, rfl⟩⟩
    · exact ⟨v, hv0, rfl⟩
    · exact ⟨w, hw0, Sym2.eq_swap⟩
  · rintro ⟨u, hu, he⟩
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun hc => parent_ne_self hp hu hc.symm, Or.inl ⟨hu, rfl⟩⟩
    · exact ⟨fun hc => parent_ne_self hp hu hc, Or.inr ⟨hu, rfl⟩⟩

lemma graphOf_isTree {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) : (graphOf p).IsTree := by
  refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨graphOf_connected hp, ?_⟩
  rw [Nat.card_coe_set_eq, edgeSet_graphOf hp, ncard_edges_image hp]
  simp

lemma graphOf_injOn_aux {p q : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p)
    (hq : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} q)
    (h : graphOf p = graphOf q) :
    ∀ (m : ℕ) (v : Fin (N + 1)), p^[m] v = 0 → p v = q v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hv
  by_cases h0 : v = 0
  · subst h0
    rw [hp.fixed 0 (by simp), hq.fixed 0 (by simp)]
  · have hadj : (graphOf q).Adj v (p v) := h ▸ graphOf_adj_parent hp h0
    obtain ⟨hne, hcase⟩ := graphOf_adj.mp hadj
    rcases hcase with ⟨-, h1⟩ | ⟨hpv0, h2⟩
    · exact h1.symm
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := by
        cases m with
        | zero => exact absurd hv h0
        | succ j => exact ⟨j, rfl⟩
      have hj : p^[j] (p v) = 0 := by rw [← Function.iterate_succ_apply]; exact hv
      have hpp : p (p v) = v := by rw [ih j (by omega) (p v) hj, h2]
      exact absurd hpp (fun hc => (not_two_cycle hp h0 hc).elim)

lemma graphOf_injOn {p q : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p)
    (hq : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} q)
    (h : graphOf p = graphOf q) : p = q := by
  funext v
  obtain ⟨m, hm⟩ := hp.reaches v (Finset.mem_univ v)
  exact graphOf_injOn_aux hp hq h m v (by simpa using hm)

/-! ### The bijection -/

lemma card_tree_eq_card_forest :
    Nat.card {G : SimpleGraph (Fin (N + 1)) // G.IsTree}
      = Nat.card {p : Fin (N + 1) → Fin (N + 1) //
          IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p} := by
  refine le_antisymm (Nat.card_le_card_of_injective
      (fun T => ⟨parent T.2, isForest_parent T.2⟩) ?_)
    (Nat.card_le_card_of_injective (fun P => ⟨graphOf P.1, graphOf_isTree P.2⟩) ?_)
  · intro T₁ T₂ h
    exact tree_parent_injective (congrArg Subtype.val h)
  · intro P₁ P₂ h
    exact Subtype.ext (graphOf_injOn P₁.2 P₂.2 (congrArg Subtype.val h))

lemma card_forest_subtype :
    Nat.card {p : Fin (N + 1) → Fin (N + 1) //
        IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p}
      = (forestFinset (Finset.univ : Finset (Fin (N + 1))) {0}).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => mem_forestFinset.symm)

end Graph

/-- The trees on `Fin n` form a finite type: there are only finitely many simple graphs
on a finite vertex type. -/
noncomputable instance instFintypeTreeSubtype (n : ℕ) :
    Fintype {G : SimpleGraph (Fin n) // G.IsTree} := Fintype.ofFinite _

/-- Cayley's formula: the number of labeled trees on n ≥ 1 vertices is n^(n−2)
    (counted as spanning trees of the complete graph, i.e. connected acyclic simple graphs). -/
theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hcard : Fintype.card {G : SimpleGraph (Fin (N + 1)) // G.IsTree}
      = (forestFinset (Finset.univ : Finset (Fin (N + 1))) {0}).card := by
    rw [← Nat.card_eq_fintype_card, card_tree_eq_card_forest, card_forest_subtype]
  have h := card_forestFinset (Finset.univ : Finset (Fin (N + 1))) {0} (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton, one_mul,
    Nat.add_sub_cancel] at h
  rw [hcard]
  refine Nat.eq_of_mul_eq_mul_left (show 0 < N + 1 by omega) ?_
  rw [h]
  rcases N with _ | N
  · simp
  · rw [show N + 1 + 1 - 2 = N by omega]
    ring

end Brockian.Cayley

