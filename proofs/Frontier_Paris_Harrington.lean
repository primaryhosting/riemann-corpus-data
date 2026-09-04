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
Infinite Ramsey theorem for `n`-element subsets of `ℕ`, proved via ultrafilters.
This is the infinitary input to the Paris–Harrington theorem.
-/
import Mathlib

namespace Frontier

open Filter

/-- `T` is homogeneous of colour `j` and dimension `n` for the colouring `c`:
every `n`-element subset of `T` gets colour `j`. -/
def HomogOn (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (T : Set ℕ) (j : Fin k) : Prop :=
  ∀ s : Finset ℕ, ↑s ⊆ T → s.card = n → c s = j

variable {k : ℕ}

/-- For an ultrafilter `U` and a finite set `s`, the colour of `insert b s` is
`U`-almost everywhere constant. -/
lemma exists_ufilter_color (c : Finset ℕ → Fin k) (U : Ultrafilter ℕ) (s : Finset ℕ) :
    ∃ j : Fin k, {b : ℕ | c (insert b s) = j} ∈ U := by
  by_contra h
  push_neg at h
  have hcompl : ∀ j : Fin k, {b : ℕ | c (insert b s) = j}ᶜ ∈ U := fun j =>
    (Ultrafilter.compl_mem_iff_not_mem U).2 (h j)
  have hfin : (⋂ j ∈ (Finset.univ : Finset (Fin k)), {b : ℕ | c (insert b s) = j}ᶜ) ∈ U :=
    (Filter.biInter_finset_mem _).2 fun j _ => hcompl j
  obtain ⟨b, hb⟩ := Filter.nonempty_of_mem hfin
  simp only [Set.mem_iInter, Finset.mem_univ, Set.mem_compl_iff, Set.mem_setOf_eq,
    forall_true_left] at hb
  exact hb (c (insert b s)) rfl

/-- The `U`-limit colour of the colouring `b ↦ c (insert b s)`. -/
noncomputable def ufColor (c : Finset ℕ → Fin k) (U : Ultrafilter ℕ) (s : Finset ℕ) : Fin k :=
  (exists_ufilter_color c U s).choose

lemma ufColor_mem (c : Finset ℕ → Fin k) (U : Ultrafilter ℕ) (s : Finset ℕ) :
    {b : ℕ | c (insert b s) = ufColor c U s} ∈ U :=
  (exists_ufilter_color c U s).choose_spec

section Construction

variable (c : Finset ℕ → Fin k) (U : Ultrafilter ℕ) (S : Set ℕ)

/-- Given a finite set `F`, one can find a point of `S` above `F` whose colour behaviour over
all subsets of `F` is the `U`-limit behaviour. -/
lemma exists_next (hS : S ∈ U) (htop : ∀ N : ℕ, {b : ℕ | N < b} ∈ U) (F : Finset ℕ) :
    ∃ b : ℕ, b ∈ S ∧ (∀ x ∈ F, x < b) ∧ ∀ s ⊆ F, c (insert b s) = ufColor c U s := by
  have h1 : {b : ℕ | ∀ x ∈ F, x < b} ∈ U := by
    refine Filter.mem_of_superset (htop (F.sup id)) ?_
    intro b hb x hx
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hx) hb
  have h2 : (⋂ s ∈ F.powerset, {b : ℕ | c (insert b s) = ufColor c U s}) ∈ U :=
    (Filter.biInter_finset_mem _).2 fun s _ => ufColor_mem c U s
  have h3 : S ∩ ({b : ℕ | ∀ x ∈ F, x < b} ∩
      (⋂ s ∈ F.powerset, {b : ℕ | c (insert b s) = ufColor c U s})) ∈ U :=
    Filter.inter_mem hS (Filter.inter_mem h1 h2)
  obtain ⟨b, hb1, hb2, hb3⟩ := Filter.nonempty_of_mem h3
  refine ⟨b, hb1, hb2, ?_⟩
  intro s hs
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hb3
  exact hb3 s (Finset.mem_powerset.2 hs)

/-- The key construction: a strictly increasing sequence inside `S` along which the colouring
`c` of `(n+1)`-sets is computed by the `U`-limit colouring of `n`-sets. -/
lemma exists_seq (hS : S ∈ U) (htop : ∀ N : ℕ, {b : ℕ | N < b} ∈ U) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, a i ∈ S) ∧
      ∀ (i : ℕ) (s : Finset ℕ), (∀ x ∈ s, ∃ p < i, x = a p) →
        c (insert (a i) s) = ufColor c U s := by
  choose next hnextS hnextlt hnextcol using exists_next c U S hS htop
  set F : ℕ → Finset ℕ := fun i => Nat.rec ∅ (fun _ G => insert (next G) G) i with hF
  set a : ℕ → ℕ := fun i => next (F i) with ha
  have hFsucc : ∀ i, F (i + 1) = insert (a i) (F i) := fun _ => rfl
  have hsub : ∀ i, F i ⊆ F (i + 1) := by
    intro i
    rw [hFsucc]
    exact Finset.subset_insert _ _
  have hmem : ∀ p i, p < i → a p ∈ F i := by
    intro p i hpi
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hpi with h | h
      · exact hsub i (ih h)
      · subst h; rw [hFsucc]; exact Finset.mem_insert_self _ _
  have hstrict : StrictMono a := fun p i hpi => hnextlt (F i) (a p) (hmem p i hpi)
  refine ⟨a, hstrict, fun i => hnextS (F i), ?_⟩
  intro i s hs
  refine hnextcol (F i) s ?_
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hs x hx
  exact hmem p i hp

end Construction

/-- **Infinite Ramsey theorem**: for every `k`-colouring `c` of the `n`-element subsets of `ℕ`
and every infinite set `S`, there is an infinite subset `T ⊆ S` all of whose `n`-element subsets
receive the same colour. -/
theorem infinite_ramsey (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ j, HomogOn n c T j := by
  induction n generalizing c S with
  | zero =>
    refine ⟨S, subset_rfl, hS, c ∅, ?_⟩
    intro s _ hs
    rw [Finset.card_eq_zero.1 hs]
  | succ n ih =>
    have hne : (Filter.atTop ⊓ Filter.principal S).NeBot := by
      rw [← Nat.cofinite_eq_atTop, Filter.inf_principal_neBot_iff]
      intro u hu
      have h := (Filter.frequently_cofinite_iff_infinite (p := fun x => x ∈ S)).2 hS
      obtain ⟨x, hx1, hx2⟩ := (h.and_eventually hu).exists
      exact ⟨x, hx2, hx1⟩
    set U : Ultrafilter ℕ := Ultrafilter.of (Filter.atTop ⊓ Filter.principal S) with hU
    have hle : (U : Filter ℕ) ≤ Filter.atTop ⊓ Filter.principal S := Ultrafilter.of_le _
    have hSU : S ∈ U := hle (Filter.mem_inf_of_right (Filter.mem_principal_self S))
    have htop : ∀ N : ℕ, {b : ℕ | N < b} ∈ U := fun N =>
      hle (Filter.mem_inf_of_left (Filter.eventually_gt_atTop N))
    obtain ⟨a, hmono, haS, hacol⟩ := exists_seq c U S hSU htop
    set T₀ : Set ℕ := Set.range a with hT₀
    have hT₀S : T₀ ⊆ S := by rintro _ ⟨i, rfl⟩; exact haS i
    have hT₀inf : T₀.Infinite := Set.infinite_range_of_injective hmono.injective
    obtain ⟨T, hTsub, hTinf, j, hj⟩ := ih (ufColor c U) T₀ hT₀inf
    refine ⟨T, hTsub.trans hT₀S, hTinf, j, ?_⟩
    intro s hs hcard
    have hsne : s.Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨i, hi⟩ : ∃ i, a i = s.max' hsne := hTsub (hs (s.max'_mem hsne))
    have hins : insert (s.max' hsne) (s.erase (s.max' hsne)) = s :=
      Finset.insert_erase (s.max'_mem hsne)
    have hcard' : (s.erase (s.max' hsne)).card = n := by
      rw [Finset.card_erase_of_mem (s.max'_mem hsne), hcard]
    have hsubT : ↑(s.erase (s.max' hsne)) ⊆ T := fun x hx =>
      hs (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hx)))
    have hstep : c s = ufColor c U (s.erase (s.max' hsne)) := by
      rw [← hins, ← hi]
      refine hacol i _ ?_
      intro x hx
      obtain ⟨p, hp⟩ := hTsub (hsubT (Finset.mem_coe.2 hx))
      refine ⟨p, ?_, hp.symm⟩
      have hxlt : x < a i := by
        rw [hi]
        exact lt_of_le_of_ne (s.le_max' x (Finset.mem_of_mem_erase hx))
          (Finset.ne_of_mem_erase hx)
      exact hmono.lt_iff_lt.1 (by rwa [hp])
    rw [hstep]
    exact hj _ hsubT hcard'

end Frontier

