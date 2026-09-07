/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- A finite set `H` of natural numbers is *relatively large* when it has a least element `a`
and its cardinality is at least `a`. -/
def IsRelativelyLarge (H : Finset ℕ) : Prop :=
  ∃ a ∈ H, (∀ b ∈ H, a ≤ b) ∧ a ≤ H.card

/-- `H` is homogeneous of colour `i` for the colouring `c`, at "dimension" `n`: every
`n`-element subset of `H` gets colour `i`. -/
def IsHomogeneous (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (H : Finset ℕ) (i : Fin k) : Prop :=
  ∀ s ⊆ H, s.card = n → c s = i

/-- **Infinite Ramsey theorem** for `n`-element subsets of `ℕ` and `k` colours: every infinite
set of naturals has an infinite subset all of whose `n`-element subsets get the same colour. -/
theorem infinite_ramsey (n k : ℕ) (c : Finset ℕ → Fin k) (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ i : Fin k, ∀ s : Finset ℕ, ↑s ⊆ T → s.card = n → c s = i := by
  induction n generalizing c S with
  | zero =>
    refine ⟨S, subset_rfl, hS, c ∅, ?_⟩
    intro s _ hcard
    rw [Finset.card_eq_zero.1 hcard]
  | succ n ih =>
    -- For every infinite set `P` we choose an infinite subset `nxt P` of `P`, lying strictly
    -- above `sInf P`, which is homogeneous for the colouring `s ↦ c (insert (sInf P) s)`.
    have key : ∀ P : {X : Set ℕ // X.Infinite}, ∃ (Q : {X : Set ℕ // X.Infinite}) (i : Fin k),
        Q.1 ⊆ P.1 \ Set.Iic (sInf P.1) ∧
          ∀ s : Finset ℕ, ↑s ⊆ Q.1 → s.card = n → c (insert (sInf P.1) s) = i := by
      rintro ⟨X, hX⟩
      have hX' : (X \ Set.Iic (sInf X)).Infinite := hX.diff (Set.finite_Iic _)
      obtain ⟨T, hTsub, hTinf, i, hi⟩ := ih (fun s => c (insert (sInf X) s)) _ hX'
      exact ⟨⟨T, hTinf⟩, i, hTsub, hi⟩
    choose nxt col hsub hcol using key
    -- Iterating this choice yields a decreasing sequence of infinite sets `g j` with least
    -- elements `a 0 < a 1 < ⋯`.
    set g : ℕ → {X : Set ℕ // X.Infinite} := fun j => nxt^[j] ⟨S, hS⟩ with hgdef
    set a : ℕ → ℕ := fun j => sInf (g j).1 with hadef
    have hgsucc : ∀ j, g (j + 1) = nxt (g j) := by
      intro j; simp [hgdef, Function.iterate_succ_apply']
    have hmemg : ∀ j, a j ∈ (g j).1 := fun j => Nat.sInf_mem (g j).2.nonempty
    have hstep : ∀ j, (g (j + 1)).1 ⊆ (g j).1 \ Set.Iic (a j) := by
      intro j; rw [hgsucc j]; exact hsub (g j)
    have hmono : ∀ j l, j ≤ l → (g l).1 ⊆ (g j).1 := by
      intro j l hjl
      induction l with
      | zero => simp_all
      | succ l ihl =>
        rcases Nat.lt_or_ge j (l + 1) with h | h
        · exact fun x hx => ihl (Nat.lt_succ_iff.1 h) ((hstep l hx).1)
        · have : j = l + 1 := le_antisymm hjl h
          subst this; exact fun x hx => hx
    have hstrict : StrictMono a := by
      refine strictMono_nat_of_lt_succ (fun j => ?_)
      have := (hstep j (hmemg (j + 1))).2
      simpa [Set.mem_Iic, not_le] using this
    have hsubS : ∀ j, (g j).1 ⊆ S := by
      intro j
      have := hmono 0 j (Nat.zero_le j)
      simpa [hgdef] using this
    set d : ℕ → Fin k := fun j => col (g j) with hddef
    have hd : ∀ j, ∀ s : Finset ℕ, ↑s ⊆ (g (j + 1)).1 → s.card = n →
        c (insert (a j) s) = d j := by
      intro j s hs hcard
      rw [hgsucc j] at hs
      exact hcol (g j) s hs hcard
    -- Some colour `i` occurs infinitely often among the `d j`.
    obtain ⟨i, hinf⟩ := Finite.exists_infinite_fiber d
    have hJ : (d ⁻¹' {i}).Infinite := Set.infinite_coe_iff.1 hinf
    refine ⟨a '' (d ⁻¹' {i}), ?_, ?_, i, ?_⟩
    · rintro x ⟨j, -, rfl⟩
      exact hsubS j (hmemg j)
    · exact hJ.image hstrict.injective.injOn
    · intro s hs hcard
      have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
      set x := s.min' hsne with hx
      have hxs : x ∈ s := s.min'_mem hsne
      obtain ⟨j, hjJ, hjx⟩ : ∃ j, j ∈ d ⁻¹' {i} ∧ a j = x := by
        have := hs hxs
        simpa [Set.mem_image, eq_comm] using this
      have hers : ↑(s.erase x) ⊆ (g (j + 1)).1 := by
        intro y hy
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hy
        obtain ⟨hys, hyx⟩ := hy
        obtain ⟨l, -, rfl⟩ := hs hys
        have hlt : a j < a l :=
          lt_of_le_of_ne (hjx ▸ s.min'_le _ hys) (by simpa [hjx, eq_comm] using hyx)
        exact hmono (j + 1) l (hstrict.lt_iff_lt.1 hlt) (hmemg l)
      have hcarderase : (s.erase x).card = n := by
        rw [Finset.card_erase_of_mem hxs, hcard]; rfl
      have hcs := hd j (s.erase x) hers hcarderase
      rw [hjx, Finset.insert_erase hxs] at hcs
      rw [hcs]
      exact hjJ

/-- **Paris–Harrington theorem** (the strengthened finite Ramsey theorem).

For all `n, k, m` there is an `N` such that for every colouring `c` of the `n`-element subsets
of `{1, …, N}` with `k` colours there is a homogeneous set `H ⊆ {1, …, N}` with at least `m`
elements which is moreover *relatively large*: its cardinality is at least its least element.

The proof is by compactness: a counterexample for every `N` would, along a nonprincipal
ultrafilter on `ℕ`, produce a single colouring of the `n`-element subsets of `ℕ` with no
relatively large finite homogeneous set of size `≥ m`, contradicting the infinite Ramsey
theorem.

(The other half of the Paris–Harrington result — that this statement is unprovable in
first-order Peano arithmetic — is a metamathematical statement about a formal system, and is
not formalized here.) -/
theorem Paris_Harrington (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H ⊆ Finset.Icc 1 N,
      m ≤ H.card ∧ IsRelativelyLarge H ∧ ∃ i : Fin k, IsHomogeneous n c H i := by
  by_contra hcon
  push_neg at hcon
  -- `C N` is a bad colouring for the bound `N`.
  choose C hC using hcon
  set U := Filter.hyperfilter ℕ with hU
  -- Take the `U`-limit of the bad colourings.
  have key : ∀ s : Finset ℕ, ∃ i : Fin k, {N : ℕ | C N s = i} ∈ U := by
    intro s
    have huniv : (Set.univ : Set ℕ) = ⋃ i ∈ (Set.univ : Set (Fin k)), {N : ℕ | C N s = i} := by
      ext N; simp
    have hmem : (⋃ i ∈ (Set.univ : Set (Fin k)), {N : ℕ | C N s = i}) ∈ U := by
      rw [← huniv]; exact Filter.univ_mem
    obtain ⟨i, -, hi⟩ := (Ultrafilter.finite_biUnion_mem_iff Set.finite_univ).1 hmem
    exact ⟨i, hi⟩
  choose c hc using key
  obtain ⟨T, hTsub, hTinf, i, hi⟩ := infinite_ramsey n k c (Set.Ici 1) (Set.Ici_infinite 1)
  set a := sInf T with hadef
  have haT : a ∈ T := Nat.sInf_mem hTinf.nonempty
  obtain ⟨H₀, hH₀sub, hH₀card⟩ := hTinf.exists_subset_card_eq (max m a)
  set H := insert a H₀ with hHdef
  have hHT : ↑H ⊆ T := by
    intro x hx
    simp only [hHdef, Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact haT
    · exact hH₀sub hx
  have hcard : max m a ≤ H.card := by
    rw [← hH₀card]
    exact Finset.card_le_card (Finset.subset_insert _ _)
  have haH : a ∈ H := Finset.mem_insert_self _ _
  have hHne : H.Nonempty := ⟨a, haH⟩
  set N₀ := H.max' hHne with hN₀
  have hAmem : {N : ℕ | N₀ ≤ N} ∩ (⋂ s ∈ H.powerset, {N : ℕ | C N s = c s}) ∈ U := by
    refine Filter.inter_mem ?_ ?_
    · have hIci : Set.Ici N₀ ∈ (Filter.atTop : Filter ℕ) := Filter.Ici_mem_atTop N₀
      rw [← Nat.cofinite_eq_atTop] at hIci
      exact Filter.hyperfilter_le_cofinite hIci
    · exact (Filter.biInter_finset_mem _).2 fun s _ => hc s
  obtain ⟨N, hN1, hN2⟩ := Filter.nonempty_of_mem hAmem
  refine hC N H ?_ ?_ ?_ i ?_
  · intro x hx
    exact Finset.mem_Icc.2 ⟨hTsub (hHT hx), le_trans (Finset.le_max' H x hx) hN1⟩
  · exact le_trans (le_max_left _ _) hcard
  · exact ⟨a, haH, fun b hb => Nat.sInf_le (hHT hb), le_trans (le_max_right _ _) hcard⟩
  · intro s hs hcs
    have h1 : C N s = c s := Set.mem_iInter₂.1 hN2 s (Finset.mem_powerset.2 hs)
    rw [h1]
    exact hi s (fun x hx => hHT (hs hx)) hcs

end Frontier

