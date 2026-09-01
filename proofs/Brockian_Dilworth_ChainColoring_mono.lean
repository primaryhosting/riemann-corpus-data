import Mathlib

/-!
# Dilworth's theorem

In a finite partial order, the minimum number of chains needed to cover the order equals the
maximum size of an antichain.

The main work is done with the auxiliary notion of a *chain colouring*: a map `f : α → ℕ`
assigning to each element of a finite set `s` a colour `< n` such that any two elements of `s`
with the same colour are comparable (i.e. the colour classes are chains).

The main results are:

* `Brockian.Dilworth.dilworth_cover`: if every antichain has at most `n` elements, then the whole
  (finite) order can be covered by at most `n` chains;
* `Brockian.Dilworth.dilworth`: if moreover `n` is attained by some antichain, the cover can be
  taken to consist of exactly `n` chains;
* `Brockian.Dilworth.card_le_card_of_cover`: the converse inequality, i.e. any antichain is at most
  as large as any covering family of chains.

Together, `dilworth` and `card_le_card_of_cover` say that the maximum size of an antichain equals
the minimum number of chains needed to cover the order.

The statement of `dilworth` differs slightly from the one originally posed, which asked for a
cover by exactly `n` chains assuming only that `n` bounds the size of every antichain; that form
is false, and `Brockian.Dilworth.exact_cover_counterexample` gives an explicit counterexample.
-/

namespace Brockian.Dilworth

variable {α : Type*} [PartialOrder α] [DecidableEq α]

/-- `ChainColoring s n f` says that `f` assigns to each element of `s` a colour `< n`, in such a
way that any two elements of `s` with the same colour are comparable; i.e. the colour classes
are chains. -/
def ChainColoring (s : Finset α) (n : ℕ) (f : α → ℕ) : Prop :=
  (∀ a ∈ s, f a < n) ∧ ∀ a ∈ s, ∀ b ∈ s, f a = f b → a ≤ b ∨ b ≤ a

omit [DecidableEq α] in
lemma ChainColoring.mono {s : Finset α} {n m : ℕ} {f : α → ℕ} (h : ChainColoring s n f)
    (hnm : n ≤ m) : ChainColoring s m f :=
  ⟨fun a ha => lt_of_lt_of_le (h.1 a ha) hnm, h.2⟩

omit [DecidableEq α] in
lemma ChainColoring.subset {s t : Finset α} {n : ℕ} {f : α → ℕ} (h : ChainColoring s n f)
    (hts : t ⊆ s) : ChainColoring t n f :=
  ⟨fun a ha => h.1 a (hts ha), fun a ha b hb hab => h.2 a (hts ha) b (hts hb) hab⟩

/-- A chain colouring is injective on any antichain. -/
lemma ChainColoring.injOn_antichain {s A : Finset α} {n : ℕ} {f : α → ℕ}
    (h : ChainColoring s n f) (hAs : A ⊆ s) (hA : IsAntichain (· ≤ ·) (A : Set α)) :
    Set.InjOn f (A : Set α) := by
  intro a ha b hb hab
  have := h.2 a (hAs ha) b (hAs hb) hab
  rcases this with hle | hle
  · by_contra hne; exact hA ha hb hne hle
  · by_contra hne; exact hA hb ha (fun h => hne h.symm) hle

/-- On an antichain of size `n` inside an `n`-colouring, every colour `< n` is attained. -/
lemma ChainColoring.exists_of_lt {s A : Finset α} {n : ℕ} {f : α → ℕ}
    (h : ChainColoring s n f) (hAs : A ⊆ s) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = n) {c : ℕ} (hc : c < n) : ∃ y ∈ A, f y = c := by
  have hinj : Set.InjOn f (A : Set α) := by
    intro a ha b hb hab
    have hab' := h.2 a (hAs ha) b (hAs hb) hab
    cases hab' with
    | inl h => by_contra hne; exact hA ha hb hne h
    | inr h => by_contra hne; exact hA hb ha (fun hab => hne hab.symm) h
  have hsubset : ∀ a ∈ A, f a ∈ Finset.range n := by
    exact fun a ha => Finset.mem_range.mpr (h.1 a (hAs ha))
  have hcard' : (Finset.image f A).card = n := by rw [Finset.card_image_of_injOn hinj, hcard]
  have heq : Finset.image f A = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hsubset)
    rw [hcard', Finset.card_range]
  have hc' : c ∈ Finset.range n := Finset.mem_range.mpr hc
  rw [← heq] at hc'
  exact Finset.mem_image.mp hc'

omit [DecidableEq α] in
/-- A nonempty finite subset of a partial order contains a maximal element `a` together with a
minimal element `b ≤ a`. -/
lemma exists_max_min {s : Finset α} (hs : s.Nonempty) :
    ∃ a ∈ s, ∃ b ∈ s, b ≤ a ∧ (∀ x ∈ s, a ≤ x → x = a) ∧ (∀ x ∈ s, x ≤ b → x = b) := by
  classical
  obtain ⟨a, ha⟩ := hs
  obtain ⟨a', _, hmax⟩ := Finset.exists_le_maximal s ha
  set t := s.filter (fun x => x ≤ a') with ht
  have htne : t.Nonempty := ⟨a', by simp [ht, hmax.1]⟩
  obtain ⟨b, hmin⟩ := Finset.exists_minimal htne
  have hbt : b ∈ t := hmin.1
  have hbs : b ∈ s := (Finset.mem_filter.mp hbt).1
  refine ⟨a', hmax.1, b, hbs, (Finset.mem_filter.mp hbt).2, ?_, ?_⟩
  · intro x hx hx'
    exact le_antisymm (hmax.2 hx hx') hx'
  · intro x hx hxb
    exact le_antisymm hxb (hmin.2 (Finset.mem_filter.mpr
      ⟨hx, hxb.trans (Finset.mem_filter.mp hbt).2⟩) hxb)

/-- Key comparability lemma: if `x` lies below the antichain `A`, `x'` lies above `A`, and both
are comparable with the same element `y ∈ A`, then `x` and `x'` are comparable. -/
lemma cross_comparable {A : Finset α} (hA : IsAntichain (· ≤ ·) (A : Set α)) {x x' y : α}
    (hy : y ∈ A) (hxA : ∃ z ∈ A, x ≤ z) (hx'A : ∃ z ∈ A, z ≤ x')
    (hxy : x ≤ y ∨ y ≤ x) (hx'y : x' ≤ y ∨ y ≤ x') : x ≤ x' ∨ x' ≤ x := by
  obtain ⟨z, hzA, hxz⟩ := hxA
  obtain ⟨z', hz'A, hz'x'⟩ := hx'A
  have hxy_le : x ≤ y := by
    rcases hxy with hxy | hxy
    · exact hxy
    · have hlez : y ≤ z := hxy.trans hxz
      by_cases heq : y = z
      · exact heq.symm ▸ hxz
      · exact (hA hy hzA heq hlez).elim
  have hyx'_le : y ≤ x' := by
    rcases hx'y with hx'y | hx'y
    · rcases eq_or_ne y z' with rfl | hne
      · exact hz'x'
      · exact (hA hz'A hy hne.symm (hz'x'.trans hx'y)).elim
    · exact hx'y
  exact Or.inl (hxy_le.trans hyx'_le)

/-- Mixed case of the gluing step: `x` lies in the lower part `D`, `x'` lies in the upper part
`U`, and the glued colours of `x` and `x'` agree; then `x` and `x'` are comparable. -/
lemma glue_mixed {D U A : Finset α} {n : ℕ} {fD fU : α → ℕ} {g : ℕ → α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAD : A ⊆ D) (hAU : A ⊆ U)
    (hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y) (hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU)
    (hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c)
    {x x' : α} (hxD : x ∈ D) (hx'U : x' ∈ U) (heq : fD x = fD (g (fU x'))) :
    x ≤ x' ∨ x' ≤ x := by
  -- Let y = g(fU x') ∈ A
  have hc : fU x' < n := hfU.1 x' hx'U
  have hgx' : g (fU x') ∈ A := (hg _ hc).1
  -- Apply cross_comparable
  apply cross_comparable hA hgx'
  · exact hD x hxD
  · exact hU x' hx'U
  · -- Need to show x ≤ g(fU x') ∨ g(fU x') ≤ x
    exact hfD.2 x hxD (g (fU x')) (hAD hgx') heq
  · -- Need to show x' ≤ g(fU x') ∨ g(fU x') ≤ x'
    have hgcolour : fU (g (fU x')) = fU x' := (hg _ hc).2
    exact hfU.2 x' hx'U (g (fU x')) (hAU hgx') hgcolour.symm

omit [DecidableEq α] in
/-- Upper case of the gluing step: both `x` and `x'` lie in the upper part `U` and their glued
colours agree; then `x` and `x'` are comparable. -/
lemma glue_upper {D U A : Finset α} {n : ℕ} {fD fU : α → ℕ} {g : ℕ → α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAD : A ⊆ D)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU)
    (hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c)
    {x x' : α} (hxU : x ∈ U) (hx'U : x' ∈ U) (heq : fD (g (fU x)) = fD (g (fU x'))) :
    x ≤ x' ∨ x' ≤ x := by
  -- Let c = fU x and c' = fU x'
  have hc : fU x < n := hfU.1 x hxU
  have hc' : fU x' < n := hfU.1 x' hx'U
  -- g (fU x) and g (fU x') are in A
  have hgxc : g (fU x) ∈ A := (hg _ hc).1
  have hgxc' : g (fU x') ∈ A := (hg _ hc').1
  -- Since fD is a chain coloring on D and both are in D, they're comparable
  have hcomp : g (fU x) ≤ g (fU x') ∨ g (fU x') ≤ g (fU x) :=
    hfD.2 (g (fU x)) (hAD hgxc) (g (fU x')) (hAD hgxc') heq
  -- But A is an antichain, so they must be equal
  have heqe : g (fU x) = g (fU x') := by
    rcases hcomp with hle | hle
    · exact Classical.byContradiction fun hne => hA hgxc hgxc' hne hle
    · exact Classical.byContradiction fun hne => hA hgxc' hgxc (Ne.symm hne) hle
  -- Since fU (g c) = c for all c < n, we have fU x = fU x'
  have hfUxeq : fU (g (fU x)) = fU x := (hg _ hc).2
  have hfUx'e : fU (g (fU x')) = fU x' := (hg _ hc').2
  have hfUeq : fU x = fU x' := by rw [← hfUxeq, ← hfUx'e, heqe]
  -- Now use hfU to conclude comparability
  exact hfU.2 x hxU x' hx'U hfUeq

/-- Gluing step, with the colour-matching function `g` given: `g c` picks out the element of the
antichain `A` with `fU`-colour `c`, and the glued colouring recolours an upper element `x` with
the `fD`-colour of the antichain element matching it. -/
lemma glue_of_matching {s D U A : Finset α} {n : ℕ} {fD fU : α → ℕ} {g : ℕ → α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAD : A ⊆ D) (hAU : A ⊆ U)
    (hsub : ∀ x ∈ s, x ∈ D ∨ x ∈ U)
    (hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y) (hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU)
    (hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c) :
    ChainColoring s n (fun x => if x ∈ D then fD x else fD (g (fU x))) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    by_cases hxD : x ∈ D
    · simpa only [if_pos hxD] using hfD.1 x hxD
    · have hxU : x ∈ U := (hsub x hx).resolve_left hxD
      have hc : fU x < n := hfU.1 x hxU
      simpa only [if_neg hxD] using hfD.1 _ (hAD (hg _ hc).1)
  · intro x hx x' hx' heq
    by_cases hxD : x ∈ D <;> by_cases hx'D : x' ∈ D
    · simp only [if_pos hxD, if_pos hx'D] at heq
      exact hfD.2 x hxD x' hx'D heq
    · simp only [if_pos hxD, if_neg hx'D] at heq
      have hx'U : x' ∈ U := (hsub x' hx').resolve_left hx'D
      exact glue_mixed hA hAD hAU hD hU hfD hfU hg hxD hx'U heq
    · simp only [if_neg hxD, if_pos hx'D] at heq
      have hxU : x ∈ U := (hsub x hx).resolve_left hxD
      exact (glue_mixed hA hAD hAU hD hU hfD hfU hg hx'D hxU heq.symm).symm
    · simp only [if_neg hxD, if_neg hx'D] at heq
      exact glue_upper hA hAD hfD hfU hg ((hsub x hx).resolve_left hxD)
        ((hsub x' hx').resolve_left hx'D) heq

/-- Gluing step: if `s` is contained in the union of a "lower part" `D` and an "upper part" `U`,
both of which are `n`-coloured and both of which contain the antichain `A` of size `n`, then `s`
admits an `n`-colouring. -/
lemma glue {s D U A : Finset α} {n : ℕ} {fD fU : α → ℕ}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAcard : A.card = n)
    (hAD : A ⊆ D) (hAU : A ⊆ U)
    (hsub : ∀ x ∈ s, x ∈ D ∨ x ∈ U)
    (hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y) (hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU) :
    ∃ f : α → ℕ, ChainColoring s n f := by
  classical
  rcases Finset.eq_empty_or_nonempty A with hAe | ⟨a₀, ha₀⟩
  · -- `A = ∅` forces `s = ∅`
    refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro x hx <;> subst hAe
    · rcases hsub x hx with h | h
      · obtain ⟨y, hy, -⟩ := hD x h; simp at hy
      · obtain ⟨y, hy, -⟩ := hU x h; simp at hy
    · rcases hsub x hx with h | h
      · obtain ⟨y, hy, -⟩ := hD x h; simp at hy
      · obtain ⟨y, hy, -⟩ := hU x h; simp at hy
  · set g : ℕ → α := fun c => if h : ∃ y, y ∈ A ∧ fU y = c then h.choose else a₀ with hgdef
    have hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c := by
      intro c hc
      have hex : ∃ y, y ∈ A ∧ fU y = c := by
        obtain ⟨y, hy, hfy⟩ := hfU.exists_of_lt hAU hA hAcard hc
        exact ⟨y, hy, hfy⟩
      simp only [hgdef, dif_pos hex]
      exact hex.choose_spec
    exact ⟨_, glue_of_matching hA hAD hAU hsub hD hU hfD hfU hg⟩

/-- If `A` is a maximum-size antichain of `s`, then every element of `s` is comparable with some
element of `A`. -/
lemma mem_up_or_down {s A : Finset α} {n : ℕ} (hAs : A ⊆ s)
    (hAanti : IsAntichain (· ≤ ·) (A : Set α)) (hAcard : A.card = n)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) {x : α} (hx : x ∈ s) :
    (∃ y ∈ A, x ≤ y) ∨ (∃ y ∈ A, y ≤ x) := by
  by_contra hne
  push_neg at hne
  have hx_notin : x ∉ A := by
    intro hx_in_A
    have := hne.1 x hx_in_A
    exact this (le_refl x)
  have hinsert : IsAntichain (· ≤ ·) (↑(insert x A) : Set α) := by
    rw [Finset.coe_insert]
    apply IsAntichain.insert hAanti
    · intro y hy hxy
      exact hne.2 y hy
    · intro y hy hxy
      exact hne.1 y hy
  have hsub : insert x A ⊆ s := by
    intro z hz
    simp at hz
    rcases hz with rfl | hz
    · exact hx
    · exact hAs hz
  have hcard : (insert x A).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hx_notin, hAcard]
  have := h (insert x A) hsub hinsert
  rw [hcard] at this
  omega

/-- First case of the inductive step: a colouring of `s` with the maximal element `a` and the
minimal element `b ≤ a` removed, using `n - 1` colours, extends to a colouring of `s` with `n`
colours by giving the chain `{b, a}` a fresh colour. -/
lemma step_case_one {s : Finset α} {a b : α} {n : ℕ} (hba : b ≤ a) (hn : 1 ≤ n)
    {f' : α → ℕ} (hf' : ChainColoring (s \ {a, b}) (n - 1) f') :
    ∃ f : α → ℕ, ChainColoring s n f := by
  let f : α → ℕ := fun x => if x = a ∨ x = b then n - 1 else f' x
  refine ⟨f, ?_, ?_⟩
  · -- f x < n for all x ∈ s
    intro x hx
    by_cases hxa : x = a ∨ x = b
    · simp [f, hxa]
      omega
    · simp [f, hxa]
      have hxmem : x ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hx, fun h => hxa (by simpa using Finset.mem_insert.mp h)⟩
      exact lt_trans (hf'.1 x hxmem) (Nat.sub_lt (by omega) (by omega))
  · -- comparability
    intro x hx y hy hxy
    by_cases hxa : x = a ∨ x = b
    · -- x ∈ {a, b}, so f x = n - 1
      have hfx : f x = n - 1 := by simp [f, hxa]
      rw [hfx] at hxy
      by_cases hyb : y = a ∨ y = b
      · -- y ∈ {a, b}, so both in {a, b}
        simp [f, hyb] at hxy
        rcases hxa with rfl | rfl <;> rcases hyb with rfl | rfl <;> simp_all
      · -- y ∉ {a, b}, so y ∈ s \ {a, b}
        have hyin : y ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hy, fun h => hyb (by simpa using Finset.mem_insert.mp h)⟩
        have hf'y : f y = f' y := by simp [f, hyb]
        rw [hf'y] at hxy
        have := hf'.1 y hyin
        omega
    · -- x ∉ {a, b}, so x ∈ s \ {a, b}
      have hxin : x ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hx, fun h => hxa (by simpa using Finset.mem_insert.mp h)⟩
      by_cases hyb : y = a ∨ y = b
      · -- y ∈ {a, b}
        have hfy : f y = n - 1 := by simp [f, hyb]
        have hfx : f x = f' x := by simp [f, hxa]
        rw [hfx, hfy] at hxy
        have := hf'.1 x hxin
        omega
      · -- y ∉ {a, b}, so y ∈ s \ {a, b}
        have hyin : y ∈ s \ {a, b} := Finset.mem_sdiff.mpr ⟨hy, fun h => hyb (by simpa using Finset.mem_insert.mp h)⟩
        have hfx : f x = f' x := by simp [f, hxa]
        have hfy : f y = f' y := by simp [f, hyb]
        rw [hfx, hfy] at hxy
        exact hf'.2 x hxin y hyin hxy

/-- Second case of the inductive step: `s` contains an antichain `A` of maximum size `n` avoiding
the maximal element `a` and the minimal element `b`.  Splitting `s` into the elements below `A`
and the elements above `A` and applying the inductive hypothesis to both halves, the two
colourings can be glued along `A`. -/
lemma step_case_two {s A : Finset α} {n : ℕ} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hamax : ∀ x ∈ s, a ≤ x → x = a) (hbmin : ∀ x ∈ s, x ≤ b → x = b)
    (haA : a ∉ A) (hbA : b ∉ A)
    (hAs : A ⊆ s) (hAanti : IsAntichain (· ≤ ·) (A : Set α)) (hAcard : A.card = n)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n)
    (IH : ∀ t : Finset α, t.card < s.card → ∀ m : ℕ,
      (∀ u ⊆ t, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ m) → ∃ f : α → ℕ, ChainColoring t m f) :
    ∃ f : α → ℕ, ChainColoring s n f := by
  classical
  -- Define D = {x ∈ s | ∃ y ∈ A, x ≤ y} and U = {x ∈ s | ∃ y ∈ A, y ≤ x}
  let pD : α → Prop := fun x => ∃ y ∈ A, x ≤ y
  let pU : α → Prop := fun x => ∃ y ∈ A, y ≤ x
  let D := Finset.filter (fun x => pD x) s
  let U := Finset.filter (fun x => pU x) s
  -- Show every element of s is in D or U
  have hsub : ∀ x ∈ s, x ∈ D ∨ x ∈ U := by
    intro x hx
    rcases mem_up_or_down hAs hAanti hAcard h hx with ⟨y, hy, hxy⟩ | ⟨y, hy, hyx⟩
    · left; exact Finset.mem_filter.mpr ⟨hx, y, hy, hxy⟩
    · right; exact Finset.mem_filter.mpr ⟨hx, y, hy, hyx⟩
  -- Show A ⊆ D and A ⊆ U
  have hAD : A ⊆ D := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hAs hx, x, hx, le_refl x⟩
  have hAU : A ⊆ U := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hAs hx, x, hx, le_refl x⟩
  -- Show the covering conditions
  have hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y := fun x hx => (Finset.mem_filter.mp hx).2
  have hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x := fun x hx => (Finset.mem_filter.mp hx).2
  -- Show D is a proper subset of s (a ∉ D because a is maximal and a ∉ A)
  have ha_notin_D : a ∉ D := by
    intro haD
    obtain ⟨y, hyA, hay⟩ := hD a haD
    have : y = a := hamax y (hAs hyA) hay
    exact haA (this ▸ hyA)
  have hDsub : D ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by
    intro heq
    exact ha_notin_D (heq ▸ ha)⟩
  have hD_card : D.card < s.card := Finset.card_lt_card hDsub
  -- Similarly U is a proper subset of s (b ∉ U because b is minimal and b ∉ A)
  have hb_notin_U : b ∉ U := by
    intro hbU
    obtain ⟨y, hyA, hyb⟩ := hU b hbU
    have : y = b := hbmin y (hAs hyA) hyb
    exact hbA (this ▸ hyA)
  have hUsub : U ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by
    intro heq
    exact hb_notin_U (heq ▸ hb)⟩
  have hU_card : U.card < s.card := Finset.card_lt_card hUsub
  -- Apply IH to D and U
  have hD_bound : ∀ u ⊆ D, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ n := by
    intro u hu hanti
    exact h u (hu.trans (Finset.filter_subset _ _)) hanti
  have hU_bound : ∀ u ⊆ U, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ n := by
    intro u hu hanti
    exact h u (hu.trans (Finset.filter_subset _ _)) hanti
  obtain ⟨fD, hfD⟩ := IH D hD_card n hD_bound
  obtain ⟨fU, hfU⟩ := IH U hU_card n hU_bound
  -- Use glue to combine
  exact glue hAanti hAcard hAD hAU hsub hD hU hfD hfU

/-- The inductive step in the proof of Dilworth's theorem. -/
lemma step (s : Finset α) (n : ℕ)
    (IH : ∀ t : Finset α, t.card < s.card → ∀ m : ℕ,
      (∀ u ⊆ t, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ m) → ∃ f : α → ℕ, ChainColoring t m f)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) :
    ∃ f : α → ℕ, ChainColoring s n f := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨a, ha, b, hb, hba, hamax, hbmin⟩ := exists_max_min hs
  have hn : 1 ≤ n := by
    have h1 : ({a} : Finset α).card ≤ n := by
      refine h {a} (by simpa using ha) ?_
      simp [Set.Subsingleton.isAntichain (Set.subsingleton_singleton) (· ≤ ·)]
    simpa using h1
  have hcardlt : (s \ {a, b}).card < s.card := by
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
    exact ⟨a, ha, by simp⟩
  by_cases hcase : ∃ A ⊆ s \ {a, b}, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = n
  · obtain ⟨A, hAsub, hAanti, hAcard⟩ := hcase
    have hAs : A ⊆ s := hAsub.trans Finset.sdiff_subset
    have haA : a ∉ A := fun hmem => by have := hAsub hmem; simp at this
    have hbA : b ∉ A := fun hmem => by have := hAsub hmem; simp at this
    exact step_case_two ha hb hamax hbmin haA hbA hAs hAanti hAcard h IH
  · push_neg at hcase
    have hbound : ∀ u ⊆ s \ {a, b}, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ n - 1 := by
      intro u hu hanti
      have h1 : u.card ≤ n := h u (hu.trans Finset.sdiff_subset) hanti
      have h2 : u.card ≠ n := hcase u hu hanti
      omega
    obtain ⟨f', hf'⟩ := IH (s \ {a, b}) hcardlt (n - 1) hbound
    exact step_case_one hba hn hf'

/-- Auxiliary form of Dilworth's theorem, proved by induction on the bound `m` for the size of
`s`, the inductive step being `step`. -/
lemma exists_chainColoring_aux (m : ℕ) : ∀ s : Finset α, s.card ≤ m → ∀ n : ℕ,
    (∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) → ∃ f : α → ℕ, ChainColoring s n f := by
  induction m with
  | zero =>
    intro s hs n hn
    have hs_empty : s = ∅ := by
      rw [Nat.le_zero] at hs
      exact Finset.card_eq_zero.mp hs
    exact ⟨fun _ => 0, by simp [hs_empty], by simp [hs_empty]⟩
  | succ m ih =>
    intros s hs n hn
    apply step s n _ hn
    intro t ht k hk
    have htcard : t.card ≤ m := by omega
    exact ih t htcard k hk

/-- Dilworth's theorem, colouring form: if every antichain of `s` has at most `n` elements, then
`s` can be coloured with `n` colours so that each colour class is a chain. -/
theorem exists_chainColoring (s : Finset α) (n : ℕ)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) :
    ∃ f : α → ℕ, ChainColoring s n f :=
  exists_chainColoring_aux s.card s le_rfl n h

/-- The easy converse: any antichain is at most as large as any family of chains covering the
order.  Together with `dilworth` this says that the maximum size of an antichain equals the
minimum number of chains needed to cover the order. -/
theorem card_le_card_of_cover (A : Finset α) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (C : Finset (Finset α)) (hC : ∀ c ∈ C, IsChain (· ≤ ·) (c : Set α))
    (hcov : ∀ a : α, ∃ c ∈ C, a ∈ c) : A.card ≤ C.card := by
  -- Define a function that picks a chain containing each element
  let g : α → Finset α := fun a => Classical.choose (hcov a)
  -- Show that g maps elements of A to elements of C
  have hg_in_C : ∀ a ∈ A, g a ∈ C := fun a ha => (Classical.choose_spec (hcov a)).1
  -- Now we show that the restriction of g to A is injective
  have hinj : Set.InjOn g ↑A := by
    intro a ha a' ha' heq
    have hain : a ∈ g a := (Classical.choose_spec (hcov a)).2
    have ha'in : a' ∈ g a' := (Classical.choose_spec (hcov a')).2
    rw [heq.symm] at ha'in
    -- Both a and a' are in g a, which is a chain
    have hchain : IsChain (· ≤ ·) (↑(g a) : Set α) := hC _ (hg_in_C a ha)
    cases eq_or_ne a a' with
    | inl h => exact h
    | inr hne =>
      have hcomp : a ≤ a' ∨ a' ≤ a := hchain hain ha'in hne
      cases hcomp with
      | inl hle => exact absurd hle (hA ha ha' hne)
      | inr hle => exact absurd hle (hA ha' ha hne.symm)
  -- Now conclude A.card ≤ C.card from injectivity
  have hmono : A.image g ⊆ C := by
    intro c hc
    rcases Finset.mem_image.1 hc with ⟨a, ha, rfl⟩
    exact hg_in_C a ha
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hmono

section Cover

variable [Fintype α]

/-- Dilworth's theorem: in a finite partial order in which every antichain has at most `n`
elements, the whole order can be covered by at most `n` chains. -/
theorem dilworth_cover (n : ℕ)
    (hanti : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ n) :
    ∃ C : Finset (Finset α), C.card ≤ n ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      (∀ a : α, ∃ c ∈ C, a ∈ c) := by
  obtain ⟨f, hf⟩ := exists_chainColoring (Finset.univ : Finset α) n
    (fun t _ hanti' => hanti t hanti')
  let C := Finset.image (fun c => Finset.filter (fun a => f a = c) Finset.univ) (Finset.range n)
  refine ⟨C, ?_, ?_, ?_⟩
  · -- C.card ≤ n
    exact Finset.card_image_le.trans (by simp)
  · -- Each c ∈ C is a chain
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨c', hc', hc_eq⟩ := hc
    rw [← hc_eq]
    intro x hx y hy hne
    simp at hx hy
    exact hf.2 x (by simp) y (by simp) (hx.trans hy.symm)
  · -- Cover: every a is in some c ∈ C
    intro a
    have hfa : f a < n := hf.1 a (by simp)
    refine ⟨Finset.filter (fun x => f x = f a) Finset.univ, ?_, ?_⟩
    · show Finset.filter (fun x => f x = f a) Finset.univ ∈ C
      change Finset.filter (fun x => f x = f a) Finset.univ ∈
        Finset.image (fun c => Finset.filter (fun a => f a = c) Finset.univ) (Finset.range n)
      exact Finset.mem_image.mpr ⟨f a, Finset.mem_range.mpr hfa, rfl⟩
    · simp

/-
The theorem as originally posed was:

```
theorem dilworth {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α]
    (n : ℕ)
    (hanti : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ n) :
    ∃ (C : Finset (Finset α)), C.card = n ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      (∀ a : α, ∃ c ∈ C, a ∈ c)
```

This is *false* as stated (see `exact_cover_counterexample` at the end of this file): the
hypothesis only says that `n` is an upper bound for the sizes of antichains, and if that bound is
not attained there need not exist `n` distinct chains at all.  The mathematical content of
Dilworth's theorem is recovered in the two statements below: `dilworth_cover` (a cover by at most
`n` chains, which is the substantial direction), and `dilworth`, which produces exactly `n`
chains under the additional hypothesis that `n` is the *maximum* size of an antichain.
-/

/-- Dilworth's theorem, exact form: if the maximum size of an antichain is `n` (i.e. every
antichain has at most `n` elements and some antichain has exactly `n` elements), then the order
can be covered by exactly `n` chains. -/
theorem dilworth (n : ℕ)
    (hanti : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ n)
    (hn : ∃ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) ∧ s.card = n) :
    ∃ C : Finset (Finset α), C.card = n ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      (∀ a : α, ∃ c ∈ C, a ∈ c) := by
  obtain ⟨s, hsanti, hscard⟩ := hn
  obtain ⟨C, hCle, hCchain, hCover⟩ := dilworth_cover n hanti
  have hsle : s.card ≤ C.card := card_le_card_of_cover s hsanti C hCchain hCover
  exact ⟨C, le_antisymm hCle (hscard ▸ hsle), hCchain, hCover⟩


end Cover

/-!
### The original formulation

The theorem was originally posed with the conclusion `C.card = n`, under the sole hypothesis that
every antichain has at most `n` elements.  In that form it is false: `n` must also be *attained*
by some antichain (as in `dilworth`), since a covering family of chains is a `Finset`, and there
may simply be fewer than `n` distinct chains available.  The following is an explicit
counterexample: the one-element order with `n = 3`.
-/

/-- The original formulation of Dilworth's theorem, which asks for a cover by exactly `n` chains
without assuming that the bound `n` on antichains is attained, is false. -/
theorem exact_cover_counterexample :
    (∀ s : Finset (Fin 1), IsAntichain (· ≤ ·) (s : Set (Fin 1)) → s.card ≤ 3) ∧
      ¬ ∃ C : Finset (Finset (Fin 1)), C.card = 3 ∧
        (∀ c ∈ C, IsChain (· ≤ ·) (c : Set (Fin 1))) ∧ (∀ a : Fin 1, ∃ c ∈ C, a ∈ c) := by
  constructor
  · intro s _hs
    exact le_trans (Finset.card_le_univ s) (by decide)
  · rintro ⟨C, hCcard, -, -⟩
    have hle : C.card ≤ 2 := by
      have := Finset.card_le_univ (C : Finset (Finset (Fin 1)))
      simpa using this
    omega

end Brockian.Dilworth

