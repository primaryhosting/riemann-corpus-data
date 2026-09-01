/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Arrow's impossibility theorem

A *ranking* of a type `A` of alternatives is a strict total order (transitive, total on
distinct elements, asymmetric).  A *social welfare function* is a map
`F : (V → Ranking A) → Ranking A` sending each profile of individual rankings (one for each
voter `i : V`) to a social ranking.

We prove: if `V` is a finite nonempty set of voters, `A` has at least three elements, and `F`
satisfies unanimity (Pareto) and independence of irrelevant alternatives (IIA), then `F` has a
dictator.  Equivalently, no `F` satisfies unanimity, IIA and non-dictatorship
(`Frontier.arrow_impossibility`).

Mathlib does not contain Arrow's theorem, so the development is from scratch.  The proof is the
classical one: a *field expansion* lemma (semi-decisiveness over one pair implies decisiveness
over all pairs) followed by a *group contraction* lemma (a decisive coalition splits into two
parts, one of which is decisive), and then induction on the size of the coalition starting from
the grand coalition, which is decisive by unanimity.
-/

namespace Frontier

/-- A strict total order ("ranking") on the type of alternatives `A`. -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_total : ∀ {x y}, x ≠ y → rel x y ∨ rel y x
  rel_asymm : ∀ {x y}, rel x y → ¬ rel y x

namespace Ranking

variable {A : Type*}

lemma rel_irrefl (R : Ranking A) (x : A) : ¬ R.rel x x := fun h => R.rel_asymm h h

lemma ne_of_rel {R : Ranking A} {x y : A} (h : R.rel x y) : x ≠ y := by
  rintro rfl; exact R.rel_irrefl x h

end Ranking

section Construction

variable {A : Type*}

/-- The ranking induced by a "score" function `f : A → ℕ`: lower score means more preferred,
ties are broken by a fixed well-ordering of `A`. -/
noncomputable def mkRank (f : A → ℕ) : Ranking A where
  rel x y := f x < f y ∨ (f x = f y ∧ WellOrderingRel x y)
  rel_trans := by
    rintro x y z (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, _root_.trans h1' h2'⟩
  rel_total := by
    intro x y hxy
    rcases lt_trichotomy (f x) (f y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases trichotomous_of WellOrderingRel x y with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd h' hxy
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  rel_asymm := by
    rintro x y (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · omega
    · omega
    · omega
    · exact asymm h1' h2'

lemma mkRank_of_lt {f : A → ℕ} {x y : A} (h : f x < f y) : (mkRank f).rel x y := Or.inl h

lemma mkRank_le {f : A → ℕ} {x y : A} (h : (mkRank f).rel x y) : f x ≤ f y := by
  rcases h with h | ⟨h, -⟩ <;> omega

lemma mkRank_not_of_lt {f : A → ℕ} {x y : A} (h : f y < f x) : ¬ (mkRank f).rel x y := by
  intro h'; have := mkRank_le h'; omega

/-- If a type has three distinct elements, then for any two elements there is a third one
distinct from both. -/
lemma exists_third (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) (u v : A) :
    ∃ w : A, w ≠ u ∧ w ≠ v := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h3
  by_contra hcon
  push_neg at hcon
  have key : ∀ w : A, w = u ∨ w = v := by
    intro w
    by_cases hw : w = u
    · exact Or.inl hw
    · exact Or.inr (hcon w hw)
  rcases key x with hx | hx <;> rcases key y with hy | hy <;> rcases key z with hz | hz <;>
    simp_all

end Construction

section Axioms

variable {V A : Type*}

/-- Unanimity / the Pareto condition. -/
def Pareto (F : (V → Ranking A) → Ranking A) : Prop :=
  ∀ (P : V → Ranking A) (x y : A), (∀ i, (P i).rel x y) → (F P).rel x y

/-- Independence of irrelevant alternatives. -/
def IIA (F : (V → Ranking A) → Ranking A) : Prop :=
  ∀ (P Q : V → Ranking A) (x y : A), (∀ i, ((P i).rel x y ↔ (Q i).rel x y)) →
    ((F P).rel x y ↔ (F Q).rel x y)

/-- Voter `i` is a dictator for `F`. -/
def IsDictator (F : (V → Ranking A) → Ranking A) (i : V) : Prop :=
  ∀ (P : V → Ranking A) (x y : A), (P i).rel x y → (F P).rel x y

/-- The coalition `S` is decisive for the ordered pair `(x, y)`. -/
def Decisive (F : (V → Ranking A) → Ranking A) (S : Finset V) (x y : A) : Prop :=
  ∀ P : V → Ranking A, (∀ i ∈ S, (P i).rel x y) → (F P).rel x y

/-- The coalition `S` is decisive for every ordered pair of distinct alternatives. -/
def DecisiveAll (F : (V → Ranking A) → Ranking A) (S : Finset V) : Prop :=
  ∀ x y : A, x ≠ y → Decisive F S x y

/-- The coalition `S` is semi-decisive for `(x, y)`: in *some* profile in which exactly the
members of `S` prefer `x` to `y`, society prefers `x` to `y`. -/
def SemiDecisive (F : (V → Ranking A) → Ranking A) (S : Finset V) (x y : A) : Prop :=
  ∃ P : V → Ranking A, (∀ i ∈ S, (P i).rel x y) ∧ (∀ i ∉ S, (P i).rel y x) ∧ (F P).rel x y

end Axioms

section Proof

variable {V A : Type*} {F : (V → Ranking A) → Ranking A}

/-- By IIA, semi-decisiveness in one profile transfers to every profile with the same
restriction to the pair `(x, y)`. -/
lemma semiDecisive_apply (hIIA : IIA F) {S : Finset V} {x y : A}
    (h : SemiDecisive F S x y) (P : V → Ranking A)
    (h1 : ∀ i ∈ S, (P i).rel x y) (h2 : ∀ i ∉ S, (P i).rel y x) : (F P).rel x y := by
  obtain ⟨Q, hQ1, hQ2, hQ⟩ := h
  refine ((hIIA Q P x y ?_).1 hQ)
  intro i
  by_cases hi : i ∈ S
  · simp [hQ1 i hi, h1 i hi]
  · constructor
    · intro hc; exact absurd hc ((Q i).rel_asymm (hQ2 i hi))
    · intro hc; exact absurd hc ((P i).rel_asymm (h2 i hi))

/-- Decisiveness implies semi-decisiveness. -/
lemma semiDecisive_of_decisive {S : Finset V} {x y : A} (hxy : x ≠ y)
    (h : Decisive F S x y) : SemiDecisive F S x y := by
  classical
  refine ⟨fun i => if i ∈ S then mkRank (fun z => if z = x then 0 else if z = y then 1 else 2)
      else mkRank (fun z => if z = y then 0 else if z = x then 1 else 2), ?_, ?_, ?_⟩
  · intro i hi
    simp only [if_pos hi]
    exact mkRank_of_lt (by simp [Ne.symm hxy])
  · intro i hi
    simp only [if_neg hi]
    exact mkRank_of_lt (by simp [hxy])
  · refine h _ ?_
    intro i hi
    simp only [if_pos hi]
    exact mkRank_of_lt (by simp [Ne.symm hxy])

/-- Field expansion, step A: if `S` is semi-decisive for `(p, q)` then it is decisive for
`(p, r)` for every third alternative `r`. -/
lemma decisive_fst (hPar : Pareto F) (hIIA : IIA F) {S : Finset V} {p q r : A}
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q) (hsd : SemiDecisive F S p q) :
    Decisive F S p r := by
  classical
  intro P hP
  -- Members of `S` rank `p > q > r`; the others rank `q` first and keep their `p`/`r` order.
  set f : A → ℕ := fun z => if z = p then 0 else if z = q then 1 else if z = r then 2 else 3
    with hf
  set g : V → A → ℕ := fun i z => if z = q then 0 else
      if z = p then (if (P i).rel p r then 1 else 2) else
      if z = r then (if (P i).rel p r then 2 else 1) else 3 with hg
  set Q : V → Ranking A := fun i => if i ∈ S then mkRank f else mkRank (g i) with hQ
  have hfp : f p = 0 := by simp [hf]
  have hfq : f q = 1 := by simp [hf, Ne.symm hpq]
  have hfr : f r = 2 := by simp [hf, hrp, hrq]
  have hgq : ∀ i, g i q = 0 := by intro i; simp [hg]
  have hgp : ∀ i, g i p = if (P i).rel p r then 1 else 2 := by intro i; simp [hg, hpq]
  have hgr : ∀ i, g i r = if (P i).rel p r then 2 else 1 := by
    intro i; simp [hg, hrq, hrp]
  have hQS : ∀ i ∈ S, Q i = mkRank f := by intro i hi; simp [hQ, hi]
  have hQn : ∀ i ∉ S, Q i = mkRank (g i) := by intro i hi; simp [hQ, hi]
  -- everybody prefers `q` to `r`
  have h1 : (F Q).rel q r := by
    refine hPar Q q r fun i => ?_
    by_cases hi : i ∈ S
    · rw [hQS i hi]; exact mkRank_of_lt (by rw [hfq, hfr]; norm_num)
    · rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgq i, hgr i]; split <;> norm_num
  -- semi-decisiveness gives `p` over `q`
  have h2 : (F Q).rel p q := by
    refine semiDecisive_apply hIIA hsd Q ?_ ?_
    · intro i hi; rw [hQS i hi]; exact mkRank_of_lt (by rw [hfp, hfq]; norm_num)
    · intro i hi
      rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgq i, hgp i]; split <;> norm_num
  have h3 : (F Q).rel p r := (F Q).rel_trans h2 h1
  refine (hIIA Q P p r ?_).1 h3
  intro i
  by_cases hi : i ∈ S
  · rw [hQS i hi]
    exact iff_of_true (mkRank_of_lt (by rw [hfp, hfr]; norm_num)) (hP i hi)
  · rw [hQn i hi]
    by_cases hpr : (P i).rel p r
    · refine iff_of_true (mkRank_of_lt ?_) hpr
      rw [hgp i, hgr i, if_pos hpr, if_pos hpr]; norm_num
    · refine iff_of_false (mkRank_not_of_lt ?_) hpr
      rw [hgp i, hgr i, if_neg hpr, if_neg hpr]; norm_num

/-- Field expansion, step B: if `S` is semi-decisive for `(p, q)` then it is decisive for
`(r, q)` for every third alternative `r`. -/
lemma decisive_snd (hPar : Pareto F) (hIIA : IIA F) {S : Finset V} {p q r : A}
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q) (hsd : SemiDecisive F S p q) :
    Decisive F S r q := by
  classical
  intro P hP
  -- Members of `S` rank `r > p > q`; the others rank `p` last and keep their `r`/`q` order.
  set f : A → ℕ := fun z => if z = r then 0 else if z = p then 1 else if z = q then 2 else 3
    with hf
  set g : V → A → ℕ := fun i z => if z = p then 2 else
      if z = r then (if (P i).rel r q then 0 else 1) else
      if z = q then (if (P i).rel r q then 1 else 0) else 3 with hg
  set Q : V → Ranking A := fun i => if i ∈ S then mkRank f else mkRank (g i) with hQ
  have hfr : f r = 0 := by simp [hf]
  have hfp : f p = 1 := by simp [hf, Ne.symm hrp]
  have hfq : f q = 2 := by simp [hf, Ne.symm hrq, Ne.symm hpq]
  have hgp : ∀ i, g i p = 2 := by intro i; simp [hg]
  have hgr : ∀ i, g i r = if (P i).rel r q then 0 else 1 := by intro i; simp [hg, hrp]
  have hgq : ∀ i, g i q = if (P i).rel r q then 1 else 0 := by
    intro i; simp [hg, Ne.symm hpq, Ne.symm hrq]
  have hQS : ∀ i ∈ S, Q i = mkRank f := by intro i hi; simp [hQ, hi]
  have hQn : ∀ i ∉ S, Q i = mkRank (g i) := by intro i hi; simp [hQ, hi]
  -- everybody prefers `r` to `p`
  have h1 : (F Q).rel r p := by
    refine hPar Q r p fun i => ?_
    by_cases hi : i ∈ S
    · rw [hQS i hi]; exact mkRank_of_lt (by rw [hfr, hfp]; norm_num)
    · rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgr i, hgp i]; split <;> norm_num
  -- semi-decisiveness gives `p` over `q`
  have h2 : (F Q).rel p q := by
    refine semiDecisive_apply hIIA hsd Q ?_ ?_
    · intro i hi; rw [hQS i hi]; exact mkRank_of_lt (by rw [hfp, hfq]; norm_num)
    · intro i hi
      rw [hQn i hi]
      refine mkRank_of_lt ?_
      rw [hgq i, hgp i]; split <;> norm_num
  have h3 : (F Q).rel r q := (F Q).rel_trans h1 h2
  refine (hIIA Q P r q ?_).1 h3
  intro i
  by_cases hi : i ∈ S
  · rw [hQS i hi]
    exact iff_of_true (mkRank_of_lt (by rw [hfr, hfq]; norm_num)) (hP i hi)
  · rw [hQn i hi]
    by_cases hrq' : (P i).rel r q
    · refine iff_of_true (mkRank_of_lt ?_) hrq'
      rw [hgr i, hgq i, if_pos hrq', if_pos hrq']; norm_num
    · refine iff_of_false (mkRank_not_of_lt ?_) hrq'
      rw [hgr i, hgq i, if_neg hrq', if_neg hrq']; norm_num

/-- Field expansion lemma: semi-decisiveness over a single pair implies decisiveness over
all pairs. -/
lemma decisiveAll_of_semiDecisive (hPar : Pareto F) (hIIA : IIA F)
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) {S : Finset V} {p q : A}
    (hpq : p ≠ q) (hsd : SemiDecisive F S p q) : DecisiveAll F S := by
  have stepA : ∀ {u v : A}, u ≠ v → SemiDecisive F S u v →
      ∀ w : A, w ≠ u → w ≠ v → Decisive F S u w :=
    fun huv hs w hwu hwv => decisive_fst hPar hIIA huv hwu hwv hs
  have stepB : ∀ {u v : A}, u ≠ v → SemiDecisive F S u v →
      ∀ w : A, w ≠ u → w ≠ v → Decisive F S w v :=
    fun huv hs w hwu hwv => decisive_snd hPar hIIA huv hwu hwv hs
  -- `S` is decisive for every pair `(p, t)`
  have step1 : ∀ t : A, t ≠ p → Decisive F S p t := by
    intro t ht
    by_cases htq : t = q
    · subst htq
      obtain ⟨z, hzp, hzt⟩ := exists_third h3 p t
      have d1 : Decisive F S p z := stepA hpq hsd z hzp hzt
      have s1 : SemiDecisive F S p z := semiDecisive_of_decisive (Ne.symm hzp) d1
      exact stepA (Ne.symm hzp) s1 t ht (Ne.symm hzt)
    · exact stepA hpq hsd t ht htq
  -- hence for every pair `(u, t)` with `t ≠ p`
  have step2 : ∀ t : A, t ≠ p → ∀ u : A, u ≠ t → Decisive F S u t := by
    intro t ht u hu
    by_cases hup : u = p
    · subst hup; exact step1 t ht
    · exact stepB (Ne.symm ht) (semiDecisive_of_decisive (Ne.symm ht) (step1 t ht)) u hup hu
  -- and finally for the pairs `(u, p)`
  have step3 : ∀ u : A, u ≠ p → Decisive F S u p := by
    intro u hu
    obtain ⟨z, hzp, hzu⟩ := exists_third h3 p u
    have d : Decisive F S u z := step2 z hzp u (Ne.symm hzu)
    exact stepA (Ne.symm hzu) (semiDecisive_of_decisive (Ne.symm hzu) d) p (Ne.symm hu)
      (Ne.symm hzp)
  intro x y hxy
  by_cases hy : y = p
  · subst hy; exact step3 x hxy
  · exact step2 y hy x hxy

/-- Group contraction: if a decisive coalition splits into two disjoint parts, one of the
parts is decisive. -/
lemma decisiveAll_split [DecidableEq V] (hPar : Pareto F) (hIIA : IIA F)
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) {S₁ S₂ : Finset V}
    (hdisj : Disjoint S₁ S₂) (h : DecisiveAll F (S₁ ∪ S₂)) :
    DecisiveAll F S₁ ∨ DecisiveAll F S₂ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  have h3' : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z := ⟨a, b, c, hab, hac, hbc⟩
  set f₁ : A → ℕ := fun z => if z = a then 0 else if z = b then 1 else if z = c then 2 else 3
    with hf₁
  set f₂ : A → ℕ := fun z => if z = b then 0 else if z = c then 1 else if z = a then 2 else 3
    with hf₂
  set f₃ : A → ℕ := fun z => if z = c then 0 else if z = a then 1 else if z = b then 2 else 3
    with hf₃
  set P : V → Ranking A :=
    fun i => if i ∈ S₁ then mkRank f₁ else if i ∈ S₂ then mkRank f₂ else mkRank f₃ with hP
  have h1a : f₁ a = 0 := by simp [hf₁]
  have h1b : f₁ b = 1 := by simp [hf₁, Ne.symm hab]
  have h1c : f₁ c = 2 := by simp [hf₁, Ne.symm hac, Ne.symm hbc]
  have h2b : f₂ b = 0 := by simp [hf₂]
  have h2c : f₂ c = 1 := by simp [hf₂, Ne.symm hbc]
  have h2a : f₂ a = 2 := by simp [hf₂, hab, hac]
  have h3c : f₃ c = 0 := by simp [hf₃]
  have h3a : f₃ a = 1 := by simp [hf₃, hac]
  have h3b : f₃ b = 2 := by simp [hf₃, hbc, Ne.symm hab]
  have hP₁ : ∀ i ∈ S₁, P i = mkRank f₁ := by intro i hi; simp [hP, hi]
  have hP₂ : ∀ i, i ∉ S₁ → i ∈ S₂ → P i = mkRank f₂ := by intro i hi hi2; simp [hP, hi, hi2]
  have hP₃ : ∀ i, i ∉ S₁ → i ∉ S₂ → P i = mkRank f₃ := by intro i hi hi2; simp [hP, hi, hi2]
  -- the whole coalition prefers `b` to `c`
  have hbc' : (F P).rel b c := by
    refine h b c hbc P ?_
    intro i hi
    by_cases h₁ : i ∈ S₁
    · rw [hP₁ i h₁]; exact mkRank_of_lt (by rw [h1b, h1c]; norm_num)
    · have h₂ : i ∈ S₂ := by
        rcases Finset.mem_union.1 hi with h' | h'
        · exact absurd h' h₁
        · exact h'
      rw [hP₂ i h₁ h₂]; exact mkRank_of_lt (by rw [h2b, h2c]; norm_num)
  by_cases hcase : (F P).rel a c
  · -- then `S₁` is semi-decisive for `(a, c)`
    left
    refine decisiveAll_of_semiDecisive hPar hIIA h3' hac ⟨P, ?_, ?_, hcase⟩
    · intro i hi; rw [hP₁ i hi]; exact mkRank_of_lt (by rw [h1a, h1c]; norm_num)
    · intro i hi
      by_cases h₂ : i ∈ S₂
      · rw [hP₂ i hi h₂]; exact mkRank_of_lt (by rw [h2c, h2a]; norm_num)
      · rw [hP₃ i hi h₂]; exact mkRank_of_lt (by rw [h3c, h3a]; norm_num)
  · -- otherwise `S₂` is semi-decisive for `(b, a)`
    right
    have hca : (F P).rel c a := ((F P).rel_total hac).resolve_left hcase
    have hba : (F P).rel b a := (F P).rel_trans hbc' hca
    refine decisiveAll_of_semiDecisive hPar hIIA h3' (Ne.symm hab) ⟨P, ?_, ?_, hba⟩
    · intro i hi
      have h₁ : i ∉ S₁ := fun hc => (Finset.disjoint_left.1 hdisj hc) hi
      rw [hP₂ i h₁ hi]; exact mkRank_of_lt (by rw [h2b, h2a]; norm_num)
    · intro i hi
      by_cases h₁ : i ∈ S₁
      · rw [hP₁ i h₁]; exact mkRank_of_lt (by rw [h1a, h1b]; norm_num)
      · rw [hP₃ i h₁ hi]; exact mkRank_of_lt (by rw [h3a, h3b]; norm_num)

/-- A nonempty decisive coalition contains a decisive singleton. -/
lemma exists_decisive_singleton [DecidableEq V] (hPar : Pareto F) (hIIA : IIA F)
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) :
    ∀ (n : ℕ) (S : Finset V), S.card ≤ n → S.Nonempty → DecisiveAll F S →
      ∃ i ∈ S, DecisiveAll F {i} := by
  intro n
  induction n with
  | zero =>
    intro S hcard hne _
    exact absurd (Finset.card_pos.2 hne) (by omega)
  | succ n ih =>
    intro S hcard hne hdec
    obtain ⟨i, hi⟩ := hne
    by_cases hsing : S = {i}
    · exact ⟨i, hi, hsing ▸ hdec⟩
    · have hsplit : ({i} ∪ S.erase i : Finset V) = S := by
        rw [Finset.singleton_union, Finset.insert_erase hi]
      have hdisj : Disjoint ({i} : Finset V) (S.erase i) :=
        Finset.disjoint_singleton_left.2 (Finset.notMem_erase i S)
      have hne' : (S.erase i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hc
        rcases (Finset.erase_eq_empty_iff _ _).1 hc with hc' | hc'
        · exact absurd hi (by simp [hc'])
        · exact hsing hc'
      have hcard' : (S.erase i).card ≤ n := by
        have := Finset.card_erase_of_mem hi
        have h2 := Finset.card_pos.2 ⟨i, hi⟩
        omega
      have hdec' : DecisiveAll F ({i} ∪ S.erase i) := by rw [hsplit]; exact hdec
      rcases decisiveAll_split hPar hIIA h3 hdisj hdec' with hL | hR
      · exact ⟨i, hi, hL⟩
      · obtain ⟨j, hj, hjd⟩ := ih (S.erase i) hcard' hne' hR
        exact ⟨j, Finset.mem_of_mem_erase hj, hjd⟩

/-- **Arrow's theorem** (dictator form): a social welfare function on at least three
alternatives satisfying unanimity and IIA has a dictator. -/
theorem exists_dictator [Fintype V] [Nonempty V]
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (F : (V → Ranking A) → Ranking A) (hPar : Pareto F) (hIIA : IIA F) :
    ∃ i : V, IsDictator F i := by
  classical
  have hdec : DecisiveAll F (Finset.univ : Finset V) := by
    intro x y _ P hP
    exact hPar P x y fun i => hP i (Finset.mem_univ i)
  obtain ⟨i, -, hi⟩ := exists_decisive_singleton hPar hIIA h3 (Finset.univ : Finset V).card
    Finset.univ le_rfl Finset.univ_nonempty hdec
  refine ⟨i, fun P x y hxy => ?_⟩
  by_cases hne : x = y
  · subst hne; exact absurd hxy ((P i).rel_irrefl x)
  · refine hi x y hne P ?_
    intro j hj
    rw [Finset.mem_singleton.1 hj]
    exact hxy

/-- **Arrow's impossibility theorem**: for at least three alternatives, no social welfare
function satisfies unanimity, independence of irrelevant alternatives, and
non-dictatorship. -/
theorem arrow_impossibility [Fintype V] [Nonempty V]
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (F : (V → Ranking A) → Ranking A) :
    ¬ (Pareto F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hPar, hIIA, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator h3 F hPar hIIA
  exact hnd i hi

/-- Sanity check (non-vacuity): the projection onto a single voter is a social welfare
function satisfying unanimity and IIA; by Arrow's theorem it must be — and indeed is —
dictatorial. -/
example (i₀ : V) : Pareto (fun P : V → Ranking A => P i₀) ∧ IIA (fun P : V → Ranking A => P i₀) ∧
    IsDictator (fun P : V → Ranking A => P i₀) i₀ :=
  ⟨fun _ _ _ h => h i₀, fun _ _ _ _ h => h i₀, fun _ _ _ h => h⟩

end Proof

end Frontier

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

