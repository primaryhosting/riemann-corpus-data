/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/
theorem arrow_impossibility_fintype {V : Type*} [Fintype V]
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F)
    (hND : ∀ v : V, ¬ Dictator F v) : False :=
  arrow_impossibility (Finset.univ.toList) (fun v => by simp) F hU hIIA hND

/-- Positive form: on a finite set of voters, every unanimous social welfare function
satisfying independence of irrelevant alternatives has a dictator. -/
theorem exists_dictator_fintype {V : Type*} [Fintype V]
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F) :
    ∃ v : V, Dictator F v :=
  exists_dictator (Finset.univ.toList) (fun v => by simp) F hU hIIA

end Frontier

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

attribute [local instance] Classical.propDecidable

/-! ## Rankings of three alternatives

The three alternatives are the elements of `Fin 3`.  A *ranking* is a strict linear order on
them, encoded by its rank function: `r.rank a` is the position of alternative `a` (smaller is
better), and distinct alternatives get distinct positions. -/

/-- A strict ranking of the three alternatives, encoded by an injective rank function. -/
structure Ranking where
  /-- The position of an alternative; smaller means more preferred. -/
  rank : Fin 3 → Nat
  /-- Distinct alternatives occupy distinct positions (no ties). -/
  inj : ∀ a b, rank a = rank b → a = b

/-- `prefers r a b` says that the ranking `r` strictly prefers `a` to `b`. -/
def prefers (r : Ranking) (a b : Fin 3) : Prop := r.rank a < r.rank b

theorem prefers_irrefl (r : Ranking) (a : Fin 3) : ¬ prefers r a a := Nat.lt_irrefl _

theorem prefers_trans {r : Ranking} {a b c : Fin 3} (h₁ : prefers r a b) (h₂ : prefers r b c) :
    prefers r a c := Nat.lt_trans h₁ h₂

theorem prefers_asymm {r : Ranking} {a b : Fin 3} (h : prefers r a b) : ¬ prefers r b a :=
  Nat.lt_asymm h

/-- Rankings are total: of two distinct alternatives, one is preferred. -/
theorem prefers_total {r : Ranking} {a b : Fin 3} (hab : a ≠ b) (h : ¬ prefers r a b) :
    prefers r b a := by
  rcases Nat.lt_trichotomy (r.rank a) (r.rank b) with h₁ | h₁ | h₁
  · exact absurd h₁ h
  · exact absurd (r.inj a b h₁) hab
  · exact h₁

/-! ## Building rankings -/

/-- The rank function of the ranking `x ≻ y ≻ z`. -/
def rankFn (x y z a : Fin 3) : Nat :=
  if a = x then 0 else if a = y then 1 else if a = z then 2 else 3

theorem rankFn_inj {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ a b, rankFn x y z a = rankFn x y z b → a = b := by
  revert hxy hxz hyz
  revert x y z
  decide

/-- The ranking `x ≻ y ≻ z`, for three distinct alternatives `x`, `y`, `z`. -/
def mkRank (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Ranking :=
  ⟨rankFn x y z, rankFn_inj hxy hxz hyz⟩

@[simp] theorem mkRank_fst {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (mkRank x y z hxy hxz hyz).rank x = 0 := by
  simp [mkRank, rankFn]

@[simp] theorem mkRank_snd {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (mkRank x y z hxy hxz hyz).rank y = 1 := by
  simp [mkRank, rankFn, Ne.symm hxy]

@[simp] theorem mkRank_trd {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (mkRank x y z hxy hxz hyz).rank z = 2 := by
  simp [mkRank, rankFn, Ne.symm hxz, Ne.symm hyz]

/-- Given two distinct alternatives there is a third one. -/
theorem exists_third : ∀ x y : Fin 3, x ≠ y → ∃ c : Fin 3, c ≠ x ∧ c ≠ y := by decide

/-- Three pairwise distinct alternatives exhaust `Fin 3`. -/
theorem fin3_trichotomy :
    ∀ x y c z : Fin 3, x ≠ y → c ≠ x → c ≠ y → z = x ∨ z = y ∨ z = c := by decide

/-! ## Social welfare functions and Arrow's conditions -/

universe u

variable {V : Type u}

/-- A social welfare function aggregates a profile of individual rankings into a social
ranking.  It is *unanimous* (Pareto efficient) if society prefers `a` to `b` whenever every
voter does. -/
def Unanimous (F : (V → Ranking) → Ranking) : Prop :=
  ∀ (p : V → Ranking) (a b : Fin 3), (∀ v, prefers (p v) a b) → prefers (F p) a b

/-- *Independence of irrelevant alternatives*: the social preference between `a` and `b`
depends only on the individual preferences between `a` and `b`. -/
def IIA (F : (V → Ranking) → Ranking) : Prop :=
  ∀ (p q : V → Ranking) (a b : Fin 3),
    (∀ v, prefers (p v) a b ↔ prefers (q v) a b) → (prefers (F p) a b ↔ prefers (F q) a b)

/-- Voter `v` is a *dictator* for `F` if the social preference always follows `v`'s. -/
def Dictator (F : (V → Ranking) → Ranking) (v : V) : Prop :=
  ∀ (p : V → Ranking) (a b : Fin 3), prefers (p v) a b → prefers (F p) a b

/-! ## Decisive coalitions

Coalitions are represented by lists of voters; only the membership predicate matters. -/

/-- The coalition `S` is *decisive* for the ordered pair `(a, b)`: whenever all of its members
prefer `a` to `b`, so does society. -/
def Decisive (F : (V → Ranking) → Ranking) (S : List V) (a b : Fin 3) : Prop :=
  ∀ p : V → Ranking, (∀ v ∈ S, prefers (p v) a b) → prefers (F p) a b

/-- The coalition `S` is *semi-decisive* for `(a, b)`: whenever all of its members prefer `a`
to `b` and everybody else prefers `b` to `a`, society prefers `a` to `b`. -/
def SemiDecisive (F : (V → Ranking) → Ranking) (S : List V) (a b : Fin 3) : Prop :=
  ∀ p : V → Ranking, (∀ v ∈ S, prefers (p v) a b) → (∀ v, v ∉ S → prefers (p v) b a) →
    prefers (F p) a b

theorem semiDecisive_of_decisive {F : (V → Ranking) → Ranking} {S : List V} {a b : Fin 3}
    (h : Decisive F S a b) : SemiDecisive F S a b := fun p hp _ => h p hp

/-- Field expansion, first half: a coalition semi-decisive for `(a,b)` is decisive for `(a,c)`. -/
theorem expand₁ {F : (V → Ranking) → Ranking} (hU : Unanimous F) (hIIA : IIA F) {S : List V}
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSD : SemiDecisive F S a b) : Decisive F S a c := by
  intro q hq
  -- members of `S` rank `a ≻ b ≻ c`; everybody else puts `b` on top and keeps their
  -- own opinion on `a` versus `c`
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun v =>
      if v ∈ S then mkRank a b c hab hac hbc
      else if (q v).rank a < (q v).rank c then mkRank b a c (Ne.symm hab) hbc hac
      else mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := ⟨_, rfl⟩
  have hin : ∀ v, v ∈ S → p v = mkRank a b c hab hac hbc := by
    intro v hv; rw [hp]; simp [hv]
  have hout₁ : ∀ v, v ∉ S → (q v).rank a < (q v).rank c →
      p v = mkRank b a c (Ne.symm hab) hbc hac := by
    intro v hv h; rw [hp]; simp [hv, h]
  have hout₂ : ∀ v, v ∉ S → ¬ ((q v).rank a < (q v).rank c) →
      p v = mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := by
    intro v hv h; rw [hp]; simp [hv, h]
  -- society prefers `a` to `b`, since `S` is semi-decisive for that pair
  have hab' : prefers (F p) a b := by
    refine hSD p ?_ ?_
    · intro v hv; simp [prefers, hin v hv]
    · intro v hv
      by_cases h : (q v).rank a < (q v).rank c
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  -- everybody prefers `b` to `c`, so society does too
  have hbc' : prefers (F p) b c := by
    refine hU p b c ?_
    intro v
    by_cases hv : v ∈ S
    · simp [prefers, hin v hv]
    · by_cases h : (q v).rank a < (q v).rank c
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  -- `p` and `q` agree on `a` versus `c`
  have hkey : ∀ v, prefers (p v) a c ↔ prefers (q v) a c := by
    intro v
    by_cases hv : v ∈ S
    · exact iff_of_true (by simp [prefers, hin v hv]) (hq v hv)
    · by_cases h : (q v).rank a < (q v).rank c
      · exact iff_of_true (by simp [prefers, hout₁ v hv h]) h
      · exact iff_of_false (by simp [prefers, hout₂ v hv h]) h
  exact (hIIA p q a c hkey).mp (prefers_trans hab' hbc')

/-- Field expansion, second half: a coalition semi-decisive for `(a,b)` is decisive for `(c,b)`. -/
theorem expand₂ {F : (V → Ranking) → Ranking} (hU : Unanimous F) (hIIA : IIA F) {S : List V}
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSD : SemiDecisive F S a b) : Decisive F S c b := by
  intro q hq
  -- members of `S` rank `c ≻ a ≻ b`; everybody else puts `a` at the bottom and keeps their
  -- own opinion on `c` versus `b`
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun v =>
      if v ∈ S then mkRank c a b (Ne.symm hac) (Ne.symm hbc) hab
      else if (q v).rank c < (q v).rank b then
        mkRank c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab)
      else mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := ⟨_, rfl⟩
  have hin : ∀ v, v ∈ S → p v = mkRank c a b (Ne.symm hac) (Ne.symm hbc) hab := by
    intro v hv; rw [hp]; simp [hv]
  have hout₁ : ∀ v, v ∉ S → (q v).rank c < (q v).rank b →
      p v = mkRank c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) := by
    intro v hv h; rw [hp]; simp [hv, h]
  have hout₂ : ∀ v, v ∉ S → ¬ ((q v).rank c < (q v).rank b) →
      p v = mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := by
    intro v hv h; rw [hp]; simp [hv, h]
  have hab' : prefers (F p) a b := by
    refine hSD p ?_ ?_
    · intro v hv; simp [prefers, hin v hv]
    · intro v hv
      by_cases h : (q v).rank c < (q v).rank b
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  have hca' : prefers (F p) c a := by
    refine hU p c a ?_
    intro v
    by_cases hv : v ∈ S
    · simp [prefers, hin v hv]
    · by_cases h : (q v).rank c < (q v).rank b
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  have hkey : ∀ v, prefers (p v) c b ↔ prefers (q v) c b := by
    intro v
    by_cases hv : v ∈ S
    · exact iff_of_true (by simp [prefers, hin v hv]) (hq v hv)
    · by_cases h : (q v).rank c < (q v).rank b
      · exact iff_of_true (by simp [prefers, hout₁ v hv h]) h
      · exact iff_of_false (by simp [prefers, hout₂ v hv h]) h
  exact (hIIA p q c b hkey).mp (prefers_trans hca' hab')

/-- Field expansion: a coalition semi-decisive for one pair is decisive for every pair. -/
theorem allDecisive_of_semiDecisive {F : (V → Ranking) → Ranking} (hU : Unanimous F)
    (hIIA : IIA F) {S : List V} {x y : Fin 3} (hxy : x ≠ y) (hSD : SemiDecisive F S x y) :
    ∀ z w : Fin 3, z ≠ w → Decisive F S z w := by
  obtain ⟨c, hcx, hcy⟩ : ∃ c : Fin 3, c ≠ x ∧ c ≠ y := exists_third x y hxy
  have hxc : x ≠ c := Ne.symm hcx
  have hyc : y ≠ c := Ne.symm hcy
  have Dxc : Decisive F S x c := expand₁ hU hIIA hxy hxc hyc hSD
  have Dcy : Decisive F S c y := expand₂ hU hIIA hxy hxc hyc hSD
  have Dyc : Decisive F S y c :=
    expand₂ hU hIIA hxc hxy hcy (semiDecisive_of_decisive Dxc)
  have Dcx : Decisive F S c x :=
    expand₁ hU hIIA hcy hcx (Ne.symm hxy) (semiDecisive_of_decisive Dcy)
  have Dxy : Decisive F S x y :=
    expand₂ hU hIIA hcy hcx (Ne.symm hxy) (semiDecisive_of_decisive Dcy)
  have Dyx : Decisive F S y x :=
    expand₂ hU hIIA hcx hcy hxy (semiDecisive_of_decisive Dcx)
  intro z w hzw
  have hz : z = x ∨ z = y ∨ z = c := fin3_trichotomy x y c z hxy hcx hcy
  have hw : w = x ∨ w = y ∨ w = c := fin3_trichotomy x y c w hxy hcx hcy
  rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hzw
      | assumption

/-- The splitting (contraction) lemma: if the disjoint union `S₁ ++ S₂` is decisive for
`(0,1)`, then one of `S₁`, `S₂` is semi-decisive for some pair. -/
theorem split_semiDecisive {F : (V → Ranking) → Ranking} (hIIA : IIA F) {S₁ S₂ : List V}
    (hdisj : ∀ v, v ∈ S₁ → v ∉ S₂) (hdec : Decisive F (S₁ ++ S₂) 0 1) :
    (∃ x y : Fin 3, x ≠ y ∧ SemiDecisive F S₁ x y) ∨
      (∃ x y : Fin 3, x ≠ y ∧ SemiDecisive F S₂ x y) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- `S₁` votes `0 ≻ 1 ≻ 2`, `S₂` votes `2 ≻ 0 ≻ 1`, everybody else votes `1 ≻ 2 ≻ 0`
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun v =>
      if v ∈ S₁ then mkRank 0 1 2 h01 h02 h12
      else if v ∈ S₂ then mkRank 2 0 1 (Ne.symm h02) (Ne.symm h12) h01
      else mkRank 1 2 0 h12 (Ne.symm h01) (Ne.symm h02) := ⟨_, rfl⟩
  have h₁ : ∀ v, v ∈ S₁ → p v = mkRank 0 1 2 h01 h02 h12 := by
    intro v hv; rw [hp]; simp [hv]
  have h₂ : ∀ v, v ∉ S₁ → v ∈ S₂ → p v = mkRank 2 0 1 (Ne.symm h02) (Ne.symm h12) h01 := by
    intro v hv1 hv2; rw [hp]; simp [hv1, hv2]
  have h₃ : ∀ v, v ∉ S₁ → v ∉ S₂ → p v = mkRank 1 2 0 h12 (Ne.symm h01) (Ne.symm h02) := by
    intro v hv1 hv2; rw [hp]; simp [hv1, hv2]
  have hFab : prefers (F p) 0 1 := by
    refine hdec p ?_
    intro v hv
    rcases List.mem_append.mp hv with hv1 | hv2
    · simp [prefers, h₁ v hv1]
    · by_cases hv1 : v ∈ S₁
      · simp [prefers, h₁ v hv1]
      · simp [prefers, h₂ v hv1 hv2]
  by_cases hcase : prefers (F p) 0 2
  · -- `S₁` is semi-decisive for `(0, 2)`
    left
    refine ⟨0, 2, h02, ?_⟩
    intro q hq1 hq2
    have hkey : ∀ v, prefers (p v) 0 2 ↔ prefers (q v) 0 2 := by
      intro v
      by_cases hv : v ∈ S₁
      · exact iff_of_true (by simp [prefers, h₁ v hv]) (hq1 v hv)
      · have hq : ¬ prefers (q v) 0 2 := prefers_asymm (hq2 v hv)
        by_cases hv2 : v ∈ S₂
        · exact iff_of_false (by simp [prefers, h₂ v hv hv2]) hq
        · exact iff_of_false (by simp [prefers, h₃ v hv hv2]) hq
    exact (hIIA p q 0 2 hkey).mp hcase
  · -- `S₂` is semi-decisive for `(2, 1)`
    right
    refine ⟨2, 1, Ne.symm h12, ?_⟩
    intro q hq1 hq2
    have h20 : prefers (F p) 2 0 := prefers_total h02 hcase
    have h21 : prefers (F p) 2 1 := prefers_trans h20 hFab
    have hkey : ∀ v, prefers (p v) 2 1 ↔ prefers (q v) 2 1 := by
      intro v
      by_cases hv2 : v ∈ S₂
      · have hv1 : v ∉ S₁ := fun h => hdisj v h hv2
        exact iff_of_true (by simp [prefers, h₂ v hv1 hv2]) (hq1 v hv2)
      · have hq : ¬ prefers (q v) 2 1 := prefers_asymm (hq2 v hv2)
        by_cases hv1 : v ∈ S₁
        · exact iff_of_false (by simp [prefers, h₁ v hv1]) hq
        · exact iff_of_false (by simp [prefers, h₃ v hv1 hv2]) hq
    exact (hIIA p q 2 1 hkey).mp h21

/-- The empty coalition is not decisive. -/
theorem not_decisive_nil {F : (V → Ranking) → Ranking}
    (h : ∀ z w : Fin 3, z ≠ w → Decisive F ([] : List V) z w) : False := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun _ => mkRank 0 1 2 h01 h02 h12 := ⟨_, rfl⟩
  have h1 : prefers (F p) 0 1 := h 0 1 h01 p (by intro v hv; cases hv)
  have h2 : prefers (F p) 1 0 := h 1 0 (Ne.symm h01) p (by intro v hv; cases hv)
  exact prefers_asymm h1 h2

/-- Contraction of decisive coalitions: a coalition that is decisive for every pair contains
a single voter that is decisive for every pair. -/
theorem exists_singleton_decisive {F : (V → Ranking) → Ranking} (hU : Unanimous F)
    (hIIA : IIA F) :
    ∀ (n : Nat) (S : List V), S.length ≤ n → (∀ z w : Fin 3, z ≠ w → Decisive F S z w) →
      ∃ v, v ∈ S ∧ ∀ z w : Fin 3, z ≠ w → Decisive F [v] z w := by
  intro n
  induction n with
  | zero =>
    intro S hlen hdec
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hS
    exact absurd hdec (fun h => not_decisive_nil h)
  | succ n ih =>
    intro S hlen hdec
    match S with
    | [] => exact absurd hdec (fun h => not_decisive_nil h)
    | v :: rest =>
      by_cases hv : v ∈ rest
      · -- `v` is redundant: pass to the shorter list `rest`
        have hdec' : ∀ z w : Fin 3, z ≠ w → Decisive F rest z w := by
          intro z w hzw q hq
          refine hdec z w hzw q ?_
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hq u hv
          · exact hq u hu
        obtain ⟨v', hv', hd⟩ := ih rest (Nat.le_of_succ_le_succ hlen) hdec'
        exact ⟨v', List.mem_cons_of_mem _ hv', hd⟩
      · have hdisj : ∀ u, u ∈ [v] → u ∉ rest := by
          intro u hu
          rcases List.mem_singleton.mp hu with rfl
          exact hv
        have hdec01 : Decisive F ([v] ++ rest) 0 1 := by
          simpa using hdec 0 1 (by decide)
        rcases split_semiDecisive hIIA hdisj hdec01 with ⟨x, y, hxy, hSD⟩ | ⟨x, y, hxy, hSD⟩
        · exact ⟨v, List.mem_cons_self .., allDecisive_of_semiDecisive hU hIIA hxy hSD⟩
        · obtain ⟨v', hv', hd⟩ :=
            ih rest (Nat.le_of_succ_le_succ hlen)
              (allDecisive_of_semiDecisive hU hIIA hxy hSD)
          exact ⟨v', List.mem_cons_of_mem _ hv', hd⟩

/-! ## Arrow's impossibility theorem -/

/-- **Arrow's impossibility theorem** (base case: three alternatives, finitely many voters).

There is no social welfare function on finitely many voters (finiteness is expressed by a
list `L` of voters containing everyone) that aggregates strict rankings of three
alternatives, is unanimous (Pareto), satisfies independence of irrelevant alternatives, and
has no dictator. -/
theorem arrow_impossibility {V : Type u} (L : List V) (hL : ∀ v : V, v ∈ L)
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F)
    (hND : ∀ v : V, ¬ Dictator F v) : False := by
  have hdec : ∀ z w : Fin 3, z ≠ w → Decisive F L z w := by
    intro z w _ p hp
    exact hU p z w fun v => hp v (hL v)
  obtain ⟨v, _, hv⟩ := exists_singleton_decisive hU hIIA L.length L (Nat.le_refl _) hdec
  refine hND v ?_
  intro p a b hab
  by_cases hab' : a = b
  · subst hab'
    exact absurd hab (prefers_irrefl _ _)
  · exact hv a b hab' p (by
      intro u hu
      rcases List.mem_singleton.mp hu with rfl
      exact hab)

/-- Equivalent positive form: any unanimous social welfare function satisfying independence
of irrelevant alternatives has a dictator. -/
theorem exists_dictator {V : Type u} (L : List V) (hL : ∀ v : V, v ∈ L)
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F) :
    ∃ v : V, Dictator F v := by
  refine Classical.byContradiction fun hc => ?_
  exact arrow_impossibility L hL F hU hIIA (fun v hv => hc ⟨v, hv⟩)

/-! ## Sanity check: the other two conditions are consistent

Dropping non-dictatorship, the remaining conditions are satisfiable: the rule "copy voter
`v₀`'s ranking" is unanimous and satisfies independence of irrelevant alternatives. -/

theorem projection_unanimous {V : Type u} (v₀ : V) :
    Unanimous (fun p : V → Ranking => p v₀) := fun _ _ _ h => h v₀

theorem projection_iia {V : Type u} (v₀ : V) :
    IIA (fun p : V → Ranking => p v₀) := fun _ _ _ _ h => h v₀

theorem projection_dictator {V : Type u} (v₀ : V) :
    Dictator (fun p : V → Ranking => p v₀) v₀ := fun _ _ _ h => h

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

