import Mathlib
/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- A (strict) ranking of three alternatives, given by an injective "rank" function:
`rank a < rank b` means that `a` is strictly preferred to `b`. -/
structure Ranking where
  rank : Fin 3 → Fin 3
  rank_inj : Function.Injective rank

/-- `Prefers r a b` : the ranking `r` strictly prefers `a` to `b`. -/
def Prefers (r : Ranking) (a b : Fin 3) : Prop := r.rank a < r.rank b

/-- A social welfare function is unanimous (Pareto) if whenever every voter prefers `a` to `b`,
so does society. -/
def Unanimous (F : (Fin 2 → Ranking) → Ranking) : Prop :=
  ∀ (p : Fin 2 → Ranking) (a b : Fin 3), (∀ i, Prefers (p i) a b) → Prefers (F p) a b

/-- Independence of irrelevant alternatives: the social ranking of `a` versus `b` depends only
on the voters' rankings of `a` versus `b`. -/
def IIA (F : (Fin 2 → Ranking) → Ranking) : Prop :=
  ∀ (p q : Fin 2 → Ranking) (a b : Fin 3),
    (∀ i, (Prefers (p i) a b ↔ Prefers (q i) a b)) →
      (Prefers (F p) a b ↔ Prefers (F q) a b)

/-- Voter `d` is a dictator: society always follows `d`'s strict preferences. -/
def IsDictator (F : (Fin 2 → Ranking) → Ranking) (d : Fin 2) : Prop :=
  ∀ (p : Fin 2 → Ranking) (a b : Fin 3), Prefers (p d) a b → Prefers (F p) a b

/-- The other of the two voters. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

lemma other_ne (i : Fin 2) : other i ≠ i := by revert i; decide

lemma eq_or_eq_other (i j : Fin 2) : j = i ∨ j = other i := by revert i j; decide

lemma Prefers.asymm {r : Ranking} {a b : Fin 3} (h : Prefers r a b) : ¬ Prefers r b a := by
  simpa [Prefers] using h.le

lemma Prefers.ne {r : Ranking} {a b : Fin 3} (h : Prefers r a b) : a ≠ b := by
  rintro rfl; exact lt_irrefl _ h

lemma Prefers.trans {r : Ranking} {a b c : Fin 3}
    (h₁ : Prefers r a b) (h₂ : Prefers r b c) : Prefers r a c := lt_trans h₁ h₂

lemma prefers_total (r : Ranking) {a b : Fin 3} (hab : a ≠ b) :
    Prefers r a b ∨ Prefers r b a := by
  rcases lt_trichotomy (r.rank a) (r.rank b) with h | h | h
  · exact Or.inl h
  · exact absurd (r.rank_inj h) hab
  · exact Or.inr h

/-- Existence of a ranking realising a prescribed strict order `a ≻ b ≻ c`. -/
lemma exists_ranking {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ r : Ranking, Prefers r a b ∧ Prefers r b c := by
  have key : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      ∃ f : Fin 3 → Fin 3, Function.Injective f ∧ f x < f y ∧ f y < f z := by decide
  obtain ⟨f, hinj, h₁, h₂⟩ := key a b c hab hac hbc
  exact ⟨⟨f, hinj⟩, h₁, h₂⟩

/-- The third alternative. -/
lemma exists_third {a b : Fin 3} (hab : a ≠ b) : ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  revert hab; revert a b; decide

/-- `Decisive F i a b` : whenever voter `i` prefers `a` to `b` and the other voter disagrees,
society prefers `a` to `b`. -/
def Decisive (F : (Fin 2 → Ranking) → Ranking) (i : Fin 2) (a b : Fin 3) : Prop :=
  ∀ p : Fin 2 → Ranking, Prefers (p i) a b → Prefers (p (other i)) b a → Prefers (F p) a b

/-- Profile in which voter `i` has ranking `r` and the other voter has ranking `s`. -/
def mkProfile (i : Fin 2) (r s : Ranking) : Fin 2 → Ranking := fun j => if j = i then r else s

lemma mkProfile_self (i : Fin 2) (r s : Ranking) : mkProfile i r s i = r := by
  simp [mkProfile]

lemma mkProfile_other (i : Fin 2) (r s : Ranking) : mkProfile i r s (other i) = s := by
  simp [mkProfile, other_ne i]

/-- Given a pair on which the voters disagree, some voter is decisive on it. -/
lemma decisive_of_pair {F : (Fin 2 → Ranking) → Ranking} (hI : IIA F) {a b : Fin 3}
    (hab : a ≠ b) : Decisive F 0 a b ∨ Decisive F 1 b a := by
  obtain ⟨c, hac, hbc⟩ := exists_third hab
  obtain ⟨r₀, hr₀ab, hr₀bc⟩ := exists_ranking hab hac hbc
  obtain ⟨r₁, hr₁ba, hr₁ac⟩ := exists_ranking hab.symm hbc hac
  set p : Fin 2 → Ranking := mkProfile 0 r₀ r₁
  have hp0 : p 0 = r₀ := mkProfile_self 0 r₀ r₁
  have hp1 : p 1 = r₁ := by
    have := mkProfile_other 0 r₀ r₁
    simpa [other] using this
  rcases prefers_total (F p) hab with hF | hF
  · left
    intro q hq0 hq1
    have hq1' : Prefers (q 1) b a := by simpa [other] using hq1
    refine (hI p q a b ?_).mp hF
    intro i
    fin_cases i
    · exact iff_of_true hr₀ab hq0
    · exact iff_of_false hr₁ba.asymm hq1'.asymm
  · right
    intro q hq1 hq0
    have hq0' : Prefers (q 0) a b := by simpa [other] using hq0
    refine (hI p q b a ?_).mp hF
    intro i
    fin_cases i
    · exact iff_of_false hr₀ab.asymm hq0'.asymm
    · exact iff_of_true hr₁ba hq1

/-- Expansion: decisiveness on `(a,b)` gives decisiveness on `(a,c)`. -/
lemma decisive_right {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F)
    {i : Fin 2} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : Decisive F i a b) : Decisive F i a c := by
  -- voter `i` ranks `a ≻ b ≻ c`, the other voter ranks `b ≻ c ≻ a`
  obtain ⟨r, hrab, hrbc⟩ := exists_ranking hab hac hbc
  obtain ⟨s, hsbc, hsca⟩ := exists_ranking hbc hab.symm (Ne.symm hac)
  set p : Fin 2 → Ranking := mkProfile i r s
  have hpi : p i = r := mkProfile_self i r s
  have hpo : p (other i) = s := mkProfile_other i r s
  have hFab : Prefers (F p) a b := by
    refine h p ?_ ?_
    · rw [hpi]; exact hrab
    · rw [hpo]; exact hsbc.trans hsca
  have hFbc : Prefers (F p) b c := by
    refine hU p b c ?_
    intro j
    rcases eq_or_eq_other i j with rfl | rfl
    · rw [hpi]; exact hrbc
    · rw [hpo]; exact hsbc
  have hFac : Prefers (F p) a c := hFab.trans hFbc
  intro q hqi hqo
  refine (hI p q a c ?_).mp hFac
  intro j
  rcases eq_or_eq_other i j with rfl | rfl
  · rw [hpi]
    exact iff_of_true (hrab.trans hrbc) hqi
  · rw [hpo]
    exact iff_of_false hsca.asymm hqo.asymm

/-- Expansion: decisiveness on `(a,b)` gives decisiveness on `(c,b)`. -/
lemma decisive_left {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F)
    {i : Fin 2} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : Decisive F i a b) : Decisive F i c b := by
  -- voter `i` ranks `c ≻ a ≻ b`, the other voter ranks `b ≻ c ≻ a`
  obtain ⟨r, hrca, hrab⟩ := exists_ranking (Ne.symm hac) (Ne.symm hbc) hab
  obtain ⟨s, hsbc, hsca⟩ := exists_ranking hbc hab.symm (Ne.symm hac)
  set p : Fin 2 → Ranking := mkProfile i r s
  have hpi : p i = r := mkProfile_self i r s
  have hpo : p (other i) = s := mkProfile_other i r s
  have hFca : Prefers (F p) c a := by
    refine hU p c a ?_
    intro j
    rcases eq_or_eq_other i j with rfl | rfl
    · rw [hpi]; exact hrca
    · rw [hpo]; exact hsca
  have hFab : Prefers (F p) a b := by
    refine h p ?_ ?_
    · rw [hpi]; exact hrab
    · rw [hpo]; exact hsbc.trans hsca
  have hFcb : Prefers (F p) c b := hFca.trans hFab
  intro q hqi hqo
  refine (hI p q c b ?_).mp hFcb
  intro j
  rcases eq_or_eq_other i j with rfl | rfl
  · rw [hpi]
    exact iff_of_true (hrca.trans hrab) hqi
  · rw [hpo]
    exact iff_of_false hsbc.asymm hqo.asymm

/-- Decisiveness on one pair spreads to all pairs. -/
lemma decisive_all {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F)
    {i : Fin 2} {a b : Fin 3} (hab : a ≠ b) (h : Decisive F i a b) :
    ∀ x y : Fin 3, x ≠ y → Decisive F i x y := by
  obtain ⟨c, hac, hbc⟩ := exists_third hab
  have dac : Decisive F i a c := decisive_right hU hI hab hac hbc h
  have dcb : Decisive F i c b := decisive_left hU hI hab hac hbc h
  have dbc : Decisive F i b c := decisive_left hU hI hac hab (Ne.symm hbc) dac
  have dca : Decisive F i c a := decisive_right hU hI (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) dcb
  have dba : Decisive F i b a := decisive_right hU hI hbc (Ne.symm hab) (Ne.symm hac) dbc
  have hmem : ∀ z : Fin 3, z = a ∨ z = b ∨ z = c := by
    have key : ∀ x u v w : Fin 3, u ≠ v → u ≠ w → v ≠ w → (x = u ∨ x = v ∨ x = w) := by decide
    exact fun z => key z a b c hab hac hbc
  intro x y hxy
  rcases hmem x with hx | hx | hx <;> rcases hmem y with hy | hy | hy <;>
    subst hx <;> subst hy <;>
      first
        | exact absurd rfl hxy
        | assumption

/-- A voter decisive on every pair is a dictator. -/
lemma dictator_of_decisive_all {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F)
    {i : Fin 2} (h : ∀ x y : Fin 3, x ≠ y → Decisive F i x y) : IsDictator F i := by
  intro p x y hxy
  rcases prefers_total (p (other i)) hxy.ne with hother | hother
  · refine hU p x y ?_
    intro j
    rcases eq_or_eq_other i j with rfl | rfl
    · exact hxy
    · exact hother
  · exact h x y hxy.ne p hxy hother

/-- **Arrow's theorem** (base case: two voters, three alternatives): unanimity and IIA force
a dictator. -/
theorem arrow_dictator {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F) :
    ∃ d : Fin 2, IsDictator F d := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  rcases decisive_of_pair hI h01 with h | h
  · exact ⟨0, dictator_of_decisive_all hU (decisive_all hU hI h01 h)⟩
  · exact ⟨1, dictator_of_decisive_all hU (decisive_all hU hI (Ne.symm h01) h)⟩

/-- **Arrow's impossibility theorem** (base case: two voters, three alternatives).
No social welfare function on rankings of three alternatives is simultaneously unanimous,
independent of irrelevant alternatives, and non-dictatorial. -/
theorem arrow_impossibility :
    ¬ ∃ F : (Fin 2 → Ranking) → Ranking, Unanimous F ∧ IIA F ∧ ∀ d : Fin 2, ¬ IsDictator F d := by
  rintro ⟨F, hU, hI, hND⟩
  obtain ⟨d, hd⟩ := arrow_dictator hU hI
  exact hND d hd

/-- Sanity check: the hypotheses of the theorem are consistent — the dictatorial rule
"society copies voter 0" is unanimous and satisfies IIA (and, of course, has a dictator).
Hence `arrow_impossibility` is not vacuously true: it is exactly non-dictatorship that fails. -/
lemma dictatorship_spec :
    Unanimous (fun p : Fin 2 → Ranking => p 0) ∧ IIA (fun p : Fin 2 → Ranking => p 0) ∧
      IsDictator (fun p : Fin 2 → Ranking => p 0) 0 :=
  ⟨fun _ _ _ h => h 0, fun _ _ _ _ h => h 0, fun _ _ _ h => h⟩

end Frontier

