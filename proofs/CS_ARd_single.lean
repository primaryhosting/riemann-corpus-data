/-
Completeness of the algorithm: if `M` rejects `x`, the algorithm has an
accepting run.
-/
import RequestProject.Sound

namespace CS

open scoped Classical

namespace NMachine

variable {Γ : Type} (M : NMachine Γ) (x : List Γ)

/-- Reachability in the algorithm's transition system. -/
abbrev ARd (st st' : St M.Cfg) : Prop := Relation.ReflTransGen (M.IStepX x) st st'

lemma ARd_single {st st' : St M.Cfg} (h : M.IStep x[M.headPos st]? st st') : M.ARd x st st' :=
  Relation.ReflTransGen.single h

/-! ### Guessing paths -/

lemma reach_pIn (b p k rk i cnt : ℕ) :
    ∀ t, t ≤ k + 1 → ∀ c, M.RLx x b p t c →
      ∃ t' ≤ t, M.ARd x (.pIn b p k rk i cnt M.initCfg 0) (.pIn b p k rk i cnt c t') := by
  intro t
  induction t with
  | zero =>
      intro _ c hc
      rcases hc with rfl
      exact ⟨0, le_refl _, Relation.ReflTransGen.refl⟩
  | succ t ih =>
      intro ht c hc
      rcases hc with hc | ⟨d, hd, hstep⟩
      · obtain ⟨t', ht', hr⟩ := ih (by omega) c hc
        exact ⟨t', by omega, hr⟩
      · obtain ⟨t', ht', hr⟩ := ih (by omega) d hd
        exact ⟨t' + 1, by omega,
          hr.tail (IStep.pInStep (by omega) hstep.2.2 hstep.2.1)⟩

lemma reach_pOut (b p k rk i cnt j icnt : ℕ) :
    ∀ t, t ≤ k → ∀ c, M.RLx x b p t c →
      ∃ t' ≤ t, M.ARd x (.pOut b p k rk i cnt j icnt M.initCfg 0)
        (.pOut b p k rk i cnt j icnt c t') := by
  intro t
  induction t with
  | zero =>
      intro _ c hc
      rcases hc with rfl
      exact ⟨0, le_refl _, Relation.ReflTransGen.refl⟩
  | succ t ih =>
      intro ht c hc
      rcases hc with hc | ⟨d, hd, hstep⟩
      · obtain ⟨t', ht', hr⟩ := ih (by omega) c hc
        exact ⟨t', by omega, hr⟩
      · obtain ⟨t', ht', hr⟩ := ih (by omega) d hd
        exact ⟨t' + 1, by omega,
          hr.tail (IStep.pOutStep (by omega) hstep.2.2 hstep.2.1)⟩

lemma reach_pFin (b p rN i cnt : ℕ) {c : M.Cfg} (h : M.RRx x b p c) :
    M.ARd x (.pFin b p rN i cnt M.initCfg) (.pFin b p rN i cnt c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (IStep.pFinStep hstep.2.2 hstep.2.1)

lemma reach_viol (b p : ℕ) {c : M.Cfg} (h : M.RRx x b p c) :
    M.ARd x (.viol b p M.initCfg) (.viol b p c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (IStep.violStep hstep.2.2 hstep.2.1)

/-! ### The inner certification loop -/

lemma reach_inner (b p k rk i cnt : ℕ) (hi : i < (M.cfgList b p).length)
    (hrk : rk = M.cnts x b p k) (hnot : ¬ M.RLx x b p (k + 1) (M.cfgAt b p i)) :
    M.ARd x (.inner b p k rk i cnt 0 0) (.outer b p k rk (i + 1) cnt) := by
  have key : ∀ j, j ≤ (M.cfgList b p).length →
      M.ARd x (.inner b p k rk i cnt 0 0)
        (.inner b p k rk i cnt j (cntP (M.Sset x b p k i) ((M.cfgList b p).take j))) := by
    intro j
    induction j with
    | zero => intro _; simpa using Relation.ReflTransGen.refl
    | succ j ih =>
        intro hj
        have hj' : j < (M.cfgList b p).length := by omega
        have hprev := ih (by omega)
        rw [M.cntP_take_cfg _ hj']
        by_cases hS : M.Sset x b p k i (M.cfgAt b p j)
        · rw [if_pos hS]
          refine hprev.trans ((M.ARd_single x (IStep.innerCount hj')).trans ?_)
          obtain ⟨t', ht', hpath⟩ := M.reach_pOut x b p k rk i cnt j
            (cntP (M.Sset x b p k i) ((M.cfgList b p).take j)) k (le_refl k)
            (M.cfgAt b p j) hS.1
          exact hpath.tail (IStep.pOutDone hj' rfl hS.2.1 hS.2.2)
        · rw [if_neg hS, Nat.add_zero]
          exact hprev.tail (IStep.innerSkip hj')
  have hfinal := key (M.cfgList b p).length (le_refl _)
  rw [List.take_length] at hfinal
  have hSeq : cntP (M.Sset x b p k i) (M.cfgList b p) = rk := by
    rw [hrk]
    show cntP (M.Sset x b p k i) (M.cfgList b p) = cntP (M.RLx x b p k) (M.cfgList b p)
    refine cntP_congr fun c _ => ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩
    · rintro rfl
      exact hnot (RL_mono (Nat.le_succ k) h)
    · intro hstep
      exact hnot (Or.inr ⟨c, h, ⟨M.RLx_reg x h, M.Reg_cfgAt hi, hstep⟩⟩)
  rw [hSeq] at hfinal
  exact hfinal.tail (IStep.innerDone rfl)

/-! ### One round of the outer loop -/

lemma reach_round (b p k rk : ℕ) (hrk : rk = M.cnts x b p k) :
    ∀ i, i ≤ (M.cfgList b p).length →
      M.ARd x (.outer b p k rk 0 0)
        (.outer b p k rk i (cntP (M.RLx x b p (k + 1)) ((M.cfgList b p).take i))) := by
  intro i
  induction i with
  | zero => intro _; simpa using Relation.ReflTransGen.refl
  | succ i ih =>
      intro hi
      have hi' : i < (M.cfgList b p).length := by omega
      have hprev := ih (by omega)
      rw [M.cntP_take_cfg _ hi']
      by_cases hR : M.RLx x b p (k + 1) (M.cfgAt b p i)
      · rw [if_pos hR]
        refine hprev.trans ((M.ARd_single x (IStep.outerIn hi')).trans ?_)
        obtain ⟨t', ht', hpath⟩ := M.reach_pIn x b p k rk i
          (cntP (M.RLx x b p (k + 1)) ((M.cfgList b p).take i)) (k + 1) (le_refl _)
          (M.cfgAt b p i) hR
        exact hpath.tail (IStep.pInDone hi' rfl)
      · rw [if_neg hR, Nat.add_zero]
        refine hprev.trans ((M.ARd_single x (IStep.outerOut hi')).trans ?_)
        exact M.reach_inner x b p k rk i _ hi' hrk hR

lemma reach_round_full (b p k rk : ℕ) (hrk : rk = M.cnts x b p k) :
    M.ARd x (.outer b p k rk 0 0)
      (.outer b p k rk (M.cfgList b p).length (M.cnts x b p (k + 1))) := by
  have h := M.reach_round x b p k rk hrk (M.cfgList b p).length (le_refl _)
  rw [List.take_length] at h
  exact h

/-! ### Iterating the rounds until the count stabilises -/

lemma exists_stab (b p : ℕ) : ∃ k, M.cnts x b p k = M.cnts x b p (k + 1) := by
  by_contra hcon
  push_neg at hcon
  have hgrow : ∀ k, k ≤ M.cnts x b p k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have h1 := M.cnts_mono x b p k
        have h2 := hcon k
        omega
  have h1 := hgrow ((M.cfgList b p).length + 1)
  have h2 : M.cnts x b p ((M.cfgList b p).length + 1) ≤ (M.cfgList b p).length :=
    cntP_le_length _ _
  omega

lemma reach_fin (b p : ℕ) :
    ∃ rN, rN = cntP (M.RRx x b p) (M.cfgList b p) ∧
      M.ARd x (.outer b p 0 (M.cnt0 b p) 0 0) (.fin b p rN 0 0) := by
  have hex := M.exists_stab x b p
  have hspec : M.cnts x b p (Nat.find hex) = M.cnts x b p (Nat.find hex + 1) := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, M.cnts x b p k ≠ M.cnts x b p (k + 1) := fun k hk =>
    Nat.find_min hex hk
  have hchain : ∀ k ≤ Nat.find hex,
      M.ARd x (.outer b p 0 (M.cnt0 b p) 0 0) (.outer b p k (M.cnts x b p k) 0 0) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [← M.cnts_zero x b p]
    | succ k ih =>
        intro hk
        refine (ih (by omega)).trans ?_
        refine (M.reach_round_full x b p k (M.cnts x b p k) rfl).trans ?_
        exact M.ARd_single x (IStep.outerNext (fun hh => hmin k (by omega) hh.symm))
  refine ⟨M.cnts x b p (Nat.find hex), ?_, ?_⟩
  · exact (cntP_congr fun c _ => M.stabilised x hspec c).symm
  · refine (hchain (Nat.find hex) (le_refl _)).trans ?_
    refine (M.reach_round_full x b p (Nat.find hex) (M.cnts x b p (Nat.find hex)) rfl).trans ?_
    exact M.ARd_single x (IStep.outerFin hspec.symm)

/-! ### The final loop -/

lemma reach_acc_final (b p rN : ℕ) (hrN : rN = cntP (M.RRx x b p) (M.cfgList b p))
    (hclosed : ∀ c, M.RRx x b p c → ∀ c', M.Step x c c' → M.Reg b p c')
    (hnacc : ¬ M.Accepts x) :
    M.ARd x (.fin b p rN 0 0) St.acc := by
  have hGood : ∀ c, M.RRx x b p c → M.Good x b p c := by
    intro c hc
    exact ⟨hc, fun hq => hnacc ⟨c, M.RRx_le_Reach x hc, hq⟩, hclosed c hc⟩
  have key : ∀ i, i ≤ (M.cfgList b p).length →
      M.ARd x (.fin b p rN 0 0)
        (.fin b p rN i (cntP (M.Good x b p) ((M.cfgList b p).take i))) := by
    intro i
    induction i with
    | zero => intro _; simpa using Relation.ReflTransGen.refl
    | succ i ih =>
        intro hi
        have hi' : i < (M.cfgList b p).length := by omega
        have hprev := ih (by omega)
        rw [M.cntP_take_cfg _ hi']
        by_cases hG : M.Good x b p (M.cfgAt b p i)
        · rw [if_pos hG]
          refine hprev.trans ((M.ARd_single x (IStep.finCount hi')).trans ?_)
          exact (M.reach_pFin x b p rN i _ hG.1).tail
            (IStep.pFinDone hi' rfl hG.2.1 hG.2.2)
        · rw [if_neg hG, Nat.add_zero]
          exact hprev.tail (IStep.finSkip hi')
  have hfull := key (M.cfgList b p).length (le_refl _)
  rw [List.take_length] at hfull
  have hcnt : cntP (M.Good x b p) (M.cfgList b p) = rN := by
    rw [hrN]
    exact cntP_congr fun c _ => ⟨fun h => h.1, hGood c⟩
  rw [hcnt] at hfull
  exact hfull.tail (IStep.finAcc rfl)

/-! ### Completeness -/

/-- **Completeness**: if `M` rejects `x`, the algorithm has an accepting run. -/
theorem algo_complete (fb : ℕ)
    (hsb : ∀ c, M.Reach x c → c.2.1 ≤ x.length ∧ c.2.2.length ≤ fb)
    (hnacc : ¬ M.Accepts x) : M.ARd x M.initSt St.acc := by
  suffices H : ∀ N b p, (fb - b) + (x.length - p) ≤ N → b ≤ fb → p ≤ x.length →
      M.ARd x (.outer b p 0 (M.cnt0 b p) 0 0) St.acc from
    H ((fb - 0) + (x.length - 0)) 0 0 (le_refl _) (Nat.zero_le _) (Nat.zero_le _)
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b p hN hb hp
    by_cases hclosed : ∀ c, M.RRx x b p c → ∀ c', M.Step x c c' → M.Reg b p c'
    · obtain ⟨rN, hrN, hpath⟩ := M.reach_fin x b p
      exact hpath.trans (M.reach_acc_final x b p rN hrN hclosed hnacc)
    · push_neg at hclosed
      obtain ⟨c, hc, c', hstep, hreg⟩ := hclosed
      have hreach : M.Reach x c' := (M.RRx_le_Reach x hc).tail hstep
      have hbc := (hsb c' hreach).2
      have hpc := (hsb c' hreach).1
      have hregu : ¬ (c'.2.1 ≤ p ∧ c'.2.2.length ≤ b) := hreg
      have hviol : M.ARd x (.outer b p 0 (M.cnt0 b p) 0 0) (.viol b p c) :=
        (M.ARd_single x IStep.startViol).trans (M.reach_viol x b p hc)
      by_cases hm : b < c'.2.2.length
      · refine (hviol.trans (M.ARd_single x (IStep.violB hstep hm))).trans ?_
        exact ih (N - 1) (by omega) (b + 1) p (by omega) (by omega) hp
      · have hp2 : p < c'.2.1 := by
          by_contra hcon
          exact hregu ⟨by omega, by omega⟩
        refine (hviol.trans (M.ARd_single x (IStep.violP hstep hp2))).trans ?_
        exact ih (N - 1) (by omega) b (p + 1) (by omega) hb (by omega)

end NMachine

end CS

/-
Counting helpers and "reachability in at most `k` steps" layers.
These are the combinatorial ingredients of the inductive-counting argument.
-/
import Mathlib

namespace CS

open scoped Classical

/-! ### Counting occurrences of a (classical) predicate in a list -/

/-- Number of positions of `l` whose entry satisfies `P`. -/
noncomputable def cntP {α : Type*} (P : α → Prop) : List α → ℕ
  | [] => 0
  | a :: l => (if P a then 1 else 0) + cntP P l

variable {α : Type*}

@[simp] lemma cntP_nil (P : α → Prop) : cntP P [] = 0 := rfl

lemma cntP_cons (P : α → Prop) (a : α) (l : List α) :
    cntP P (a :: l) = (if P a then 1 else 0) + cntP P l := rfl

lemma cntP_le_length (P : α → Prop) (l : List α) : cntP P l ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [cntP_cons]
      simp only [List.length_cons]
      split <;> omega

lemma cntP_append (P : α → Prop) (l₁ l₂ : List α) :
    cntP P (l₁ ++ l₂) = cntP P l₁ + cntP P l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [cntP_cons, ih, Nat.add_assoc]

lemma cntP_mono {P Q : α → Prop} {l : List α} (h : ∀ a ∈ l, P a → Q a) :
    cntP P l ≤ cntP Q l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 : ∀ b ∈ l, P b → Q b := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have h2 := h a (List.mem_cons_self ..)
      have := ih h1
      rw [cntP_cons, cntP_cons]
      by_cases hp : P a
      · simp [hp, h2 hp]; omega
      · simp only [hp, if_false]
        split <;> omega

lemma cntP_congr {P Q : α → Prop} {l : List α} (h : ∀ a ∈ l, (P a ↔ Q a)) :
    cntP P l = cntP Q l :=
  le_antisymm (cntP_mono fun a ha hp => (h a ha).1 hp)
    (cntP_mono fun a ha hp => (h a ha).2 hp)

/-- If `P` implies `Q` on `l` and the two counts agree, then in fact `Q` implies `P` on `l`. -/
lemma cntP_forces {P Q : α → Prop} {l : List α} (himp : ∀ a ∈ l, P a → Q a)
    (heq : cntP P l = cntP Q l) : ∀ a ∈ l, Q a → P a := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 : ∀ b ∈ l, P b → Q b := fun b hb => himp b (List.mem_cons_of_mem _ hb)
      have hle := cntP_mono (P := P) (Q := Q) h1
      rw [cntP_cons, cntP_cons] at heq
      have hhead : (if P a then 1 else 0) = (if Q a then (1:ℕ) else 0) := by
        by_cases hp : P a
        · have := himp a (List.mem_cons_self ..) hp
          simp [hp, this]
        · by_cases hq : Q a
          · exfalso; simp only [hp, hq, if_true, if_false] at heq; omega
          · simp [hp, hq]
      have heq' : cntP P l = cntP Q l := by omega
      intro c hc hq
      rcases List.mem_cons.1 hc with rfl | hc'
      · by_contra hpc
        simp [hpc, hq] at hhead
      · exact ih h1 heq' c hc' hq

/-- Counting over an initial segment, one step at a time. -/
lemma cntP_take_succ {α : Type*} (P : α → Prop) (l : List α) (i : ℕ) (d : α)
    (h : i < l.length) :
    cntP P (l.take (i + 1)) = cntP P (l.take i) + (if P (l.getD i d) then 1 else 0) := by
  rw [List.take_add_one, cntP_append]
  congr 1
  have h1 : l[i]? = some l[i] := getElem?_pos l i h
  have h2 : l.getD i d = l[i] := List.getD_eq_getElem l d h
  simp [h1, cntP_cons]

lemma cntP_take_le_take_succ {α : Type*} (P : α → Prop) (l : List α) (i : ℕ) :
    cntP P (l.take i) ≤ cntP P (l.take (i + 1)) := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [cntP_take_succ P l i (l[i]'h) h]
    split <;> omega
  · rw [List.take_of_length_le h, List.take_of_length_le (by omega)]

lemma one_le_cntP {α : Type*} {P : α → Prop} {l : List α} {a : α} (ha : a ∈ l) (hp : P a) :
    1 ≤ cntP P l := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
      rcases List.mem_cons.1 ha with rfl | h
      · rw [cntP_cons]; simp [hp]
      · have := ih h
        rw [cntP_cons]; omega

end CS

/-
Soundness of the algorithm: the invariant is preserved by every transition, and
it says that the accepting state can only be reached when `M` rejects `x`.
-/
import RequestProject.Algo

namespace CS

open scoped Classical

namespace NMachine

variable {Γ : Type} (M : NMachine Γ) (x : List Γ)

lemma RLx_reg {b p k : ℕ} {c : M.Cfg} (h : M.RLx x b p k c) : M.Reg b p c :=
  RL_reg (M.Reg_init b p) h

lemma RRx_reg {b p : ℕ} {c : M.Cfg} (h : M.RRx x b p c) : M.Reg b p c :=
  RReach_reg (M.Reg_init b p) h

lemma RLx_mem {b p k : ℕ} {c : M.Cfg} (h : M.RLx x b p k c) : c ∈ M.cfgList b p :=
  M.mem_cfgList (M.RLx_reg x h)

lemma RRx_mem {b p : ℕ} {c : M.Cfg} (h : M.RRx x b p c) : c ∈ M.cfgList b p :=
  M.mem_cfgList (M.RRx_reg x h)

lemma RLx_mono {b p k m : ℕ} (hkm : k ≤ m) {c : M.Cfg} (h : M.RLx x b p k c) :
    M.RLx x b p m c := RL_mono hkm h

lemma RLx_le_RRx {b p k : ℕ} {c : M.Cfg} (h : M.RLx x b p k c) : M.RRx x b p c :=
  RL_le_RReach (M.Reg_init b p) h

lemma cnts_mono (b p k : ℕ) : M.cnts x b p k ≤ M.cnts x b p (k + 1) :=
  cntP_mono fun _ _ h => RL_mono (Nat.le_succ k) h

lemma cnts_zero (b p : ℕ) : M.cnts x b p 0 = M.cnt0 b p := rfl

lemma RRx_le_Reach {b p : ℕ} {c : M.Cfg} (h : M.RRx x b p c) : M.Reach x c := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.2.2

/-- If layer `k` has stabilised (as measured by the counts), it is exactly the set
of region-reachable configurations. -/
lemma stabilised {b p k : ℕ} (h : M.cnts x b p k = M.cnts x b p (k + 1)) (c : M.Cfg) :
    M.RRx x b p c ↔ M.RLx x b p k c := by
  have hforce : ∀ c ∈ M.cfgList b p, M.RLx x b p (k + 1) c → M.RLx x b p k c :=
    cntP_forces (fun c _ hc => RL_mono (Nat.le_succ k) hc) (by simpa [cnts] using h)
  have hall : ∀ c, M.RLx x b p (k + 1) c → M.RLx x b p k c := fun c hc =>
    hforce c (M.RLx_mem x hc) hc
  exact RReach_eq_RL (M.Reg_init b p) hall c


lemma cntP_take_cfg (P : M.Cfg → Prop) {b p i : ℕ} (hi : i < (M.cfgList b p).length) :
    cntP P ((M.cfgList b p).take (i + 1))
      = cntP P ((M.cfgList b p).take i) + (if P (M.cfgAt b p i) then 1 else 0) :=
  cntP_take_succ P _ i M.initCfg hi

/-- The invariant is preserved by every step of the algorithm. -/
theorem Inv_step {fb : ℕ}
    (hsb : ∀ c, M.Reach x c → c.2.1 ≤ x.length ∧ c.2.2.length ≤ fb)
    {a : Option Γ} {st st' : St M.Cfg} (hInv : M.Inv x fb st)
    (ha : a = x[M.headPos st]?) (h : M.IStep a st st') : M.Inv x fb st' := by
  cases h with
  | violStep hs hr =>
      rename_i b p cur cur'
      subst ha; simp only [headPos] at hs
      obtain ⟨h1, h2, h3⟩ := hInv
      exact ⟨h1, h2, h3.tail ⟨M.RRx_reg x h3, hr, hs⟩⟩
  | violB hs hb =>
      rename_i b p cur cur'
      subst ha; simp only [headPos] at hs
      obtain ⟨h1, h2, h3⟩ := hInv
      have hreach : M.Reach x cur' := (M.RRx_le_Reach x h3).tail hs
      have hb' := (hsb cur' hreach).2
      exact ⟨by omega, h2, M.one_le_cnt0 (b + 1) p, (M.cnts_zero x (b + 1) p).symm,
        Nat.zero_le _, by simp⟩
  | violP hs hp =>
      rename_i b p cur cur'
      subst ha; simp only [headPos] at hs
      obtain ⟨h1, h2, h3⟩ := hInv
      have hreach : M.Reach x cur' := (M.RRx_le_Reach x h3).tail hs
      have hp' := (hsb cur' hreach).1
      exact ⟨h1, by omega, M.one_le_cnt0 b (p + 1), (M.cnts_zero x b (p + 1)).symm,
        Nat.zero_le _, by simp⟩
  | startViol =>
      rename_i b p k rk i cnt
      obtain ⟨h1, h2, -, -, -, -⟩ := hInv
      exact ⟨h1, h2, Relation.ReflTransGen.refl⟩
  | outerIn hi =>
      rename_i b p k rk i cnt
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      exact ⟨h1, h2, h3, h4, hi, h6, Nat.zero_le _, rfl⟩
  | outerOut hi =>
      rename_i b p k rk i cnt
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      exact ⟨h1, h2, h3, h4, hi, h6, Nat.zero_le _, by simp⟩
  | outerNext hne =>
      rename_i b p k rk cnt
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      rw [List.take_length] at h6
      have hc : cnt = M.cnts x b p (k + 1) := h6
      have hmono := M.cnts_mono x b p k
      exact ⟨h1, h2, by omega, hc, Nat.zero_le _, by simp⟩
  | outerFin heq =>
      rename_i b p k rk cnt
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      rw [List.take_length] at h6
      have hstab : M.cnts x b p k = M.cnts x b p (k + 1) := by
        rw [← h4, ← heq]; exact h6
      refine ⟨h1, h2, ?_, Nat.zero_le _, by simp⟩
      have hcg : cntP (M.RRx x b p) (M.cfgList b p) = cntP (M.RLx x b p k) (M.cfgList b p) :=
        cntP_congr fun c _ => M.stabilised x hstab c
      rw [hcg]; exact h4
  | pInStep ht hs hr =>
      rename_i b p k rk i cnt cur cur' t
      subst ha; simp only [headPos] at hs
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, h6, by omega,
        Or.inr ⟨cur, h8, ⟨M.RLx_reg x h8, hr, hs⟩⟩⟩
  | pInDone hi hcur =>
      rename_i b p k rk i cnt cur t
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      have hR : M.RLx x b p (k + 1) (M.cfgAt b p i) := by
        rw [← hcur]; exact M.RLx_mono x h7 h8
      refine ⟨h1, h2, h3, h4, hi, ?_⟩
      rw [M.cntP_take_cfg _ hi, ← h6, if_pos hR]
  | innerSkip hj =>
      rename_i b p k rk i cnt j icnt
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, h6, hj, le_trans h8 (cntP_take_le_take_succ _ _ _)⟩
  | innerCount hj =>
      rename_i b p k rk i cnt j icnt
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, h6, hj, h8, Nat.zero_le _, rfl⟩
  | innerDone hic =>
      rename_i b p k rk i cnt icnt
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      rw [List.take_length] at h8
      have hSle : cntP (M.Sset x b p k i) (M.cfgList b p) ≤ M.cnts x b p k :=
        cntP_mono fun c _ hc => hc.1
      have hcnts : M.cnts x b p k = cntP (M.RLx x b p k) (M.cfgList b p) := rfl
      have heqS : cntP (M.Sset x b p k i) (M.cfgList b p)
          = cntP (M.RLx x b p k) (M.cfgList b p) := by omega
      have hforce := cntP_forces (fun c (_ : c ∈ M.cfgList b p)
        (hc : M.Sset x b p k i c) => hc.1) heqS
      have hall : ∀ c, M.RLx x b p k c → M.Sset x b p k i c := fun c hc =>
        hforce c (M.RLx_mem x hc) hc
      have hnot : ¬ M.RLx x b p (k + 1) (M.cfgAt b p i) := by
        rintro (hc | ⟨d, hd, hstep⟩)
        · exact (hall _ hc).2.1 rfl
        · exact (hall _ hd).2.2 hstep.2.2
      refine ⟨h1, h2, h3, h4, h5, ?_⟩
      rw [M.cntP_take_cfg _ h5, ← h6, if_neg hnot]
      omega
  | pOutStep ht hs hr =>
      rename_i b p k rk i cnt j icnt cur cur' t
      subst ha; simp only [headPos] at hs
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by omega,
        Or.inr ⟨cur, h10, ⟨M.RLx_reg x h10, hr, hs⟩⟩⟩
  | pOutDone hj hc1 hc2 hc3 =>
      rename_i b p k rk i cnt j icnt cur t
      subst ha; simp only [headPos] at hc3
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hInv
      have hS : M.Sset x b p k i cur := ⟨M.RLx_mono x h9 h10, hc2, hc3⟩
      refine ⟨h1, h2, h3, h4, h5, h6, hj, ?_⟩
      rw [M.cntP_take_cfg _ hj, if_pos (by rw [← hc1]; exact hS)]
      omega
  | finSkip hi =>
      rename_i b p rN i cnt
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      exact ⟨h1, h2, h3, hi, le_trans h5 (cntP_take_le_take_succ _ _ _)⟩
  | finCount hi =>
      rename_i b p rN i cnt
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      exact ⟨h1, h2, h3, hi, h5, Relation.ReflTransGen.refl⟩
  | finAcc hc =>
      rename_i b p rN cnt
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      rw [List.take_length] at h5
      have hle : cntP (M.Good x b p) (M.cfgList b p) ≤ cntP (M.RRx x b p) (M.cfgList b p) :=
        cntP_mono fun c _ hg => hg.1
      have heq : cntP (M.Good x b p) (M.cfgList b p)
          = cntP (M.RRx x b p) (M.cfgList b p) := by omega
      have hforce := cntP_forces (fun c (_ : c ∈ M.cfgList b p)
        (hg : M.Good x b p c) => hg.1) heq
      have hall : ∀ c, M.RRx x b p c → M.Good x b p c := fun c hc' =>
        hforce c (M.RRx_mem x hc') hc'
      have hclosed : ∀ c, M.Reach x c → M.RRx x b p c := by
        intro c hcr
        induction hcr with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hstep ih => exact ih.tail ⟨M.RRx_reg x ih, (hall _ ih).2.2 _ hstep, hstep⟩
      rintro ⟨c, hcr, hacc⟩
      exact (hall c (hclosed c hcr)).2.1 hacc
  | pFinStep hs hr =>
      rename_i b p rN i cnt cur cur'
      subst ha; simp only [headPos] at hs
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, h6.tail ⟨M.RRx_reg x h6, hr, hs⟩⟩
  | pFinDone hi hc1 hc2 hc3 =>
      rename_i b p rN i cnt cur
      subst ha; simp only [headPos] at hc3
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      have hG : M.Good x b p cur := ⟨h6, hc2, hc3⟩
      refine ⟨h1, h2, h3, hi, ?_⟩
      rw [M.cntP_take_cfg _ hi, if_pos (by rw [← hc1]; exact hG)]
      omega

/-- The invariant holds initially. -/
theorem Inv_initSt (fb : ℕ) : M.Inv x fb M.initSt :=
  ⟨Nat.zero_le _, Nat.zero_le _, M.one_le_cnt0 0 0, (M.cnts_zero x 0 0).symm,
    Nat.zero_le _, by simp⟩

/-- The invariant holds at every reachable algorithm state. -/
theorem Inv_reach {fb : ℕ}
    (hsb : ∀ c, M.Reach x c → c.2.1 ≤ x.length ∧ c.2.2.length ≤ fb)
    {st : St M.Cfg} (h : Relation.ReflTransGen (M.IStepX x) M.initSt st) : M.Inv x fb st := by
  induction h with
  | refl => exact M.Inv_initSt x fb
  | tail _ hstep ih => exact M.Inv_step x hsb ih rfl hstep

/-- **Soundness**: if the algorithm can accept, then `M` rejects `x`. -/
theorem algo_sound {fb : ℕ}
    (hsb : ∀ c, M.Reach x c → c.2.1 ≤ x.length ∧ c.2.2.length ≤ fb)
    (h : Relation.ReflTransGen (M.IStepX x) M.initSt (St.acc)) : ¬ M.Accepts x :=
  M.Inv_reach x hsb h

end NMachine

end CS

/-
The complement machine: a nondeterministic machine whose configurations are the
encoded states of the Immerman–Szelepcsényi algorithm.
-/
import RequestProject.Encoding
import RequestProject.Complete

namespace CS

open scoped Classical

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

/-- The complement machine of `M`. -/
noncomputable def compl : NMachine Γ where
  Q := Tag
  W := Alph M.Q M.W
  q₀ := Tag.start
  qacc := Tag.acc
  δ := fun q a m => {z |
    (q = Tag.start ∧ m = [] ∧
      z = (M.tagOf M.initSt, M.headPos M.initSt, M.encMem M.initSt)) ∨
    (∃ st st', M.tagOf st = q ∧ M.encMem st = m ∧ M.IStep a st st' ∧
      z = (M.tagOf st', M.headPos st', M.encMem st'))}

/-- The configuration of `compl` encoding an algorithm state. -/
noncomputable def encCfgSt (st : St M.Cfg) : M.compl.Cfg :=
  (M.tagOf st, M.headPos st, M.encMem st)

lemma tagOf_ne_start (st : St M.Cfg) : M.tagOf st ≠ Tag.start := by
  cases st <;> simp [tagOf]

lemma tagOf_eq_acc {st : St M.Cfg} (h : M.tagOf st = Tag.acc) : st = St.acc := by
  cases st <;> simp [tagOf] at h ⊢

lemma compl_initCfg : M.compl.initCfg = (Tag.start, 0, ([] : List (Alph M.Q M.W))) := rfl

lemma compl_step_iff (x : List Γ) (z z' : M.compl.Cfg) :
    M.compl.Step x z z' ↔
      ((z.1 = Tag.start ∧ z.2.2 = [] ∧ z' = M.encCfgSt M.initSt) ∨
        (∃ st st', M.tagOf st = z.1 ∧ M.encMem st = z.2.2 ∧
          M.IStep x[z.2.1]? st st' ∧ z' = M.encCfgSt st')) := Iff.rfl

/-- Reachable configurations of `compl` are exactly the initial configuration and
the encodings of reachable algorithm states. -/
lemma compl_reach_iff (x : List Γ) (z : M.compl.Cfg) :
    M.compl.Reach x z ↔
      (z = M.compl.initCfg ∨ ∃ st, M.ARd x M.initSt st ∧ z = M.encCfgSt st) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail hprev hstep ih =>
        rename_i z₁ z₂
        rcases ih with rfl | ⟨st, hst, rfl⟩
        · rcases (M.compl_step_iff x _ _).1 hstep with ⟨-, -, rfl⟩ | ⟨st, st', htag, -, -, -⟩
          · exact Or.inr ⟨M.initSt, Relation.ReflTransGen.refl, rfl⟩
          · exact absurd htag (M.tagOf_ne_start st)
        · rcases (M.compl_step_iff x _ _).1 hstep with ⟨htag, -, -⟩ | ⟨st₁, st', htag, hmem, hstep', rfl⟩
          · exact absurd htag (M.tagOf_ne_start st)
          · have : st₁ = st := M.enc_inj htag hmem
            subst this
            exact Or.inr ⟨st', hst.tail hstep', rfl⟩
  · rintro (rfl | ⟨st, hst, rfl⟩)
    · exact Relation.ReflTransGen.refl
    · have hbase : M.compl.Reach x (M.encCfgSt M.initSt) :=
        Relation.ReflTransGen.single ((M.compl_step_iff x _ _).2 (Or.inl ⟨rfl, rfl, rfl⟩))
      clear hbase
      induction hst with
      | refl =>
          exact Relation.ReflTransGen.single
            ((M.compl_step_iff x _ _).2 (Or.inl ⟨rfl, rfl, rfl⟩))
      | tail hprev hstep ih =>
          rename_i st₁ st₂
          exact ih.tail ((M.compl_step_iff x _ _).2 (Or.inr ⟨st₁, st₂, rfl, rfl, hstep, rfl⟩))

lemma compl_accepts_iff (x : List Γ) :
    M.compl.Accepts x ↔ M.ARd x M.initSt St.acc := by
  constructor
  · rintro ⟨z, hz, hacc⟩
    rcases (M.compl_reach_iff x z).1 hz with rfl | ⟨st, hst, rfl⟩
    · exact absurd (show (Tag.start : Tag) = Tag.acc from hacc) (by simp)
    · have : st = St.acc := M.tagOf_eq_acc hacc
      subst this; exact hst
  · intro h
    exact ⟨M.encCfgSt St.acc, (M.compl_reach_iff x _).2 (Or.inr ⟨St.acc, h, rfl⟩), rfl⟩

end NMachine

end CS

/-
Enumeration of all configurations of a machine inside a region
`{c | c.pos ≤ p ∧ c.mem.length ≤ b}`.

We do not need the enumeration to be duplicate-free; we only need it to contain
every configuration of the region, together with an upper bound on its length.
-/
import RequestProject.Model
import RequestProject.Layers

namespace CS

open scoped Classical

/-! ### A crude length bound for `flatMap` -/

lemma length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 : ∀ b ∈ l, (f b).length ≤ c := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have h2 := h a (List.mem_cons_self ..)
      have := ih h1
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      calc (f a).length + (l.flatMap f).length ≤ c + l.length * c := by omega
        _ = (l.length + 1) * c := by ring

/-! ### All words of a given length -/

/-- All lists over `W` of length exactly `n`. -/
noncomputable def allLen (W : Type) [Fintype W] : ℕ → List (List W)
  | 0 => [[]]
  | n + 1 => (Finset.univ : Finset W).toList.flatMap
      (fun w => (allLen W n).map (fun l => w :: l))

lemma mem_allLen {W : Type} [Fintype W] :
    ∀ (n : ℕ) (l : List W), l.length = n → l ∈ allLen W n := by
  intro n
  induction n with
  | zero => intro l hl; simp [allLen, List.length_eq_zero_iff.1 hl]
  | succ n ih =>
      intro l hl
      match l with
      | [] => simp at hl
      | w :: l' =>
          have : l'.length = n := by simpa using hl
          have h1 : l' ∈ allLen W n := ih l' this
          simp only [allLen, List.mem_flatMap]
          exact ⟨w, by simp, by simp only [List.mem_map]; exact ⟨l', h1, rfl⟩⟩

lemma length_allLen_le {W : Type} [Fintype W] (n : ℕ) :
    (allLen W n).length ≤ (Fintype.card W) ^ n := by
  induction n with
  | zero => simp [allLen]
  | succ n ih =>
      have : ((Finset.univ : Finset W).toList).length = Fintype.card W := by
        simp [Finset.length_toList]
      calc (allLen W (n + 1)).length
          ≤ ((Finset.univ : Finset W).toList).length * (Fintype.card W) ^ n := by
            refine length_flatMap_le _ _ _ ?_
            intro w _
            simpa using ih
        _ = (Fintype.card W) ^ (n + 1) := by rw [this]; ring

/-- All lists over `W` of length at most `b`. -/
noncomputable def memList (W : Type) [Fintype W] (b : ℕ) : List (List W) :=
  (List.range (b + 1)).flatMap (allLen W)

lemma mem_memList {W : Type} [Fintype W] {b : ℕ} {l : List W} (h : l.length ≤ b) :
    l ∈ memList W b := by
  simp only [memList, List.mem_flatMap]
  exact ⟨l.length, by simp; omega, mem_allLen _ _ rfl⟩

lemma length_memList_le {W : Type} [Fintype W] (b : ℕ) :
    (memList W b).length ≤ (b + 1) * (Fintype.card W + 1) ^ b := by
  have : ((List.range (b + 1)).flatMap (allLen W)).length
      ≤ (List.range (b + 1)).length * ((Fintype.card W + 1) ^ b) := by
    refine length_flatMap_le _ _ _ ?_
    intro k hk
    have hk' : k ≤ b := by simpa [Nat.lt_succ_iff] using hk
    calc (allLen W k).length ≤ (Fintype.card W) ^ k := length_allLen_le k
      _ ≤ (Fintype.card W + 1) ^ b := by
          exact Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ _) k)
            (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) hk')
  simpa [memList] using this

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

/-- The region of configurations with input pointer `≤ p` and memory length `≤ b`. -/
def Reg (b p : ℕ) (c : M.Cfg) : Prop := c.2.1 ≤ p ∧ c.2.2.length ≤ b

lemma Reg_init (b p : ℕ) : M.Reg b p M.initCfg := ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- An enumeration of the region `Reg b p`. -/
noncomputable def cfgList (b p : ℕ) : List M.Cfg :=
  ((Finset.univ : Finset M.Q).toList).flatMap fun q =>
    (List.range (p + 1)).flatMap fun i =>
      (memList M.W b).map fun m => (q, i, m)

lemma mem_cfgList {b p : ℕ} {c : M.Cfg} (h : M.Reg b p c) : c ∈ M.cfgList b p := by
  obtain ⟨q, i, m⟩ := c
  obtain ⟨h1, h2⟩ := h
  simp only [cfgList, List.mem_flatMap, List.mem_map]
  refine ⟨q, by simp, i, by simp; omega, m, mem_memList h2, rfl⟩

lemma length_cfgList_le (b p : ℕ) :
    (M.cfgList b p).length
      ≤ Fintype.card M.Q * ((p + 1) * ((b + 1) * (Fintype.card M.W + 1) ^ b)) := by
  have h1 : ∀ q : M.Q,
      ((List.range (p + 1)).flatMap fun i => (memList M.W b).map fun m => ((q, i, m) : M.Cfg)).length
        ≤ (p + 1) * ((b + 1) * (Fintype.card M.W + 1) ^ b) := by
    intro q
    have := length_flatMap_le (List.range (p + 1))
      (fun i => (memList M.W b).map fun m => ((q, i, m) : M.Cfg))
      ((b + 1) * (Fintype.card M.W + 1) ^ b)
      (by intro i _; simpa using length_memList_le (W := M.W) b)
    simpa using this
  have h2 := length_flatMap_le ((Finset.univ : Finset M.Q).toList)
      (fun q => (List.range (p + 1)).flatMap fun i => (memList M.W b).map fun m => ((q, i, m) : M.Cfg))
      ((p + 1) * ((b + 1) * (Fintype.card M.W + 1) ^ b)) (fun q _ => h1 q)
  rw [cfgList]
  simpa [Finset.length_toList] using h2

/-- The `i`-th configuration of the enumeration (with a default outside the range). -/
noncomputable def cfgAt (b p i : ℕ) : M.Cfg := (M.cfgList b p).getD i M.initCfg

end NMachine

lemma length_of_mem_allLen {W : Type} [Fintype W] :
    ∀ (n : ℕ) (l : List W), l ∈ allLen W n → l.length = n := by
  intro n
  induction n with
  | zero => intro l hl; simp [allLen] at hl; simp [hl]
  | succ n ih =>
      intro l hl
      simp only [allLen, List.mem_flatMap, List.mem_map] at hl
      obtain ⟨w, -, l', hl', rfl⟩ := hl
      simp [ih l' hl']

lemma length_le_of_mem_memList {W : Type} [Fintype W] {b : ℕ} {l : List W}
    (h : l ∈ memList W b) : l.length ≤ b := by
  simp only [memList, List.mem_flatMap, List.mem_range] at h
  obtain ⟨k, hk, hl⟩ := h
  rw [length_of_mem_allLen k l hl]
  omega

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

lemma cfgList_reg {b p : ℕ} {c : M.Cfg} (h : c ∈ M.cfgList b p) : M.Reg b p c := by
  simp only [cfgList, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨q, -, i, hi, m, hm, rfl⟩ := h
  exact ⟨by simpa using Nat.lt_succ_iff.1 hi, length_le_of_mem_memList hm⟩

lemma Reg_cfgAt {b p i : ℕ} (hi : i < (M.cfgList b p).length) : M.Reg b p (M.cfgAt b p i) := by
  have : M.cfgAt b p i = (M.cfgList b p)[i] := List.getD_eq_getElem _ _ hi
  rw [this]
  exact M.cfgList_reg (List.getElem_mem hi)

end NMachine

end CS

/-
Reachability layers inside a region: `RL reg stp init k` is the set of
configurations reachable from `init` in at most `k` steps, using only steps that
stay inside the region `reg`.
-/
import RequestProject.Count

namespace CS

open scoped Classical

variable {C : Type*}

/-- A step that stays inside the region. -/
def RStep (reg : C → Prop) (stp : C → C → Prop) (c c' : C) : Prop :=
  reg c ∧ reg c' ∧ stp c c'

/-- Configurations reachable from `init` within `k` region-steps. -/
def RL (reg : C → Prop) (stp : C → C → Prop) (init : C) : ℕ → C → Prop
  | 0 => fun c => c = init
  | k + 1 => fun c => RL reg stp init k c ∨ ∃ d, RL reg stp init k d ∧ RStep reg stp d c

variable {reg : C → Prop} {stp : C → C → Prop} {init : C}

@[simp] lemma RL_zero (c : C) : RL reg stp init 0 c ↔ c = init := Iff.rfl

lemma RL_succ (k : ℕ) (c : C) :
    RL reg stp init (k + 1) c ↔
      RL reg stp init k c ∨ ∃ d, RL reg stp init k d ∧ RStep reg stp d c := Iff.rfl

lemma RL_init (k : ℕ) : RL reg stp init k init := by
  induction k with
  | zero => rfl
  | succ k ih => exact Or.inl ih

lemma RL_mono_succ {k : ℕ} {c : C} (h : RL reg stp init k c) : RL reg stp init (k + 1) c :=
  Or.inl h

lemma RL_mono {k m : ℕ} (hkm : k ≤ m) {c : C} (h : RL reg stp init k c) :
    RL reg stp init m c := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact RL_mono_succ ih

lemma RL_reg (hinit : reg init) {k : ℕ} {c : C} (h : RL reg stp init k c) : reg c := by
  induction k generalizing c with
  | zero => rcases h with rfl; exact hinit
  | succ k ih =>
      rcases h with h | ⟨d, _, hd⟩
      · exact ih h
      · exact hd.2.1

/-- Membership in some layer is the same as region-reachability. -/
lemma RL_iff_reachable (hinit : reg init) (c : C) :
    (∃ k, RL reg stp init k c) ↔ Relation.ReflTransGen (RStep reg stp) init c := by
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing c with
    | zero => rcases hk with rfl; exact Relation.ReflTransGen.refl
    | succ k ih =>
        rcases hk with h | ⟨d, hd, hstep⟩
        · exact ih c h
        · exact (ih d hd).tail hstep
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hstep ih =>
        obtain ⟨k, hk⟩ := ih
        exact ⟨k + 1, Or.inr ⟨_, hk, hstep⟩⟩

/-- Region-reachability. -/
def RReach (reg : C → Prop) (stp : C → C → Prop) (init : C) (c : C) : Prop :=
  Relation.ReflTransGen (RStep reg stp) init c

lemma RL_le_RReach {k : ℕ} {c : C} (hinit : reg init) (h : RL reg stp init k c) :
    RReach reg stp init c := (RL_iff_reachable hinit c).1 ⟨k, h⟩

/-- Once a layer stops growing, it never grows again. -/
lemma RL_stab {k : ℕ} (h : ∀ c, RL reg stp init (k + 1) c → RL reg stp init k c) :
    ∀ m, k ≤ m → ∀ c, RL reg stp init m c → RL reg stp init k c := by
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base => exact fun c hc => hc
  | succ m _ ih =>
      intro c hc
      rcases (RL_succ m c).1 hc with hc' | ⟨d, hd, hstep⟩
      · exact ih c hc'
      · exact h c (Or.inr ⟨d, ih d hd, hstep⟩)

/-- If a layer has stabilised, it is exactly the set of region-reachable configurations. -/
lemma RReach_eq_RL (hinit : reg init) {k : ℕ}
    (h : ∀ c, RL reg stp init (k + 1) c → RL reg stp init k c) (c : C) :
    RReach reg stp init c ↔ RL reg stp init k c := by
  constructor
  · intro hc
    obtain ⟨m, hm⟩ := (RL_iff_reachable hinit c).2 hc
    exact RL_stab h (max k m) (le_max_left _ _) c (RL_mono (le_max_right _ _) hm)
  · intro hc; exact RL_le_RReach hinit hc

lemma RReach_reg (hinit : reg init) {c : C} (h : RReach reg stp init c) : reg c := by
  induction h with
  | refl => exact hinit
  | tail _ hstep _ => exact hstep.2.1

end CS

/-
The Immerman–Szelepcsényi algorithm, presented as a nondeterministic transition
system on an abstract state type `St`.

Given a nondeterministic machine `M` and an input `x`, the algorithm accepts iff
`M` does *not* accept `x`.  It uses only a constant number of counters bounded by
the number of configurations in the current region, plus one configuration.
-/
import RequestProject.CfgList

namespace CS

open scoped Classical

/-- States of the inductive-counting algorithm. -/
inductive St (C : Type) where
  /-- Searching for a configuration whose successor leaves the current region. -/
  | viol (b p : ℕ) (cur : C)
  /-- Outer loop: computing `|R (k+1)|`, having classified the first `i`
  configurations, `cnt` of which are in `R (k+1)`; `rk = |R k|`. -/
  | outer (b p k rk i cnt : ℕ)
  /-- Verifying that the `i`-th configuration lies in `R (k+1)`. -/
  | pIn (b p k rk i cnt : ℕ) (cur : C) (t : ℕ)
  /-- Inner loop: certifying that the `i`-th configuration is *not* in `R (k+1)`. -/
  | inner (b p k rk i cnt j icnt : ℕ)
  /-- Verifying that the `j`-th configuration lies in `R k`. -/
  | pOut (b p k rk i cnt j icnt : ℕ) (cur : C) (t : ℕ)
  /-- Final loop, with `rN` the number of region-reachable configurations. -/
  | fin (b p rN i cnt : ℕ)
  /-- Verifying that the `i`-th configuration is region-reachable. -/
  | pFin (b p rN i cnt : ℕ) (cur : C)
  /-- Accepting state. -/
  | acc
  deriving DecidableEq

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

/-- One step of `M` when the scanned input symbol is `a`. -/
def SuccA (a : Option Γ) (c c' : M.Cfg) : Prop := c' ∈ M.δ c.1 a c.2.2

lemma succA_eq_step (x : List Γ) (c c' : M.Cfg) :
    M.SuccA x[c.2.1]? c c' ↔ M.Step x c c' := Iff.rfl

/-- The number of positions of the enumeration holding the initial configuration. -/
noncomputable def cnt0 (b p : ℕ) : ℕ := cntP (fun c => c = M.initCfg) (M.cfgList b p)

lemma one_le_cnt0 (b p : ℕ) : 1 ≤ M.cnt0 b p :=
  one_le_cntP (M.mem_cfgList (M.Reg_init b p)) rfl

/-- The position of the input head in a given algorithm state. -/
def headPos : St M.Cfg → ℕ
  | .viol _ _ cur => cur.2.1
  | .pIn _ _ _ _ _ _ cur _ => cur.2.1
  | .pOut _ _ _ _ _ _ _ _ cur _ => cur.2.1
  | .pFin _ _ _ _ _ cur => cur.2.1
  | _ => 0

/-- The transition relation of the algorithm, when the scanned input symbol is `a`. -/
inductive IStep (a : Option Γ) : St M.Cfg → St M.Cfg → Prop
  | violStep {b p cur cur'} : M.SuccA a cur cur' → M.Reg b p cur' →
      IStep a (.viol b p cur) (.viol b p cur')
  | violB {b p cur cur'} : M.SuccA a cur cur' → b < cur'.2.2.length →
      IStep a (.viol b p cur) (.outer (b + 1) p 0 (M.cnt0 (b + 1) p) 0 0)
  | violP {b p cur cur'} : M.SuccA a cur cur' → p < cur'.2.1 →
      IStep a (.viol b p cur) (.outer b (p + 1) 0 (M.cnt0 b (p + 1)) 0 0)
  | startViol {b p k rk i cnt} :
      IStep a (.outer b p k rk i cnt) (.viol b p M.initCfg)
  | outerIn {b p k rk i cnt} : i < (M.cfgList b p).length →
      IStep a (.outer b p k rk i cnt) (.pIn b p k rk i cnt M.initCfg 0)
  | outerOut {b p k rk i cnt} : i < (M.cfgList b p).length →
      IStep a (.outer b p k rk i cnt) (.inner b p k rk i cnt 0 0)
  | outerNext {b p k rk cnt} : cnt ≠ rk →
      IStep a (.outer b p k rk (M.cfgList b p).length cnt) (.outer b p (k + 1) cnt 0 0)
  | outerFin {b p k rk cnt} : cnt = rk →
      IStep a (.outer b p k rk (M.cfgList b p).length cnt) (.fin b p rk 0 0)
  | pInStep {b p k rk i cnt cur cur' t} : t < k + 1 → M.SuccA a cur cur' → M.Reg b p cur' →
      IStep a (.pIn b p k rk i cnt cur t) (.pIn b p k rk i cnt cur' (t + 1))
  | pInDone {b p k rk i cnt cur t} : i < (M.cfgList b p).length → cur = M.cfgAt b p i →
      IStep a (.pIn b p k rk i cnt cur t) (.outer b p k rk (i + 1) (cnt + 1))
  | innerSkip {b p k rk i cnt j icnt} : j < (M.cfgList b p).length →
      IStep a (.inner b p k rk i cnt j icnt) (.inner b p k rk i cnt (j + 1) icnt)
  | innerCount {b p k rk i cnt j icnt} : j < (M.cfgList b p).length →
      IStep a (.inner b p k rk i cnt j icnt) (.pOut b p k rk i cnt j icnt M.initCfg 0)
  | innerDone {b p k rk i cnt icnt} : icnt = rk →
      IStep a (.inner b p k rk i cnt (M.cfgList b p).length icnt)
        (.outer b p k rk (i + 1) cnt)
  | pOutStep {b p k rk i cnt j icnt cur cur' t} : t < k → M.SuccA a cur cur' → M.Reg b p cur' →
      IStep a (.pOut b p k rk i cnt j icnt cur t) (.pOut b p k rk i cnt j icnt cur' (t + 1))
  | pOutDone {b p k rk i cnt j icnt cur t} : j < (M.cfgList b p).length →
      cur = M.cfgAt b p j → cur ≠ M.cfgAt b p i → ¬ M.SuccA a cur (M.cfgAt b p i) →
      IStep a (.pOut b p k rk i cnt j icnt cur t) (.inner b p k rk i cnt (j + 1) (icnt + 1))
  | finSkip {b p rN i cnt} : i < (M.cfgList b p).length →
      IStep a (.fin b p rN i cnt) (.fin b p rN (i + 1) cnt)
  | finCount {b p rN i cnt} : i < (M.cfgList b p).length →
      IStep a (.fin b p rN i cnt) (.pFin b p rN i cnt M.initCfg)
  | finAcc {b p rN cnt} : cnt = rN →
      IStep a (.fin b p rN (M.cfgList b p).length cnt) .acc
  | pFinStep {b p rN i cnt cur cur'} : M.SuccA a cur cur' → M.Reg b p cur' →
      IStep a (.pFin b p rN i cnt cur) (.pFin b p rN i cnt cur')
  | pFinDone {b p rN i cnt cur} : i < (M.cfgList b p).length → cur = M.cfgAt b p i →
      cur.1 ≠ M.qacc → (∀ cur', M.SuccA a cur cur' → M.Reg b p cur') →
      IStep a (.pFin b p rN i cnt cur) (.fin b p rN (i + 1) (cnt + 1))

/-- The algorithm's transition relation on input `x`: the scanned symbol is the
one at the current head position. -/
def IStepX (x : List Γ) (st st' : St M.Cfg) : Prop := M.IStep x[M.headPos st]? st st'

/-- The initial state of the algorithm. -/
noncomputable def initSt : St M.Cfg := .outer 0 0 0 (M.cnt0 0 0) 0 0

section Fixed

variable (x : List Γ)

/-- Reachability layers inside the region `(b,p)`. -/
def RLx (b p k : ℕ) : M.Cfg → Prop := RL (M.Reg b p) (M.Step x) M.initCfg k

/-- Region reachability. -/
def RRx (b p : ℕ) : M.Cfg → Prop := RReach (M.Reg b p) (M.Step x) M.initCfg

/-- The size of the `k`-th layer, as counted along the enumeration. -/
noncomputable def cnts (b p k : ℕ) : ℕ := cntP (M.RLx x b p k) (M.cfgList b p)

/-- Configurations certifying that the `i`-th configuration is not in `R (k+1)`. -/
def Sset (b p k i : ℕ) (d : M.Cfg) : Prop :=
  M.RLx x b p k d ∧ d ≠ M.cfgAt b p i ∧ ¬ M.Step x d (M.cfgAt b p i)

/-- Region-reachable, non-accepting configurations all of whose successors stay
in the region. -/
def Good (b p : ℕ) (c : M.Cfg) : Prop :=
  M.RRx x b p c ∧ c.1 ≠ M.qacc ∧ ∀ c', M.Step x c c' → M.Reg b p c'

/-- The invariant maintained by the algorithm.  `fb` is the memory bound of `M`
on inputs of length `x.length`. -/
def Inv (fb : ℕ) : St M.Cfg → Prop
  | .viol b p cur => b ≤ fb ∧ p ≤ x.length ∧ M.RRx x b p cur
  | .outer b p k rk i cnt =>
      b ≤ fb ∧ p ≤ x.length ∧ k < rk ∧ rk = M.cnts x b p k ∧
        i ≤ (M.cfgList b p).length ∧
        cnt = cntP (M.RLx x b p (k + 1)) ((M.cfgList b p).take i)
  | .pIn b p k rk i cnt cur t =>
      b ≤ fb ∧ p ≤ x.length ∧ k < rk ∧ rk = M.cnts x b p k ∧
        i < (M.cfgList b p).length ∧
        cnt = cntP (M.RLx x b p (k + 1)) ((M.cfgList b p).take i) ∧
        t ≤ k + 1 ∧ M.RLx x b p t cur
  | .inner b p k rk i cnt j icnt =>
      b ≤ fb ∧ p ≤ x.length ∧ k < rk ∧ rk = M.cnts x b p k ∧
        i < (M.cfgList b p).length ∧
        cnt = cntP (M.RLx x b p (k + 1)) ((M.cfgList b p).take i) ∧
        j ≤ (M.cfgList b p).length ∧
        icnt ≤ cntP (M.Sset x b p k i) ((M.cfgList b p).take j)
  | .pOut b p k rk i cnt j icnt cur t =>
      b ≤ fb ∧ p ≤ x.length ∧ k < rk ∧ rk = M.cnts x b p k ∧
        i < (M.cfgList b p).length ∧
        cnt = cntP (M.RLx x b p (k + 1)) ((M.cfgList b p).take i) ∧
        j < (M.cfgList b p).length ∧
        icnt ≤ cntP (M.Sset x b p k i) ((M.cfgList b p).take j) ∧
        t ≤ k ∧ M.RLx x b p t cur
  | .fin b p rN i cnt =>
      b ≤ fb ∧ p ≤ x.length ∧ rN = cntP (M.RRx x b p) (M.cfgList b p) ∧
        i ≤ (M.cfgList b p).length ∧ cnt ≤ cntP (M.Good x b p) ((M.cfgList b p).take i)
  | .pFin b p rN i cnt cur =>
      b ≤ fb ∧ p ≤ x.length ∧ rN = cntP (M.RRx x b p) (M.cfgList b p) ∧
        i < (M.cfgList b p).length ∧ cnt ≤ cntP (M.Good x b p) ((M.cfgList b p).take i) ∧
        M.RRx x b p cur
  | .acc => ¬ M.Accepts x

end Fixed

end NMachine

end CS

/-
# A model of nondeterministic space-bounded computation

We use the standard "offline machine" model: a nondeterministic machine has a
finite control, read-only random access to its input, and a read/write memory
tape holding a finite list of symbols.  The space bound restricts the length of
the memory tape (and requires the input pointer to stay inside the input).

The transition relation of a machine is an *arbitrary* set-valued function of
the current state, the currently scanned input symbol, and the current memory
contents.  No computability assumption is made; the only resource that is
restricted is memory.  This is the usual abstraction in which the
Immerman–Szelepcsényi theorem is proved.
-/
import Mathlib

namespace CS

/-- A nondeterministic machine over input alphabet `Γ`. -/
structure NMachine (Γ : Type) where
  /-- finite control -/
  Q : Type
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  /-- memory alphabet -/
  W : Type
  [fintypeW : Fintype W]
  [decEqW : DecidableEq W]
  /-- initial state -/
  q₀ : Q
  /-- accepting state -/
  qacc : Q
  /-- transition relation: from a state, the scanned input symbol and the memory
  contents, to a new state, a new input pointer and new memory contents. -/
  δ : Q → Option Γ → List W → Set (Q × ℕ × List W)

attribute [instance] NMachine.fintypeQ NMachine.decEqQ NMachine.fintypeW NMachine.decEqW

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

/-- A configuration: control state, input pointer, memory contents. -/
abbrev Cfg := M.Q × ℕ × List M.W

/-- The initial configuration. -/
def initCfg : M.Cfg := (M.q₀, 0, [])

/-- One computation step on input `x`. -/
def Step (x : List Γ) (c c' : M.Cfg) : Prop := c' ∈ M.δ c.1 x[c.2.1]? c.2.2

/-- `c` is reachable from the initial configuration on input `x`. -/
def Reach (x : List Γ) (c : M.Cfg) : Prop :=
  Relation.ReflTransGen (M.Step x) M.initCfg c

/-- The machine accepts `x` if some reachable configuration is accepting. -/
def Accepts (x : List Γ) : Prop := ∃ c, M.Reach x c ∧ c.1 = M.qacc

/-- The language of the machine. -/
def language : Language Γ := {x | M.Accepts x}

/-- The machine runs in space `f`: on every input, every reachable configuration
has its input pointer inside the input and its memory of length at most
`f (length of input)`. -/
def SpaceBounded (f : ℕ → ℕ) : Prop :=
  ∀ x : List Γ, ∀ c, M.Reach x c → c.2.1 ≤ x.length ∧ c.2.2.length ≤ f x.length

end NMachine

/-- `NSPACE s`: the languages recognised by a nondeterministic machine running in
space `O(s)`.  (As usual, space classes are defined up to a constant factor.) -/
def NSPACE (Γ : Type) (s : ℕ → ℕ) : Set (Language Γ) :=
  {L | ∃ (M : NMachine Γ) (c : ℕ), M.SpaceBounded (fun n => c * (s n + 1)) ∧ M.language = L}

/-- `coNSPACE s`: languages whose complement is in `NSPACE s`. -/
def coNSPACE (Γ : Type) (s : ℕ → ℕ) : Set (Language Γ) :=
  {L | Lᶜ ∈ NSPACE Γ s}

/-- The logarithmic space bound. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Nondeterministic logarithmic space. -/
def NL (Γ : Type) : Set (Language Γ) := NSPACE Γ logSpace

/-- The complement class of `NL`. -/
def coNL (Γ : Type) : Set (Language Γ) := coNSPACE Γ logSpace

theorem lt_two_pow_logSpace (n : ℕ) : n < 2 ^ logSpace n :=
  Nat.lt_pow_succ_log_self (by norm_num) n

end CS

/-
The space bound satisfied by the complement machine.
-/
import RequestProject.Compl

namespace CS

open scoped Classical


lemma length_take_le_length {α : Type*} (i : ℕ) (l : List α) : (l.take i).length ≤ l.length := by
  rw [List.length_take]; omega

namespace NMachine

variable {Γ : Type} (M : NMachine Γ) (x : List Γ)

/-- A crude bound on every counter used by the algorithm. -/
noncomputable def bnd (fb n : ℕ) : ℕ :=
  fb + n + Fintype.card M.Q * ((n + 1) * ((fb + 1) * (Fintype.card M.W + 1) ^ fb))

lemma le_bnd_fb (fb n : ℕ) : fb ≤ M.bnd fb n := by unfold bnd; omega

lemma le_bnd_n (fb n : ℕ) : n ≤ M.bnd fb n := by unfold bnd; omega

lemma cfgList_len_le_bnd {b p fb n : ℕ} (hb : b ≤ fb) (hp : p ≤ n) :
    (M.cfgList b p).length ≤ M.bnd fb n := by
  refine le_trans (M.length_cfgList_le b p) ?_
  have h1 : (Fintype.card M.W + 1) ^ b ≤ (Fintype.card M.W + 1) ^ fb :=
    Nat.pow_le_pow_right (by omega) hb
  have h2 : (b + 1) * (Fintype.card M.W + 1) ^ b ≤ (fb + 1) * (Fintype.card M.W + 1) ^ fb :=
    Nat.mul_le_mul (by omega) h1
  have h3 : (p + 1) * ((b + 1) * (Fintype.card M.W + 1) ^ b)
      ≤ (n + 1) * ((fb + 1) * (Fintype.card M.W + 1) ^ fb) := Nat.mul_le_mul (by omega) h2
  have h4 : Fintype.card M.Q * ((p + 1) * ((b + 1) * (Fintype.card M.W + 1) ^ b))
      ≤ Fintype.card M.Q * ((n + 1) * ((fb + 1) * (Fintype.card M.W + 1) ^ fb)) :=
    Nat.mul_le_mul_left _ h3
  unfold bnd
  omega

/-- All quantities stored by the algorithm are appropriately bounded. -/
lemma Inv_bounds {fb : ℕ} {st : St M.Cfg} (hInv : M.Inv x fb st) :
    M.headPos st ≤ x.length ∧ (M.curOf st).2.1 ≤ x.length ∧
      (M.curOf st).2.2.length ≤ fb ∧ ∀ v ∈ M.numsOf st, v ≤ M.bnd fb x.length := by
  have hfb := M.le_bnd_fb fb x.length
  have hn := M.le_bnd_n fb x.length
  cases st with
  | viol b p cur =>
      obtain ⟨h1, h2, h3⟩ := hInv
      obtain ⟨hr1, hr2⟩ := M.RRx_reg x h3
      refine ⟨by simp only [headPos]; omega, by simp only [curOf]; omega,
        by simp only [curOf]; omega, ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | outer b p k rk i cnt =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      have hL := M.cfgList_len_le_bnd h1 h2
      have hrk : rk ≤ (M.cfgList b p).length := by rw [h4]; exact cntP_le_length _ _
      have hcnt : cnt ≤ (M.cfgList b p).length := by
        rw [h6]
        exact le_trans (cntP_le_length _ _) (length_take_le_length _ _)
      refine ⟨by simp [headPos], by simp [curOf, initCfg], by simp [curOf, initCfg], ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | pIn b p k rk i cnt cur t =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      obtain ⟨hr1, hr2⟩ := M.RLx_reg x h8
      have hL := M.cfgList_len_le_bnd h1 h2
      have hrk : rk ≤ (M.cfgList b p).length := by rw [h4]; exact cntP_le_length _ _
      have hcnt : cnt ≤ (M.cfgList b p).length := by
        rw [h6]
        exact le_trans (cntP_le_length _ _) (length_take_le_length _ _)
      refine ⟨by simp only [headPos]; omega, by simp only [curOf]; omega,
        by simp only [curOf]; omega, ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | inner b p k rk i cnt j icnt =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hInv
      have hL := M.cfgList_len_le_bnd h1 h2
      have hrk : rk ≤ (M.cfgList b p).length := by rw [h4]; exact cntP_le_length _ _
      have hcnt : cnt ≤ (M.cfgList b p).length := by
        rw [h6]
        exact le_trans (cntP_le_length _ _) (length_take_le_length _ _)
      have hicnt : icnt ≤ (M.cfgList b p).length :=
        le_trans h8 (le_trans (cntP_le_length _ _) (length_take_le_length _ _))
      refine ⟨by simp [headPos], by simp [curOf, initCfg], by simp [curOf, initCfg], ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | pOut b p k rk i cnt j icnt cur t =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hInv
      obtain ⟨hr1, hr2⟩ := M.RLx_reg x h10
      have hL := M.cfgList_len_le_bnd h1 h2
      have hrk : rk ≤ (M.cfgList b p).length := by rw [h4]; exact cntP_le_length _ _
      have hcnt : cnt ≤ (M.cfgList b p).length := by
        rw [h6]
        exact le_trans (cntP_le_length _ _) (length_take_le_length _ _)
      have hicnt : icnt ≤ (M.cfgList b p).length :=
        le_trans h8 (le_trans (cntP_le_length _ _) (length_take_le_length _ _))
      refine ⟨by simp only [headPos]; omega, by simp only [curOf]; omega,
        by simp only [curOf]; omega, ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | fin b p rN i cnt =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      have hL := M.cfgList_len_le_bnd h1 h2
      have hrN : rN ≤ (M.cfgList b p).length := by rw [h3]; exact cntP_le_length _ _
      have hcnt : cnt ≤ (M.cfgList b p).length :=
        le_trans h5 (le_trans (cntP_le_length _ _) (length_take_le_length _ _))
      refine ⟨by simp [headPos], by simp [curOf, initCfg], by simp [curOf, initCfg], ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | pFin b p rN i cnt cur =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hInv
      obtain ⟨hr1, hr2⟩ := M.RRx_reg x h6
      have hL := M.cfgList_len_le_bnd h1 h2
      have hrN : rN ≤ (M.cfgList b p).length := by rw [h3]; exact cntP_le_length _ _
      have hcnt : cnt ≤ (M.cfgList b p).length :=
        le_trans h5 (le_trans (cntP_le_length _ _) (length_take_le_length _ _))
      refine ⟨by simp only [headPos]; omega, by simp only [curOf]; omega,
        by simp only [curOf]; omega, ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
  | acc =>
      refine ⟨by simp [headPos], by simp [curOf, initCfg], by simp [curOf, initCfg], ?_⟩
      intro v hv
      simp only [numsOf, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega

/-! ### Turning the counter bound into a bound on the encoding length -/

lemma bnd_le_pow (fb n sn : ℕ) (hn : n < 2 ^ sn) :
    M.bnd fb n ≤ 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 2) := by
  have hA : Fintype.card M.Q ≤ 2 ^ Fintype.card M.Q := le_of_lt Nat.lt_two_pow_self
  have hB : n + 1 ≤ 2 ^ sn := hn
  have hF : fb + 1 ≤ 2 ^ fb := Nat.lt_two_pow_self
  have hG : (Fintype.card M.W + 1) ^ fb ≤ 2 ^ ((Fintype.card M.W + 1) * fb) := by
    calc (Fintype.card M.W + 1) ^ fb
        ≤ (2 ^ (Fintype.card M.W + 1)) ^ fb :=
          Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) fb
      _ = 2 ^ ((Fintype.card M.W + 1) * fb) := by rw [← pow_mul]
  have hprod : Fintype.card M.Q * ((n + 1) * ((fb + 1) * (Fintype.card M.W + 1) ^ fb))
      ≤ 2 ^ Fintype.card M.Q * (2 ^ sn * (2 ^ fb * 2 ^ ((Fintype.card M.W + 1) * fb))) :=
    Nat.mul_le_mul hA (Nat.mul_le_mul hB (Nat.mul_le_mul hF hG))
  have hpow : 2 ^ Fintype.card M.Q * (2 ^ sn * (2 ^ fb * 2 ^ ((Fintype.card M.W + 1) * fb)))
      = 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    ring_nf
  rw [hpow] at hprod
  have hfb : fb < 2 ^ fb := Nat.lt_two_pow_self
  have hle1 : (2:ℕ) ^ fb ≤ 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle2 : (2:ℕ) ^ sn ≤ 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfinal : (2:ℕ) ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 2)
      = 4 * 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb) := by
    rw [pow_add]; ring
  rw [hfinal]
  unfold bnd
  omega

lemma encMem_length_le (fb sn : ℕ) (hn : x.length < 2 ^ sn) {st : St M.Cfg}
    (hInv : M.Inv x fb st) :
    (M.encMem st).length
      ≤ 9 * (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 4) + (2 + sn + fb) := by
  obtain ⟨hhp, hc1, hc2, hnums⟩ := M.Inv_bounds x hInv
  have hb := M.bnd_le_pow fb x.length sn hn
  have hD : ∀ v ∈ M.numsOf st,
      (Nat.digits 2 v).length
        ≤ Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 2 + 1 := by
    intro v hv
    rw [Nat.digits_length_le_iff (by norm_num)]
    have h1 : v ≤ 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 2) :=
      le_trans (hnums v hv) hb
    have h2 : (2:ℕ) ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 2)
        < 2 ^ (Fintype.card M.Q + sn + fb + (Fintype.card M.W + 1) * fb + 2 + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hDn : (Nat.digits 2 (M.curOf st).2.1).length ≤ sn := by
    rw [Nat.digits_length_le_iff (by norm_num)]
    omega
  have h := M.length_encMem_le st _ sn hD hDn
  omega

/-! ### The space bound of the complement machine -/

theorem compl_spaceBounded (c : ℕ) (s : ℕ → ℕ) (hs : ∀ n, n < 2 ^ s n)
    (hsb : M.SpaceBounded (fun n => c * (s n + 1))) :
    M.compl.SpaceBounded (fun n =>
      (9 * Fintype.card M.Q + 48 + 10 * c + 9 * (Fintype.card M.W + 1) * c) * (s n + 1)) := by
  intro y z hz
  rcases (M.compl_reach_iff y z).1 hz with rfl | ⟨st, hst, rfl⟩
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · have hInv : M.Inv y (c * (s y.length + 1)) st :=
      M.Inv_reach y (fun cc hcc => hsb y cc hcc) hst
    obtain ⟨hhp, -, -, -⟩ := M.Inv_bounds y hInv
    refine ⟨hhp, ?_⟩
    have hlen := M.encMem_length_le y (c * (s y.length + 1)) (s y.length) (hs y.length) hInv
    -- abbreviations
    set A := Fintype.card M.Q with hA
    set cw := Fintype.card M.W with hcw
    set sn := s y.length with hsn
    set S := sn + 1 with hS
    set fb := c * S with hfb
    have hSpos : 0 < S := by omega
    have e1 : 9 * A ≤ 9 * A * S := Nat.le_mul_of_pos_right _ hSpos
    have e2 : 10 * sn ≤ 10 * S := by omega
    have e3 : 10 * fb = 10 * c * S := by rw [hfb]; ring
    have e4 : 9 * ((cw + 1) * fb) = 9 * (cw + 1) * c * S := by rw [hfb]; ring
    have e5 : (38:ℕ) ≤ 38 * S := Nat.le_mul_of_pos_right _ hSpos
    have hexp : 9 * (A + sn + fb + (cw + 1) * fb + 4) + (2 + sn + fb)
        = 9 * A + 10 * sn + 10 * fb + 9 * ((cw + 1) * fb) + 38 := by ring
    have hgoal : (9 * A + 48 + 10 * c + 9 * (cw + 1) * c) * S
        = 9 * A * S + 10 * S + 10 * c * S + 9 * (cw + 1) * c * S + 38 * S := by ring
    rw [hexp] at hlen
    show (M.encMem st).length ≤ (9 * A + 48 + 10 * c + 9 * (cw + 1) * c) * S
    rw [hgoal]
    refine le_trans hlen ?_
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add e1 e2)
      (le_of_eq e3)) (le_of_eq e4)) e5

end NMachine

end CS

/-
Encoding of algorithm states into a finite control state plus a memory word over
a fixed finite alphabet, together with the length bound this encoding satisfies.
-/
import RequestProject.Algo

namespace CS

open scoped Classical

/-! ### Splitting at a separator -/

lemma sep_split {α : Type*} {s : α} :
    ∀ {l₁ l₂ r₁ r₂ : List α}, s ∉ l₁ → s ∉ l₂ →
      l₁ ++ s :: r₁ = l₂ ++ s :: r₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ r₁ r₂ _ h2 h
      match l₂ with
      | [] => simpa using h
      | a :: l₂' =>
          exfalso
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact h2 (by rw [← h.1]; exact List.mem_cons_self ..)
  | cons a l₁ ih =>
      intro l₂ r₁ r₂ h1 h2 h
      match l₂ with
      | [] =>
          exfalso
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact h1 (by rw [h.1]; exact List.mem_cons_self ..)
      | c :: l₂' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          obtain ⟨rfl, rfl⟩ := ih (fun hx => h1 (List.mem_cons_of_mem _ hx))
            (fun hx => h2 (List.mem_cons_of_mem _ hx)) h'
          exact ⟨rfl, rfl⟩

/-! ### The memory alphabet -/

/-- The memory alphabet of the complement machine: binary digits, control states
of `M`, memory symbols of `M`, and a separator (`none`). -/
abbrev Alph (Q W : Type) := Option (Bool ⊕ Q ⊕ W)

variable {Q W : Type}

/-- Binary encoding of a natural number. -/
def encN (v : ℕ) : List (Alph Q W) :=
  (Nat.digits 2 v).map (fun d => some (Sum.inl (decide (d = 1))))

/-- Reading a single digit back. -/
def decD (a : Alph Q W) : ℕ :=
  match a with
  | some (Sum.inl true) => 1
  | _ => 0

/-- Reading a natural number back. -/
def decN (l : List (Alph Q W)) : ℕ := Nat.ofDigits 2 (l.map (decD (Q := Q) (W := W)))

lemma decN_encN (v : ℕ) : decN (encN (Q := Q) (W := W) v) = v := by
  have h : (encN (Q := Q) (W := W) v).map (decD (Q := Q) (W := W)) = Nat.digits 2 v := by
    rw [encN, List.map_map]
    rw [show ((decD (Q := Q) (W := W)) ∘ fun d => some (Sum.inl (decide (d = 1))))
        = fun d => decD (Q := Q) (W := W) (some (Sum.inl (decide (d = 1)))) from rfl]
    rw [List.map_congr_left (g := id) ?_, List.map_id]
    intro d hd
    have hd2 : d < 2 := Nat.digits_lt_base (by norm_num) hd
    interval_cases d <;> simp [decD]
  rw [decN, h, Nat.ofDigits_digits]

lemma encN_inj {v w : ℕ} (h : encN (Q := Q) (W := W) v = encN (Q := Q) (W := W) w) : v = w := by
  have := congrArg (decN (Q := Q) (W := W)) h
  rwa [decN_encN, decN_encN] at this

lemma none_notMem_encN (v : ℕ) : (none : Alph Q W) ∉ encN (Q := Q) (W := W) v := by
  simp [encN]

lemma length_encN (v : ℕ) : (encN (Q := Q) (W := W) v).length = (Nat.digits 2 v).length := by
  simp [encN]

/-! ### Encoding configurations and tuples -/

/-- Encoding of a configuration of `M`. -/
def encCfg (c : Q × ℕ × List W) : List (Alph Q W) :=
  some (Sum.inr (Sum.inl c.1)) ::
    (encN c.2.1 ++ none :: c.2.2.map (fun w => some (Sum.inr (Sum.inr w))))

lemma encCfg_inj {c c' : Q × ℕ × List W} (h : encCfg c = encCfg c') : c = c' := by
  obtain ⟨q, i, m⟩ := c
  obtain ⟨q', i', m'⟩ := c'
  simp only [encCfg, List.cons.injEq, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  obtain ⟨he, hm⟩ := sep_split (none_notMem_encN (Q := Q) (W := W) i)
    (none_notMem_encN (Q := Q) (W := W) i') h2
  have hi : i = i' := encN_inj he
  have hmm : m = m' := by
    have : Function.Injective (fun w : W => (some (Sum.inr (Sum.inr w)) : Alph Q W)) := by
      intro a b hab; simpa using hab
    exact List.map_injective_iff.2 this hm
  subst hi; subst hmm; rfl

lemma length_encCfg (c : Q × ℕ × List W) :
    (encCfg c).length = 2 + (Nat.digits 2 c.2.1).length + c.2.2.length := by
  simp [encCfg, length_encN]
  omega

/-- Encoding of a list of numbers followed by a configuration. -/
def pack (ns : List ℕ) (c : Q × ℕ × List W) : List (Alph Q W) :=
  (ns.flatMap (fun v => encN v ++ [none])) ++ encCfg c

lemma pack_inj : ∀ {ns ns' : List ℕ} {c c' : Q × ℕ × List W},
    ns.length = ns'.length → pack ns c = pack ns' c' → ns = ns' ∧ c = c' := by
  intro ns
  induction ns with
  | nil =>
      intro ns' c c' hlen h
      match ns' with
      | [] => exact ⟨rfl, encCfg_inj (by simpa [pack] using h)⟩
      | _ :: _ => simp at hlen
  | cons v t ih =>
      intro ns' c c' hlen h
      match ns' with
      | [] => simp at hlen
      | v' :: t' =>
          simp only [pack, List.flatMap_cons, List.append_assoc, List.singleton_append] at h
          obtain ⟨he, hrest⟩ := sep_split (none_notMem_encN (Q := Q) (W := W) v)
            (none_notMem_encN (Q := Q) (W := W) v') h
          have hv : v = v' := encN_inj he
          have hlen' : t.length = t'.length := by simpa using hlen
          obtain ⟨ht, hc⟩ := ih hlen' (by simpa [pack] using hrest)
          exact ⟨by rw [hv, ht], hc⟩

lemma length_pack_le (ns : List ℕ) (c : Q × ℕ × List W) (D : ℕ)
    (hD : ∀ v ∈ ns, (Nat.digits 2 v).length ≤ D) :
    (pack ns c).length ≤ ns.length * (D + 1) + (2 + (Nat.digits 2 c.2.1).length + c.2.2.length) := by
  have h1 : (ns.flatMap (fun v => encN (Q := Q) (W := W) v ++ [none])).length
      ≤ ns.length * (D + 1) := by
    refine length_flatMap_le _ _ _ ?_
    intro v hv
    simp only [List.length_append, List.length_singleton, length_encN]
    have := hD v hv
    omega
  simp only [pack, List.length_append, length_encCfg]
  omega

/-! ### Encoding algorithm states -/

/-- Finite control states of the complement machine. -/
inductive Tag
  | start | viol | outer | pIn | inner | pOut | fin | pFin | acc
  deriving DecidableEq, Fintype

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

/-- The control state corresponding to an algorithm state. -/
def tagOf : St M.Cfg → Tag
  | .viol .. => .viol
  | .outer .. => .outer
  | .pIn .. => .pIn
  | .inner .. => .inner
  | .pOut .. => .pOut
  | .fin .. => .fin
  | .pFin .. => .pFin
  | .acc => .acc

/-- The nine counters of an algorithm state (unused slots are `0`). -/
def numsOf : St M.Cfg → List ℕ
  | .viol b p _ => [b, p, 0, 0, 0, 0, 0, 0, 0]
  | .outer b p k rk i cnt => [b, p, k, rk, i, cnt, 0, 0, 0]
  | .pIn b p k rk i cnt _ t => [b, p, k, rk, i, cnt, 0, 0, t]
  | .inner b p k rk i cnt j icnt => [b, p, k, rk, i, cnt, j, icnt, 0]
  | .pOut b p k rk i cnt j icnt _ t => [b, p, k, rk, i, cnt, j, icnt, t]
  | .fin b p rN i cnt => [b, p, 0, rN, i, cnt, 0, 0, 0]
  | .pFin b p rN i cnt _ => [b, p, 0, rN, i, cnt, 0, 0, 0]
  | .acc => [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The configuration stored in an algorithm state. -/
def curOf : St M.Cfg → M.Cfg
  | .viol _ _ cur => cur
  | .pIn _ _ _ _ _ _ cur _ => cur
  | .pOut _ _ _ _ _ _ _ _ cur _ => cur
  | .pFin _ _ _ _ _ cur => cur
  | _ => M.initCfg

lemma length_numsOf (st : St M.Cfg) : (M.numsOf st).length = 9 := by
  cases st <;> rfl

lemma headPos_eq (st : St M.Cfg) : M.headPos st = 0 ∨ M.headPos st = (M.curOf st).2.1 := by
  cases st <;> simp [headPos, curOf]

/-- The memory word encoding an algorithm state. -/
noncomputable def encMem (st : St M.Cfg) : List (Alph M.Q M.W) :=
  pack (M.numsOf st) (M.curOf st)

lemma enc_inj {st st' : St M.Cfg} (h1 : M.tagOf st = M.tagOf st')
    (h2 : M.encMem st = M.encMem st') : st = st' := by
  obtain ⟨hn, hc⟩ := pack_inj (by rw [M.length_numsOf, M.length_numsOf]) h2
  cases st <;> cases st' <;> simp_all [tagOf, numsOf, curOf]

lemma length_encMem_le (st : St M.Cfg) (D Dn : ℕ)
    (hnums : ∀ v ∈ M.numsOf st, (Nat.digits 2 v).length ≤ D)
    (hcur : (Nat.digits 2 (M.curOf st).2.1).length ≤ Dn) :
    (M.encMem st).length ≤ 9 * (D + 1) + (2 + Dn + (M.curOf st).2.2.length) := by
  have h := length_pack_le (M.numsOf st) (M.curOf st) D hnums
  rw [M.length_numsOf] at h
  rw [encMem]
  omega

end NMachine

end CS

/-
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is written as an ordinary block comment.)
import Mathlib
import RequestProject.Space

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

/-!
## The Immerman–Szelepcsényi theorem

`NL = coNL`: nondeterministic space is closed under complement.

Remarks on the formalisation.

* The machine model (`CS.NMachine`, in `RequestProject/Model.lean`) is the usual
  offline model: a finite control, read-only random access to the input, and a
  read/write memory tape holding a list of symbols.  Space is measured by the
  length of the memory tape; the transition relation is an arbitrary set-valued
  function of the state, the scanned input symbol and the memory contents, so no
  computability assumption is imposed — only memory is restricted.  This is the
  standard abstraction in which the inductive-counting argument takes place.
* As usual, space classes are closed under constant factors: `NSPACE s` consists
  of the languages accepted by a machine running in space `c * (s n + 1)` for
  some constant `c`.
* Because `δ` is unrestricted, the classes formalised here are the "oracle"
  variants of the usual ones; what is restricted, faithfully, is space.  The
  proof is not an abstract class manipulation: given `M`, the complement machine
  `CS.NMachine.compl M` is constructed explicitly from `M`, runs in the same
  space up to a constant factor, and accepts exactly the complement of `L(M)`.
* Mathlib contains no complexity theory, so the whole development (machine
  model, the inductive-counting algorithm, its soundness and completeness, and
  the space analysis of the constructed machine) is built from scratch here.
-/

namespace CS

namespace NMachine

variable {Γ : Type} (M : NMachine Γ)

/-- The complement machine accepts exactly the complement of `L(M)`. -/
theorem compl_language (c : ℕ) (s : ℕ → ℕ)
    (hsb : M.SpaceBounded (fun n => c * (s n + 1))) :
    M.compl.language = (M.language)ᶜ := by
  ext y
  simp only [language]
  constructor
  · intro h
    exact M.algo_sound y (fun cc hcc => hsb y cc hcc) ((M.compl_accepts_iff y).1 h)
  · intro h
    exact (M.compl_accepts_iff y).2
      (M.algo_complete y (c * (s y.length + 1)) (fun cc hcc => hsb y cc hcc) h)

end NMachine

/-- **Immerman–Szelepcsényi**, general form: for any space bound `s` that is at
least logarithmic, `NSPACE s` is closed under complementation. -/
theorem NSPACE_compl_mem {Γ : Type} (s : ℕ → ℕ) (hs : ∀ n, n < 2 ^ s n)
    {L : Language Γ} (hL : L ∈ NSPACE Γ s) : Lᶜ ∈ NSPACE Γ s := by
  obtain ⟨M, c, hsb, rfl⟩ := hL
  exact ⟨M.compl, _, M.compl_spaceBounded c s hs hsb, M.compl_language c s hsb⟩

/-- **Immerman–Szelepcsényi**, class form: `NSPACE s = coNSPACE s` for any space
bound `s` that is at least logarithmic. -/
theorem NSPACE_eq_coNSPACE {Γ : Type} (s : ℕ → ℕ) (hs : ∀ n, n < 2 ^ s n) :
    NSPACE Γ s = coNSPACE Γ s := by
  ext L
  constructor
  · intro hL
    exact NSPACE_compl_mem s hs hL
  · intro hL
    have h := NSPACE_compl_mem s hs hL
    rwa [compl_compl] at h

/-- **The Immerman–Szelepcsényi theorem**: `NL = coNL`, i.e. nondeterministic
logarithmic space is closed under complement. -/
theorem immerman_szelepcsenyi (Γ : Type) : NL Γ = coNL Γ :=
  NSPACE_eq_coNSPACE logSpace lt_two_pow_logSpace

end CS

