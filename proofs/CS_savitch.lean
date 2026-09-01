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

import RequestProject.Savitch.Machine

/-!
# Reduction to single-target reachability

`CS.addSink M` adds one new configuration (the *sink*) to `M`, with an edge from every
accepting configuration of `M` to the sink and no outgoing edge from the sink.  Then `M`
accepts iff the sink is reachable from the start configuration of `addSink M`, so that
deciding acceptance becomes deciding reachability between two *fixed* configurations.
-/

namespace CS

namespace Machine

/-- Add a sink configuration reachable exactly from the accepting configurations. -/
def addSink (M : Machine) : Machine where
  N := M.N + 1
  step x y :=
    if hx : x.val < M.N then
      (if hy : y.val < M.N then M.step ⟨x.val, hx⟩ ⟨y.val, hy⟩ else M.accept ⟨x.val, hx⟩)
    else false
  start := ⟨M.start.val, by omega⟩
  accept y := decide (y.val = M.N)

@[simp] theorem addSink_N (M : Machine) : (M.addSink).N = M.N + 1 := rfl

/-- The sink configuration. -/
def sink (M : Machine) : Fin (M.addSink).N := ⟨M.N, by simp⟩

theorem addSink_step_eq (M : Machine) (x y : Fin (M.addSink).N) :
    (M.addSink).step x y =
      if hx : x.val < M.N then
        (if hy : y.val < M.N then M.step ⟨x.val, hx⟩ ⟨y.val, hy⟩ else M.accept ⟨x.val, hx⟩)
      else false := rfl

theorem addSink_reaches_aux (M : Machine) (y : Fin (M.addSink).N)
    (h : (M.addSink).Reaches (M.addSink).start y) :
    (∃ hy : y.val < M.N, M.Reaches M.start ⟨y.val, hy⟩) ∨ (y.val = M.N ∧ M.Accepts) := by
  induction h with
  | refl =>
      exact Or.inl ⟨M.start.isLt, by simpa using Relation.ReflTransGen.refl⟩
  | @tail x y h hs ih =>
      rcases ih with ⟨hx, hrx⟩ | ⟨hx, hacc⟩
      · rw [addSink_step_eq] at hs
        rw [dif_pos hx] at hs
        by_cases hy : y.val < M.N
        · rw [dif_pos hy] at hs
          exact Or.inl ⟨hy, hrx.tail hs⟩
        · rw [dif_neg hy] at hs
          have hylt : y.val < M.N + 1 := by simpa using y.isLt
          refine Or.inr ⟨by omega, ⟨⟨x.val, hx⟩, hrx, hs⟩⟩
      · rw [addSink_step_eq] at hs
        rw [dif_neg (by omega)] at hs
        exact absurd hs (by simp)

/-- `M` accepts iff the sink of `M.addSink` is reachable from its start configuration. -/
theorem addSink_reaches_sink_iff (M : Machine) :
    (M.addSink).Reaches (M.addSink).start (M.sink) ↔ M.Accepts := by
  constructor
  · intro h
    rcases addSink_reaches_aux M _ h with ⟨hy, -⟩ | ⟨-, hacc⟩
    · exact absurd hy (by simp [sink])
    · exact hacc
  · rintro ⟨c, hc, hacc⟩
    have hmap : ∀ z : Fin M.N, M.Reaches M.start z →
        (M.addSink).Reaches (M.addSink).start ⟨z.val, by simp only [addSink_N]; omega⟩ := by
      intro z hz
      induction hz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail u v h hs ih =>
          refine ih.tail ?_
          rw [addSink_step_eq, dif_pos (show (u : ℕ) < M.N from u.isLt),
            dif_pos (show (v : ℕ) < M.N from v.isLt)]
          simpa using hs
    refine (hmap c hc).tail ?_
    rw [addSink_step_eq, dif_pos (show (c : ℕ) < M.N from c.isLt), dif_neg (by simp [sink])]
    simpa using hacc

end Machine

end CS

import Mathlib

/-!
# Configuration-graph machines and space classes

This file sets up the model of computation used for Savitch's theorem.

A `Machine` is the *configuration graph* of a space-bounded machine on a fixed input:
a finite set of configurations `Fin N`, a transition relation `step`, an initial
configuration `start`, and a set of accepting configurations `accept`.  The machine
accepts if some accepting configuration is reachable from `start`.  It is
*deterministic* when `step` is functional.

The space used is `log₂ N`: a machine running in space `s` (with `s ≥ log₂` of the
input length) has `2^{O(s)}` configurations, and conversely a configuration can be
stored in `log₂ N` bits.  Accordingly a language is in `DSPACE f` (resp. `NSPACE f`)
if it is decided by a family of (deterministic) configuration graphs with at most
`2 ^ f n` configurations on inputs of length `n`.
-/

namespace CS

/-- The configuration graph of a machine on a fixed input:
`N` configurations, a transition relation, a start configuration and accepting
configurations. -/
structure Machine where
  /-- Number of configurations. -/
  N : ℕ
  /-- The transition relation between configurations. -/
  step : Fin N → Fin N → Bool
  /-- The initial configuration. -/
  start : Fin N
  /-- The accepting configurations. -/
  accept : Fin N → Bool

namespace Machine

/-- Reachability in the configuration graph. -/
def Reaches (M : Machine) (a b : Fin M.N) : Prop :=
  Relation.ReflTransGen (fun x y => M.step x y = true) a b

/-- A machine accepts if some accepting configuration is reachable from the start. -/
def Accepts (M : Machine) : Prop := ∃ c, M.Reaches M.start c ∧ M.accept c = true

/-- A machine is deterministic if its transition relation is functional. -/
def Det (M : Machine) : Prop := ∀ a b c, M.step a b = true → M.step a c = true → b = c

theorem Reaches.refl (M : Machine) (a : Fin M.N) : M.Reaches a a := Relation.ReflTransGen.refl

theorem Reaches.tail {M : Machine} {a b c : Fin M.N} (h : M.Reaches a b)
    (hs : M.step b c = true) : M.Reaches a c := Relation.ReflTransGen.tail h hs

/-! ### Building a machine from an arbitrary finite state space -/

/-- The deterministic machine on a finite state space `S` given by the transition
function `f`, initial state `init` and accepting states `acc`. -/
noncomputable def ofFn {S : Type} [Fintype S] [DecidableEq S] (f : S → S) (init : S)
    (acc : S → Bool) : Machine where
  N := Fintype.card S
  step x y := decide ((Fintype.equivFin S) (f ((Fintype.equivFin S).symm x)) = y)
  start := Fintype.equivFin S init
  accept x := acc ((Fintype.equivFin S).symm x)

@[simp] theorem ofFn_N {S : Type} [Fintype S] [DecidableEq S] (f : S → S) (init : S)
    (acc : S → Bool) : (ofFn f init acc).N = Fintype.card S := rfl

theorem ofFn_det {S : Type} [Fintype S] [DecidableEq S] (f : S → S) (init : S)
    (acc : S → Bool) : (ofFn f init acc).Det := by
  intro a b c hb hc
  simp only [ofFn, decide_eq_true_eq] at hb hc
  exact hb ▸ hc ▸ rfl

theorem ofFn_reaches_iff {S : Type} [Fintype S] [DecidableEq S] (f : S → S) (init : S)
    (acc : S → Bool) (c : Fin (ofFn f init acc).N) :
    (ofFn f init acc).Reaches (ofFn f init acc).start c ↔
      ∃ t, (Fintype.equivFin S) (f^[t] init) = c := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail h hs ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨t + 1, ?_⟩
        simp only [ofFn, decide_eq_true_eq] at hs
        rw [Function.iterate_succ_apply']
        rw [← hs, ← ht, Equiv.symm_apply_apply]
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih =>
        refine Relation.ReflTransGen.tail ih ?_
        simp only [ofFn, decide_eq_true_eq, Equiv.symm_apply_apply]
        rw [Function.iterate_succ_apply']

theorem ofFn_accepts_iff {S : Type} [Fintype S] [DecidableEq S] (f : S → S) (init : S)
    (acc : S → Bool) : (ofFn f init acc).Accepts ↔ ∃ t, acc (f^[t] init) = true := by
  constructor
  · rintro ⟨c, hc, hacc⟩
    obtain ⟨t, ht⟩ := (ofFn_reaches_iff f init acc c).1 hc
    refine ⟨t, ?_⟩
    simpa [ofFn, ← ht] using hacc
  · rintro ⟨t, ht⟩
    refine ⟨(Fintype.equivFin S) (f^[t] init), (ofFn_reaches_iff f init acc _).2 ⟨t, rfl⟩, ?_⟩
    simpa [ofFn] using ht

end Machine

/-! ### Space classes -/

/-- `L ∈ NSPACE f`: `L` is decided by a family of configuration graphs with at most
`2 ^ f n` configurations on inputs of length `n`. -/
def NSPACE (f : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ M : List Bool → Machine, (∀ x, (M x).N ≤ 2 ^ f x.length) ∧ ∀ x, (L x ↔ (M x).Accepts)

/-- `L ∈ DSPACE f`: `L` is decided by a family of *deterministic* configuration graphs
with at most `2 ^ f n` configurations on inputs of length `n`. -/
def DSPACE (f : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ M : List Bool → Machine, (∀ x, (M x).Det) ∧ (∀ x, (M x).N ≤ 2 ^ f x.length) ∧
    ∀ x, (L x ↔ (M x).Accepts)

theorem DSPACE.mono {f g : ℕ → ℕ} {L : List Bool → Prop} (h : DSPACE f L)
    (hfg : ∀ n, f n ≤ g n) : DSPACE g L := by
  obtain ⟨M, hdet, hcard, hL⟩ := h
  exact ⟨M, hdet, fun x => (hcard x).trans (Nat.pow_le_pow_right (by norm_num) (hfg _)), hL⟩

theorem NSPACE.mono {f g : ℕ → ℕ} {L : List Bool → Prop} (h : NSPACE f L)
    (hfg : ∀ n, f n ≤ g n) : NSPACE g L := by
  obtain ⟨M, hcard, hL⟩ := h
  exact ⟨M, fun x => (hcard x).trans (Nat.pow_le_pow_right (by norm_num) (hfg _)), hL⟩

theorem DSPACE.toNSPACE {f : ℕ → ℕ} {L : List Bool → Prop} (h : DSPACE f L) : NSPACE f L := by
  obtain ⟨M, _, hcard, hL⟩ := h
  exact ⟨M, hcard, hL⟩

end CS

import RequestProject.Savitch.Machine

/-!
# Bounded reachability and the Savitch recursion

`CS.W M n a b` says that `b` is reachable from `a` by a walk of at most `n` steps.

`CS.Reach M k a b` is the *Savitch recursion*: it is true iff `b` is reachable from `a`
in at most `2 ^ k` steps.  It is defined by
`Reach (k+1) a b = ∃ m, Reach k a m ∧ Reach k m b`, where the middle configuration is
searched for by the explicit loop `CS.midFrom`, which is the loop that the deterministic
simulator of `RequestProject/Savitch/Stack.lean` runs.

The main result of this file is `CS.Reach_eq_true_iff_reaches`: if `M.N ≤ 2 ^ K` then
`Reach M K a b` decides reachability in the configuration graph.
-/

namespace CS

variable {M : Machine}

/-! ### The middle-configuration loop -/

/-- `midFrom R a b i` searches the configurations of index `≥ i` for a middle
configuration `m` with `R a m` and `R m b`. -/
def midFrom {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (i : ℕ) : Bool :=
  if h : i < n then (R a ⟨i, h⟩ && R ⟨i, h⟩ b) || midFrom R a b (i + 1) else false
termination_by n - i

theorem midFrom_of_lt {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) {i : ℕ} (h : i < n) :
    midFrom R a b i = ((R a ⟨i, h⟩ && R ⟨i, h⟩ b) || midFrom R a b (i + 1)) := by
  rw [midFrom]
  simp [h]

theorem midFrom_of_ge {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) {i : ℕ} (h : ¬ i < n) :
    midFrom R a b i = false := by
  rw [midFrom]
  simp [h]

theorem midFrom_eq_true_iff_aux {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (j : ℕ) :
    ∀ i, n ≤ i + j →
      (midFrom R a b i = true ↔ ∃ m : Fin n, i ≤ m.val ∧ R a m = true ∧ R m b = true) := by
  induction j with
  | zero =>
      intro i hi
      rw [midFrom_of_ge R a b (by omega)]
      simp only [false_iff, Bool.false_eq_true, not_exists]
      rintro m ⟨hm, -, -⟩
      omega
  | succ j ih =>
      intro i hi
      by_cases h : i < n
      · rw [midFrom_of_lt R a b h, Bool.or_eq_true_iff, ih (i + 1) (by omega)]
        constructor
        · rintro (hb | ⟨m, hm, h1, h2⟩)
          · exact ⟨⟨i, h⟩, le_rfl, (Bool.and_eq_true_iff.1 hb).1, (Bool.and_eq_true_iff.1 hb).2⟩
          · exact ⟨m, by omega, h1, h2⟩
        · rintro ⟨m, hm, h1, h2⟩
          rcases Nat.eq_or_lt_of_le hm with hm' | hm'
          · refine Or.inl ?_
            have : (⟨i, h⟩ : Fin n) = m := Fin.ext hm'
            rw [this]
            simp [h1, h2]
          · exact Or.inr ⟨m, by omega, h1, h2⟩
      · rw [midFrom_of_ge R a b h]
        simp only [false_iff, Bool.false_eq_true, not_exists]
        rintro m ⟨hm, -, -⟩
        omega

theorem midFrom_eq_true_iff {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (i : ℕ) :
    midFrom R a b i = true ↔ ∃ m : Fin n, i ≤ m.val ∧ R a m = true ∧ R m b = true :=
  midFrom_eq_true_iff_aux R a b n i (by omega)

/-! ### The Savitch recursion -/

/-- The Savitch recursion: `Reach M k a b` is true iff `b` can be reached from `a` in at
most `2 ^ k` steps. -/
def Reach (M : Machine) : ℕ → Fin M.N → Fin M.N → Bool
  | 0, a, b => decide (a = b) || M.step a b
  | (k + 1), a, b => midFrom (Reach M k) a b 0

theorem Reach_zero (a b : Fin M.N) : Reach M 0 a b = (decide (a = b) || M.step a b) := rfl

theorem Reach_succ_iff (k : ℕ) (a b : Fin M.N) :
    Reach M (k + 1) a b = true ↔ ∃ m, Reach M k a m = true ∧ Reach M k m b = true := by
  show midFrom (Reach M k) a b 0 = true ↔ _
  rw [midFrom_eq_true_iff]
  constructor
  · rintro ⟨m, -, h1, h2⟩; exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩; exact ⟨m, Nat.zero_le _, h1, h2⟩

theorem Reach_refl (k : ℕ) (a : Fin M.N) : Reach M k a a = true := by
  induction k with
  | zero => simp [Reach_zero]
  | succ k ih => exact (Reach_succ_iff k a a).2 ⟨a, ih, ih⟩

theorem Reach_mono {k : ℕ} {a b : Fin M.N} (h : Reach M k a b = true) :
    Reach M (k + 1) a b = true :=
  (Reach_succ_iff k a b).2 ⟨b, h, Reach_refl k b⟩

theorem Reach_mono' {k l : ℕ} {a b : Fin M.N} (hkl : k ≤ l) (h : Reach M k a b = true) :
    Reach M l a b = true := by
  induction l with
  | zero =>
      have : k = 0 := by omega
      exact this ▸ h
  | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with h' | h'
      · exact Reach_mono (ih (by omega))
      · have : k = l + 1 := by omega
        exact this ▸ h

theorem Reach_sound {k : ℕ} {a b : Fin M.N} (h : Reach M k a b = true) : M.Reaches a b := by
  induction k generalizing a b with
  | zero =>
      rw [Reach_zero] at h
      rcases Bool.or_eq_true_iff.1 h with h | h
      · exact (of_decide_eq_true h) ▸ Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h
  | succ k ih =>
      obtain ⟨m, h1, h2⟩ := (Reach_succ_iff k a b).1 h
      exact (ih h1).trans (ih h2)

/-! ### Walks -/

/-- `W M n a b` : there is a walk of at most `n` steps from `a` to `b`. -/
def W (M : Machine) : ℕ → Fin M.N → Fin M.N → Bool
  | 0, a, b => decide (a = b)
  | (n + 1), a, b => decide (a = b) || decide (∃ c, M.step a c = true ∧ W M n c b = true)

theorem W_zero (a b : Fin M.N) : W M 0 a b = decide (a = b) := rfl

theorem W_succ_iff (n : ℕ) (a b : Fin M.N) :
    W M (n + 1) a b = true ↔ a = b ∨ ∃ c, M.step a c = true ∧ W M n c b = true := by
  show (decide (a = b) || decide (∃ c, M.step a c = true ∧ W M n c b = true)) = true ↔ _
  simp

theorem W_refl (n : ℕ) (a : Fin M.N) : W M n a a = true := by
  cases n with
  | zero => simp [W_zero]
  | succ n => exact (W_succ_iff n a a).2 (Or.inl rfl)

theorem W_mono {n : ℕ} {a b : Fin M.N} (h : W M n a b = true) : W M (n + 1) a b = true := by
  induction n generalizing a with
  | zero =>
      rw [W_zero] at h
      exact (W_succ_iff 0 a b).2 (Or.inl (of_decide_eq_true h))
  | succ n ih =>
      rcases (W_succ_iff n a b).1 h with h | ⟨c, hc, hw⟩
      · exact (W_succ_iff (n + 1) a b).2 (Or.inl h)
      · exact (W_succ_iff (n + 1) a b).2 (Or.inr ⟨c, hc, ih hw⟩)

theorem W_le {n m : ℕ} {a b : Fin M.N} (hnm : n ≤ m) (h : W M n a b = true) :
    W M m a b = true := by
  induction m with
  | zero =>
      have : n = 0 := by omega
      exact this ▸ h
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · exact W_mono (ih (by omega))
      · have : n = m + 1 := by omega
        exact this ▸ h

theorem W_split {p q : ℕ} {a b : Fin M.N} (h : W M (p + q) a b = true) :
    ∃ c, W M p a c = true ∧ W M q c b = true := by
  induction p generalizing a with
  | zero => exact ⟨a, W_refl 0 a, by simpa using h⟩
  | succ p ih =>
      have h' : W M ((p + q) + 1) a b = true := by
        have : p + 1 + q = (p + q) + 1 := by omega
        rwa [this] at h
      rcases (W_succ_iff (p + q) a b).1 h' with rfl | ⟨c, hc, hw⟩
      · exact ⟨a, W_refl _ a, W_refl _ a⟩
      · obtain ⟨d, hd1, hd2⟩ := ih hw
        exact ⟨d, (W_succ_iff p a d).2 (Or.inr ⟨c, hc, hd1⟩), hd2⟩

theorem W_snoc {n : ℕ} {a c b : Fin M.N} (h : W M n a c = true) (hs : M.step c b = true) :
    W M (n + 1) a b = true := by
  induction n generalizing a with
  | zero =>
      rw [W_zero] at h
      have : a = c := of_decide_eq_true h
      subst this
      exact (W_succ_iff 0 a b).2 (Or.inr ⟨b, hs, W_refl 0 b⟩)
  | succ n ih =>
      rcases (W_succ_iff n a c).1 h with rfl | ⟨d, hd, hw⟩
      · exact (W_succ_iff (n + 1) a b).2 (Or.inr ⟨b, hs, W_refl _ b⟩)
      · exact (W_succ_iff (n + 1) a b).2 (Or.inr ⟨d, hd, ih hw⟩)

theorem W_unsnoc {n : ℕ} {a b : Fin M.N} (h : W M (n + 1) a b = true) :
    W M n a b = true ∨ ∃ c, W M n a c = true ∧ M.step c b = true := by
  induction n generalizing a with
  | zero =>
      rcases (W_succ_iff 0 a b).1 h with rfl | ⟨c, hc, hw⟩
      · exact Or.inl (W_refl 0 a)
      · rw [W_zero] at hw
        have : c = b := of_decide_eq_true hw
        subst this
        exact Or.inr ⟨a, W_refl 0 a, hc⟩
  | succ n ih =>
      rcases (W_succ_iff (n + 1) a b).1 h with rfl | ⟨c, hc, hw⟩
      · exact Or.inl (W_refl _ a)
      · rcases ih hw with hw' | ⟨d, hd1, hd2⟩
        · exact Or.inl ((W_succ_iff n a b).2 (Or.inr ⟨c, hc, hw'⟩))
        · exact Or.inr ⟨d, (W_succ_iff n a d).2 (Or.inr ⟨c, hc, hd1⟩), hd2⟩

theorem reaches_iff_exists_W {a b : Fin M.N} : M.Reaches a b ↔ ∃ n, W M n a b = true := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, W_refl 0 a⟩
    | tail h hs ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, W_snoc hn hs⟩
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero =>
        rw [W_zero] at hn
        exact (of_decide_eq_true hn) ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        rcases (W_succ_iff n a b).1 hn with rfl | ⟨c, hc, hw⟩
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.head hc (ih hw)

/-- A walk of length at most `2 ^ k` is found by the Savitch recursion at level `k`. -/
theorem Reach_of_W {k n : ℕ} {a b : Fin M.N} (hn : n ≤ 2 ^ k) (h : W M n a b = true) :
    Reach M k a b = true := by
  induction k generalizing n a b with
  | zero =>
      have h1 : W M 1 a b = true := W_le (by simpa using hn) h
      rcases (W_succ_iff 0 a b).1 h1 with rfl | ⟨c, hc, hw⟩
      · simp [Reach_zero]
      · rw [W_zero] at hw
        have : c = b := of_decide_eq_true hw
        subst this
        simp [Reach_zero, hc]
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have h' : W M (2 ^ k + 2 ^ k) a b = true := W_le (by omega) h
      obtain ⟨c, h1, h2⟩ := W_split h'
      exact (Reach_succ_iff k a b).2 ⟨c, ih le_rfl h1, ih le_rfl h2⟩

/-! ### Reachable sets and stabilisation -/

/-- The set of configurations reachable from `a` in at most `i` steps. -/
def Rset (M : Machine) (a : Fin M.N) (i : ℕ) : Finset (Fin M.N) :=
  Finset.univ.filter (fun b => W M i a b = true)

theorem mem_Rset {a b : Fin M.N} {i : ℕ} : b ∈ Rset M a i ↔ W M i a b = true := by
  simp [Rset]

theorem Rset_subset_succ (a : Fin M.N) (i : ℕ) : Rset M a i ⊆ Rset M a (i + 1) := by
  intro b hb
  exact mem_Rset.2 (W_mono (mem_Rset.1 hb))

theorem Rset_mono {a : Fin M.N} {i j : ℕ} (hij : i ≤ j) : Rset M a i ⊆ Rset M a j := by
  intro b hb
  exact mem_Rset.2 (W_le hij (mem_Rset.1 hb))

theorem Rset_fix_succ {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    Rset M a (i + 2) = Rset M a (i + 1) := by
  apply Finset.Subset.antisymm _ (Rset_subset_succ a (i + 1))
  intro b hb
  rcases W_unsnoc (mem_Rset.1 hb) with hw | ⟨c, hc1, hc2⟩
  · exact mem_Rset.2 hw
  · have hc : c ∈ Rset M a i := h ▸ mem_Rset.2 hc1
    exact mem_Rset.2 (W_snoc (mem_Rset.1 hc) hc2)

theorem Rset_fix_step {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    ∀ t, Rset M a (i + t + 1) = Rset M a (i + t) := by
  intro t
  induction t with
  | zero => simpa using h
  | succ t ih =>
      have := Rset_fix_succ (a := a) (i := i + t) ih
      have e1 : i + (t + 1) + 1 = i + t + 2 := by omega
      have e2 : i + (t + 1) = i + t + 1 := by omega
      rw [e1, e2]
      exact this

theorem Rset_fix {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    ∀ j, i ≤ j → Rset M a j = Rset M a i := by
  have key : ∀ t, Rset M a (i + t) = Rset M a i := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        have e : i + (t + 1) = i + t + 1 := by omega
        rw [e, Rset_fix_step h t, ih]
  intro j hj
  obtain ⟨t, rfl⟩ : ∃ t, j = i + t := ⟨j - i, by omega⟩
  exact key t

theorem Rset_card_grow {a : Fin M.N} (i : ℕ) (h : ∀ j < i, Rset M a (j + 1) ≠ Rset M a j) :
    i + 1 ≤ (Rset M a i).card := by
  induction i with
  | zero =>
      have : a ∈ Rset M a 0 := mem_Rset.2 (W_refl 0 a)
      exact Finset.card_pos.2 ⟨a, this⟩
  | succ i ih =>
      have hi : i + 1 ≤ (Rset M a i).card := ih (fun j hj => h j (by omega))
      have hne : Rset M a (i + 1) ≠ Rset M a i := h i (by omega)
      have hss : Rset M a i ⊂ Rset M a (i + 1) :=
        ⟨Rset_subset_succ a i, fun hcon => hne (Finset.Subset.antisymm hcon (Rset_subset_succ a i))⟩
      have := Finset.card_lt_card hss
      omega

theorem Rset_subset_card {a : Fin M.N} (n : ℕ) : Rset M a n ⊆ Rset M a M.N := by
  by_cases h : ∃ i < M.N, Rset M a (i + 1) = Rset M a i
  · obtain ⟨i, hi, hfix⟩ := h
    rcases Nat.lt_or_ge n M.N with hn | hn
    · exact Rset_mono (by omega)
    · have h1 : Rset M a n = Rset M a i := Rset_fix hfix n (by omega)
      have h2 : Rset M a M.N = Rset M a i := Rset_fix hfix M.N (by omega)
      rw [h1, h2]
  · push_neg at h
    have := Rset_card_grow (M := M) (a := a) M.N (fun j hj => h j hj)
    have hle : (Rset M a M.N).card ≤ M.N := by
      simpa using Finset.card_le_univ (Rset M a M.N)
    omega

/-- **Reachability is decided by the Savitch recursion**, provided `2 ^ K` is at least the
number of configurations. -/
theorem Reach_eq_true_iff_reaches {K : ℕ} (hK : M.N ≤ 2 ^ K) (a b : Fin M.N) :
    Reach M K a b = true ↔ M.Reaches a b := by
  constructor
  · exact Reach_sound
  · intro h
    obtain ⟨n, hn⟩ := reaches_iff_exists_W.1 h
    have hb : b ∈ Rset M a M.N := Rset_subset_card n (mem_Rset.2 hn)
    exact Reach_of_W hK (mem_Rset.1 hb)

end CS

