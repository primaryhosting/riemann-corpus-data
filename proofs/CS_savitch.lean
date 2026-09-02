/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

/-! ## Walks and bounded reachability in a directed graph -/

section Reach

variable {Q : Type}

/-- `Walk E m u v`: there is a walk of exactly `m` steps from `u` to `v`. -/
def Walk (E : Q → Q → Prop) (m : ℕ) (u v : Q) : Prop :=
  ∃ p : ℕ → Q, p 0 = u ∧ p m = v ∧ ∀ i < m, E (p i) (p (i + 1))

/-- `ReachLe E m u v`: there is a walk of at most `m` steps from `u` to `v`. -/
def ReachLe (E : Q → Q → Prop) (m : ℕ) (u v : Q) : Prop := ∃ j ≤ m, Walk E j u v

variable {E : Q → Q → Prop}

theorem walk_zero (u : Q) : Walk E 0 u u := ⟨fun _ => u, rfl, rfl, by omega⟩

theorem walk_one {u v : Q} (h : E u v) : Walk E 1 u v :=
  ⟨fun i => if i = 0 then u else v, by simp, by simp, by
    intro i hi
    interval_cases i
    simpa using h⟩

theorem walk_comp {a b : ℕ} {u w v : Q} (h₁ : Walk E a u w) (h₂ : Walk E b w v) :
    Walk E (a + b) u v := by
  obtain ⟨p, hp0, hpa, hp⟩ := h₁
  obtain ⟨q, hq0, hqb, hq⟩ := h₂
  refine ⟨fun i => if i ≤ a then p i else q (i - a), ?_, ?_, ?_⟩
  · simp [hp0]
  · by_cases h : a + b ≤ a
    · have hb : b = 0 := by omega
      subst hb
      simp only [Nat.add_zero, le_refl, if_pos]
      rw [hpa, ← hq0, ← hqb]
    · simp only [h, if_neg, Nat.add_sub_cancel_left]
      exact hqb
  · intro i hi
    by_cases h1 : i + 1 ≤ a
    · have h0 : i ≤ a := by omega
      simp only [h0, h1, if_pos]
      exact hp i (by omega)
    · by_cases h0 : i ≤ a
      · have hia : i = a := by omega
        subst hia
        simp only [le_refl, if_pos, h1, if_neg, Nat.add_sub_cancel_left]
        rw [hpa, ← hq0]
        exact hq 0 (by omega)
      · simp only [h0, h1, if_neg]
        have : i + 1 - a = (i - a) + 1 := by omega
        rw [this]
        exact hq (i - a) (by omega)

theorem walk_split {a b : ℕ} {u v : Q} (h : Walk E (a + b) u v) :
    ∃ w, Walk E a u w ∧ Walk E b w v := by
  obtain ⟨p, hp0, hpab, hp⟩ := h
  refine ⟨p a, ⟨p, hp0, rfl, fun i hi => hp i (by omega)⟩,
    ⟨fun i => p (a + i), rfl, by simpa using hpab, fun i hi => ?_⟩⟩
  have h2 := hp (a + i) (by omega)
  simpa [Nat.add_assoc] using h2

theorem reachLe_comp {a b : ℕ} {u w v : Q} (h₁ : ReachLe E a u w) (h₂ : ReachLe E b w v) :
    ReachLe E (a + b) u v := by
  obtain ⟨i, hi, hw1⟩ := h₁
  obtain ⟨j, hj, hw2⟩ := h₂
  exact ⟨i + j, by omega, walk_comp hw1 hw2⟩

theorem reachLe_split {a b : ℕ} {u v : Q} (h : ReachLe E (a + b) u v) :
    ∃ w, ReachLe E a u w ∧ ReachLe E b w v := by
  obtain ⟨m, hm, hw⟩ := h
  by_cases ha : m ≤ a
  · obtain ⟨p, hp0, hpm, hp⟩ := hw
    exact ⟨v, ⟨m, ha, ⟨p, hp0, hpm, hp⟩⟩, ⟨0, Nat.zero_le _, walk_zero v⟩⟩
  · have : m = a + (m - a) := by omega
    rw [this] at hw
    obtain ⟨w, hw1, hw2⟩ := walk_split hw
    exact ⟨w, ⟨a, le_refl _, hw1⟩, ⟨m - a, by omega, hw2⟩⟩

theorem walk_shorten [Fintype Q] {m : ℕ} {u v : Q} (hm : Fintype.card Q ≤ m)
    (h : Walk E m u v) : ∃ m' < m, Walk E m' u v := by
  obtain ⟨p, hp0, hpm, hp⟩ := h
  have hcard : Fintype.card Q < Fintype.card (Fin (m + 1)) := by
    simpa using Nat.lt_succ_of_le hm
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (m + 1) => p i) hcard
  -- wlog i < j
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact walk_shorten_aux hp0 hpm hp i j hlt hfij
  · exact walk_shorten_aux hp0 hpm hp j i hlt hfij.symm
where
  walk_shorten_aux {m : ℕ} {u v : Q} {p : ℕ → Q} (hp0 : p 0 = u) (hpm : p m = v)
      (hp : ∀ i < m, E (p i) (p (i + 1))) (i j : Fin (m + 1)) (hlt : i < j)
      (hfij : p i = p j) : ∃ m' < m, Walk E m' u v := by
    set d := (j : ℕ) - (i : ℕ) with hd
    have hd0 : 0 < d := by
      have := hlt
      simp only [Fin.lt_def] at this
      omega
    have hjm : (j : ℕ) ≤ m := by omega
    refine ⟨m - d, by omega, fun k => if k < (i : ℕ) then p k else p (k + d), ?_, ?_, ?_⟩
    · by_cases h : 0 < (i : ℕ)
      · simp [h, hp0]
      · have hi0 : (i : ℕ) = 0 := by omega
        have hdj : d = (j : ℕ) := by omega
        simp only [hi0, Nat.lt_irrefl, Nat.zero_add, if_false]
        rw [hdj, ← hfij, hi0, hp0]
    · have h1 : ¬ (m - d < (i : ℕ)) := by omega
      have h2 : m - d + d = m := by omega
      simp only [h1, if_false]
      rw [h2, hpm]
    · intro k hk
      by_cases h1 : k + 1 < (i : ℕ)
      · have h0 : k < (i : ℕ) := by omega
        simp only [h0, h1, if_pos]
        exact hp k (by omega)
      · by_cases h0 : k < (i : ℕ)
        · have hki : k + 1 = (i : ℕ) := by omega
          simp only [h0, if_pos, h1, if_neg]
          have : k + 1 + d = (j : ℕ) := by omega
          rw [this, ← hfij, ← hki]
          exact hp k (by omega)
        · simp only [h0, h1, if_neg]
          have : k + 1 + d = (k + d) + 1 := by omega
          rw [this]
          exact hp (k + d) (by omega)

theorem reachLe_of_walk [Fintype Q] {m B : ℕ} {u v : Q} (hcard : Fintype.card Q ≤ B)
    (h : Walk E m u v) : ReachLe E B u v := by
  induction m using Nat.strong_induction_on generalizing u with
  | _ m ih =>
    by_cases hm : Fintype.card Q ≤ m
    · obtain ⟨m', hm', hw⟩ := walk_shorten hm h
      exact ih m' hm' hw
    · exact ⟨m, by omega, h⟩

theorem walk_of_reflTransGen {u v : Q} (h : Relation.ReflTransGen E u v) :
    ∃ m, Walk E m u v := by
  induction h with
  | refl => exact ⟨0, walk_zero u⟩
  | tail _ hb ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, walk_comp hm (walk_one hb)⟩

theorem reflTransGen_of_walk {m : ℕ} {u v : Q} (h : Walk E m u v) :
    Relation.ReflTransGen E u v := by
  obtain ⟨p, hp0, hpm, hp⟩ := h
  subst hp0; subst hpm
  clear * - hp
  induction m with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    exact Relation.ReflTransGen.tail (ih (fun i hi => hp i (by omega))) (hp n (by omega))

/-- The Savitch predicate: `reachP E k u v` says `v` is reachable from `u`
in at most `2 ^ k` steps, defined by the divide-and-conquer recursion. -/
def reachP (E : Q → Q → Prop) : ℕ → Q → Q → Prop
  | 0, u, v => u = v ∨ E u v
  | (k + 1), u, v => ∃ w, reachP E k u w ∧ reachP E k w v

theorem reachP_iff (k : ℕ) (u v : Q) : reachP E k u v ↔ ReachLe E (2 ^ k) u v := by
  induction k generalizing u v with
  | zero =>
    constructor
    · rintro (rfl | h)
      · exact ⟨0, by norm_num, walk_zero u⟩
      · exact ⟨1, by norm_num, walk_one h⟩
    · rintro ⟨j, hj, hw⟩
      simp only [pow_zero] at hj
      interval_cases j
      · obtain ⟨p, hp0, hp1, _⟩ := hw
        exact Or.inl (by rw [← hp0, ← hp1])
      · obtain ⟨p, hp0, hp1, hp⟩ := hw
        exact Or.inr (by rw [← hp0, ← hp1]; exact hp 0 (by omega))
  | succ k ih =>
    have hpow : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    constructor
    · rintro ⟨w, h1, h2⟩
      rw [hpow]
      exact reachLe_comp ((ih u w).1 h1) ((ih w v).1 h2)
    · intro h
      rw [hpow] at h
      obtain ⟨w, h1, h2⟩ := reachLe_split h
      exact ⟨w, (ih u w).2 h1, (ih w v).2 h2⟩

end Reach

/-! ## Space-bounded machines with random access to a read-only input

A machine has a finite set `S` of memory configurations.  Its *space* is measured
by the number of bits needed to store a configuration: the machine runs in space
`s` if `S` embeds into `Fin s → Bool`.  The input is read-only and is accessed at
random: in configuration `q` the machine reads the input bit at position `idx q`,
and its transition depends on the current configuration and on that single bit
only.  (Thus the machine itself only depends on the input *length*, never on the
input itself; this is what makes the space measure meaningful.) -/

/-- The `i`-th bit of the input word `x`; `false` beyond the end of the word. -/
def bitAt (x : List Bool) (i : ℕ) : Bool := x.getD i false

open scoped Classical in
/-- The (classical) truth value of a proposition, as a `Bool`. -/
noncomputable def bof (P : Prop) : Bool := if P then true else false

theorem bof_eq_true {P : Prop} : bof P = true ↔ P := by
  by_cases h : P <;> simp [bof, h]

theorem bof_eq_false {P : Prop} : bof P = false ↔ ¬ P := by
  by_cases h : P <;> simp [bof, h]

/-- A nondeterministic machine with read-only random access input. -/
structure NMachine where
  /-- The type of memory configurations. -/
  S : Type
  /-- Position of the input bit scanned in a given configuration. -/
  idx : S → ℕ
  /-- The transition relation: `next q b q'` if `q'` is a possible successor of `q`
  when the scanned input bit is `b`. -/
  next : S → Bool → S → Prop
  /-- The initial configuration. -/
  start : S
  /-- The accepting configurations. -/
  acc : S → Prop

/-- A deterministic machine with read-only random access input. -/
structure DMachine where
  /-- The type of memory configurations. -/
  S : Type
  /-- Position of the input bit scanned in a given configuration. -/
  idx : S → ℕ
  /-- The transition function. -/
  next : S → Bool → S
  /-- The initial configuration. -/
  start : S
  /-- The accepting configurations. -/
  acc : S → Prop

/-- The one-step relation of a nondeterministic machine on a fixed input. -/
def NMachine.stepRel (M : NMachine) (x : List Bool) (u v : M.S) : Prop :=
  M.next u (bitAt x (M.idx u)) v

/-- A nondeterministic machine accepts `x` if some accepting configuration is
reachable from the initial configuration. -/
def NMachine.Accepts (M : NMachine) (x : List Bool) : Prop :=
  ∃ z, Relation.ReflTransGen (M.stepRel x) M.start z ∧ M.acc z

/-- The one-step function of a deterministic machine on a fixed input. -/
def DMachine.stepFun (M : DMachine) (x : List Bool) (u : M.S) : M.S :=
  M.next u (bitAt x (M.idx u))

/-- A deterministic machine accepts `x` if its run enters an accepting configuration. -/
def DMachine.Accepts (M : DMachine) (x : List Bool) : Prop :=
  ∃ T, M.acc ((M.stepFun x)^[T] M.start)

/-- `M` runs in space `s`: a configuration of `M` fits in `s` bits. -/
def NMachine.SpaceLE (M : NMachine) (s : ℕ) : Prop := Nonempty (M.S ↪ (Fin s → Bool))

/-- `M` runs in space `s`: a configuration of `M` fits in `s` bits. -/
def DMachine.SpaceLE (M : DMachine) (s : ℕ) : Prop := Nonempty (M.S ↪ (Fin s → Bool))

/-- The nondeterministic space complexity class `NSPACE f`. -/
def NSPACE (f : ℕ → ℕ) : Set (List Bool → Prop) :=
  {L | ∀ n : ℕ, ∃ M : NMachine, M.SpaceLE (f n) ∧
        ∀ x : List Bool, x.length = n → (L x ↔ M.Accepts x)}

/-- The deterministic space complexity class `DSPACE f`. -/
def DSPACE (f : ℕ → ℕ) : Set (List Bool → Prop) :=
  {L | ∀ n : ℕ, ∃ M : DMachine, M.SpaceLE (f n) ∧
        ∀ x : List Bool, x.length = n → (L x ↔ M.Accepts x)}

/-! ## The Savitch simulation -/

/-- Control state of the deterministic Savitch simulator. -/
inductive Ctl (Q : Type) where
  /-- Evaluate the query "is there a path of length `≤ 2 ^ k` from `u` to `v`?". -/
  | call (k : ℕ) (u v : Q) : Ctl Q
  /-- Return the value `b` of the query just evaluated. -/
  | ret (b : Bool) : Ctl Q
  /-- Move on to the next candidate accepting configuration. -/
  | scan : Ctl Q
  /-- Halt with answer `b`. -/
  | done (b : Bool) : Ctl Q

section Sav

variable (M : NMachine) [Fintype M.S]

/-- A stack frame: the level of the subcalls, the two endpoints, the index of the
current candidate midpoint, and the phase (`false` = first half, `true` = second half). -/
abbrev SFrame : Type := ℕ × M.S × M.S × ℕ × Bool

/-- A configuration of the Savitch simulator: index of the current candidate accepting
configuration, the stack, the stack depth, and the control state. -/
abbrev SSt : Type := ℕ × (ℕ → SFrame M) × ℕ × Ctl M.S

/-- An enumeration of the configurations of `M`. -/
noncomputable def enumQ (i : ℕ) : M.S :=
  if h : i < Fintype.card M.S then (Fintype.equivFin M.S).symm ⟨i, h⟩ else M.start

theorem enumQ_surj (z : M.S) : ∃ i < Fintype.card M.S, enumQ M i = z := by
  refine ⟨(Fintype.equivFin M.S z : ℕ), (Fintype.equivFin M.S z).isLt, ?_⟩
  simp [enumQ, (Fintype.equivFin M.S z).isLt]

/-- Advance to the next candidate midpoint, or pop the stack if they are exhausted. -/
noncomputable def sadvance (t j' : ℕ) (A : ℕ → SFrame M) : SSt M :=
  if (A j').2.2.2.1 + 1 < Fintype.card M.S then
    (t, Function.update A j' ((A j').1, (A j').2.1, (A j').2.2.1, (A j').2.2.2.1 + 1, false),
      j' + 1, Ctl.call (A j').1 (A j').2.1 (enumQ M ((A j').2.2.2.1 + 1)))
  else (t, A, j', Ctl.ret false)

/-- One step of the Savitch simulator, given the scanned input bit `b`. -/
noncomputable def sstep (s : ℕ) (b : Bool) : SSt M → SSt M
  | (t, A, j, Ctl.done c) => (t, A, j, Ctl.done c)
  | (t, A, j, Ctl.scan) =>
      if t < Fintype.card M.S then
        (if bof (M.acc (enumQ M t)) then (t, A, j, Ctl.call s M.start (enumQ M t))
          else (t + 1, A, j, Ctl.scan))
      else (t, A, j, Ctl.done false)
  | (t, A, j, Ctl.call 0 u v) => (t, A, j, Ctl.ret (bof (u = v ∨ M.next u b v)))
  | (t, A, j, Ctl.call (k + 1) u v) =>
      (t, Function.update A j (k, u, v, 0, false), j + 1, Ctl.call k u (enumQ M 0))
  | (t, A, 0, Ctl.ret c) => if c then (t, A, 0, Ctl.done true) else (t + 1, A, 0, Ctl.scan)
  | (t, A, j' + 1, Ctl.ret c) =>
      if (A j').2.2.2.2 then
        (if c then (t, A, j', Ctl.ret true) else sadvance M t j' A)
      else
        (if c then
          (t, Function.update A j' ((A j').1, (A j').2.1, (A j').2.2.1, (A j').2.2.2.1, true),
            j' + 1, Ctl.call (A j').1 (enumQ M (A j').2.2.2.1) (A j').2.2.1)
         else sadvance M t j' A)

/-- The input position scanned by the simulator. -/
def idxS : SSt M → ℕ
  | (_, _, _, Ctl.call 0 u _) => M.idx u
  | _ => 0

/-- One step of the simulator on the fixed input `x`. -/
noncomputable def dstep (s : ℕ) (x : List Bool) (st : SSt M) : SSt M :=
  sstep M s (bitAt x (idxS M st)) st

/-- States that have not yet halted with answer `true`. -/
def NotDT (st : SSt M) : Prop := st.2.2.2 ≠ Ctl.done true

section Steps

variable (s : ℕ) (x : List Bool) (t j k : ℕ) (A : ℕ → SFrame M) (u v : M.S)

@[simp] theorem dstep_done (c : Bool) :
    dstep M s x (t, A, j, Ctl.done c) = (t, A, j, Ctl.done c) := by
  simp [dstep, sstep, idxS]

@[simp] theorem dstep_call_zero :
    dstep M s x (t, A, j, Ctl.call 0 u v)
      = (t, A, j, Ctl.ret (bof (u = v ∨ M.stepRel x u v))) := by
  simp [dstep, sstep, idxS, NMachine.stepRel]

@[simp] theorem dstep_call_succ :
    dstep M s x (t, A, j, Ctl.call (k + 1) u v)
      = (t, Function.update A j (k, u, v, 0, false), j + 1, Ctl.call k u (enumQ M 0)) := by
  simp [dstep, sstep, idxS]

@[simp] theorem dstep_ret_zero (c : Bool) :
    dstep M s x (t, A, 0, Ctl.ret c)
      = (if c then (t, A, 0, Ctl.done true) else (t + 1, A, 0, Ctl.scan)) := by
  cases c <;> simp [dstep, sstep, idxS]

theorem dstep_scan :
    dstep M s x (t, A, j, Ctl.scan)
      = (if t < Fintype.card M.S then
          (if bof (M.acc (enumQ M t)) then (t, A, j, Ctl.call s M.start (enumQ M t))
            else (t + 1, A, j, Ctl.scan))
         else (t, A, j, Ctl.done false)) := by
  simp [dstep, sstep, idxS]

theorem dstep_ret_succ (c : Bool) :
    dstep M s x (t, A, j + 1, Ctl.ret c)
      = (if (A j).2.2.2.2 then
          (if c then (t, A, j, Ctl.ret true) else sadvance M t j A)
         else
          (if c then
            (t, Function.update A j ((A j).1, (A j).2.1, (A j).2.2.1, (A j).2.2.2.1, true),
              j + 1, Ctl.call (A j).1 (enumQ M (A j).2.2.2.1) (A j).2.2.1)
           else sadvance M t j A)) := by
  simp [dstep, sstep, idxS]

end Steps

end Sav

/-! ## Safe runs -/

/-- `SafeRun f P a b`: iterating `f` leads from `a` to `b`, and all states strictly
before `b` satisfy `P`. -/
def SafeRun {α : Type} (f : α → α) (P : α → Prop) (a b : α) : Prop :=
  ∃ T, f^[T] a = b ∧ ∀ T' < T, P (f^[T'] a)

namespace SafeRun

variable {α : Type} {f : α → α} {P : α → Prop} {a b c : α}

theorem rfl' : SafeRun f P a a := ⟨0, by simp, by omega⟩

theorem one (h : P a) (hb : f a = b) : SafeRun f P a b :=
  ⟨1, by simpa using hb, by
    intro T' hT'
    interval_cases T'
    simpa using h⟩

theorem trans' (h₁ : SafeRun f P a b) (h₂ : SafeRun f P b c) : SafeRun f P a c := by
  obtain ⟨T₁, e₁, s₁⟩ := h₁
  obtain ⟨T₂, e₂, s₂⟩ := h₂
  refine ⟨T₂ + T₁, ?_, ?_⟩
  · rw [Function.iterate_add_apply, e₁, e₂]
  · intro T' hT'
    by_cases h : T' < T₁
    · exact s₁ T' h
    · have hr : T' = (T' - T₁) + T₁ := by omega
      rw [hr, Function.iterate_add_apply, e₁]
      exact s₂ _ (by omega)

end SafeRun


end CS

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

