import Mathlib

/-!
# Spatial Memory Separation (seL4 / MILS separation-kernel integrity)

A machine-checked model of the memory-integrity property at the heart of a
separation kernel: a subject can only affect memory it holds explicit write
authority over. Reads/execution are modelled implicitly — only writes mutate
state, and every write is *guarded* by a static access-control policy
`writeAuth`. An unauthorized write is a provable no-op.

The headline results:
* `unauth_write_noop`   — the guard blocks an unauthorized write (no-op).
* `frame`               — if no operation is an authorized write to `a`, the
                          value at `a` is unchanged (memory integrity / frame).
* `cross_subject_isolation` — a subject with no write authority over `a`
                          (e.g. an address only another subject may write)
                          can never change the value at `a`, over ANY finite
                          sequence of its operations (noninterference).
* `memory_separation`   — (bonus) the final value at `a` depends ONLY on the
                          operations that are authorized writes to `a`; all
                          others may be deleted without changing the outcome.
-/

namespace Brockian.HighAssurance.MemorySeparation

/-- An address in the flat memory space. -/
abbrev Addr := ℕ
/-- A stored value. -/
abbrev Val := ℕ
/-- A subject / principal (a partition, in MILS terms). -/
abbrev Subject := ℕ
/-- Memory: a total map from addresses to values. -/
abbrev Mem := Addr → Val

/-- A primitive operation: subject `s` attempts to write value `v` at address `a`. -/
inductive Op
  | write (s : Subject) (a : Addr) (v : Val)

/-- One guarded step. Subject `s`'s write to `a` takes effect **only if** the
static policy `writeAuth s a` holds; otherwise the memory is left untouched.
This single `if` folds the reference monitor's authorization check into the
semantics — there is no code path by which an unauthorized subject mutates
memory. -/
def stepOp (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (op : Op) (m : Mem) : Mem :=
  match op with
  | Op.write s a v => fun x => if writeAuth s a ∧ x = a then v else m x

/-- Execute a finite sequence of operations left-to-right. -/
def run (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth] :
    List Op → Mem → Mem
  | [], m => m
  | op :: ops, m => run writeAuth ops (stepOp writeAuth op m)

/-- The predicate picking out the operations that are *authorized writes to the
particular address `a`* — i.e. exactly those whose effect can reach `a`. -/
def keepA (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (a : Addr) : Op → Bool
  | Op.write s a' _ => decide (writeAuth s a ∧ a' = a)

/-- **The guard blocks unauthorized writes.** If subject `s` lacks write
authority over `a`, its write is a complete no-op on memory. -/
theorem unauth_write_noop (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (s : Subject) (a : Addr) (v : Val) (m : Mem) (h : ¬ writeAuth s a) :
    stepOp writeAuth (Op.write s a v) m = m := by
  funext x
  simp only [stepOp]
  rw [if_neg (fun hc => h hc.1)]

/-- General (memory-generalized) frame lemma, the engine behind `frame`. -/
theorem frame_general (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (a : Addr) :
    ∀ (ops : List Op) (m : Mem),
      (∀ o ∈ ops, ¬ (∃ s v, o = Op.write s a v ∧ writeAuth s a)) →
      run writeAuth ops m a = m a := by
  intro ops
  induction ops with
  | nil => intro m _; rfl
  | cons op ops ih =>
    intro m h
    cases op with
    | write s addr v =>
      have htail : ∀ o ∈ ops, ¬ (∃ s v, o = Op.write s a v ∧ writeAuth s a) :=
        fun o ho => h o (List.mem_cons_of_mem _ ho)
      have hstep : stepOp writeAuth (Op.write s addr v) m a = m a := by
        simp only [stepOp]
        by_cases hw : writeAuth s addr
        · by_cases haddr : a = addr
          · exact absurd ⟨s, v, by rw [haddr], by rw [haddr]; exact hw⟩
              (h (Op.write s addr v) (by simp))
          · rw [if_neg (fun hc => haddr hc.2)]
        · rw [if_neg (fun hc => hw hc.1)]
      show run writeAuth ops (stepOp writeAuth (Op.write s addr v) m) a = m a
      rw [ih (stepOp writeAuth (Op.write s addr v) m) htail, hstep]

/-- **Memory integrity / frame property.** If none of the operations in `ops`
is an authorized write to address `a`, then the value at `a` is preserved:
`run ops m a = m a`. No unauthorized activity — and no authorized activity
aimed elsewhere — can perturb `a`. -/
theorem frame (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (ops : List Op) (m : Mem) (a : Addr)
    (h : ∀ o ∈ ops, ¬ (∃ s v, o = Op.write s a v ∧ writeAuth s a)) :
    run writeAuth ops m a = m a :=
  frame_general writeAuth a ops m h

/-- **Cross-subject isolation (noninterference).** Given two subjects `s1`, `s2`
with disjoint write authority, if every operation is performed by `s1`, and `a`
is an address `s2` may write but `s1` may not, then none of `s1`'s operations
can change the value at `a` — for any finite operation sequence. -/
theorem cross_subject_isolation (writeAuth : Subject → Addr → Prop)
    [DecidableRel writeAuth] (s1 s2 : Subject)
    (hdisj : ∀ a, writeAuth s1 a → ¬ writeAuth s2 a)
    (ops : List Op) (hops : ∀ o ∈ ops, ∃ v a, o = Op.write s1 a v)
    (m : Mem) (a : Addr) (hs2 : writeAuth s2 a) (hns1 : ¬ writeAuth s1 a) :
    run writeAuth ops m a = m a := by
  apply frame writeAuth ops m a
  intro o ho
  obtain ⟨v0, a0, rfl⟩ := hops o ho
  rintro ⟨s, v, heq, hw⟩
  injection heq with hs ha hv
  subst hs
  subst ha
  exact hns1 hw

/-- All addresses touched by a filtered (authorized-writes-to-`a`) list overwrite
`a` identically, so the value at `a` after running such a list is independent of
the starting memory (given agreement at `a`). This is the invariance lemma the
separation theorem rests on. -/
theorem run_filtered_indep (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (a : Addr) :
    ∀ (L : List Op), (∀ o ∈ L, keepA writeAuth a o = true) →
      ∀ (m m' : Mem), m a = m' a → run writeAuth L m a = run writeAuth L m' a := by
  intro L
  induction L with
  | nil => intro _ m m' hmm; exact hmm
  | cons op L ih =>
    intro hall m m' hmm
    cases op with
    | write s a' v =>
      have hcond : writeAuth s a ∧ a' = a := by
        have hop := hall (Op.write s a' v) (by simp)
        simp only [keepA] at hop
        exact of_decide_eq_true hop
      obtain ⟨hwa, ha'⟩ := hcond
      subst a'
      have htail : ∀ o ∈ L, keepA writeAuth a o = true :=
        fun o ho => hall o (List.mem_cons_of_mem _ ho)
      have hstep : (stepOp writeAuth (Op.write s a v) m) a
                 = (stepOp writeAuth (Op.write s a v) m') a := by
        simp only [stepOp]
        rw [if_pos ⟨hwa, trivial⟩, if_pos ⟨hwa, trivial⟩]
      show run writeAuth L (stepOp writeAuth (Op.write s a v) m) a
         = run writeAuth L (stepOp writeAuth (Op.write s a v) m') a
      exact ih htail _ _ hstep

/-- **The separation theorem (bonus, strong form).** The value at any address
`a` after running an arbitrary operation sequence depends *only* on those
operations that are authorized writes to `a`. Deleting every other operation
(unauthorized writes, and writes to other addresses) leaves the result at `a`
unchanged. This is spatial memory separation in its sharpest form. -/
theorem memory_separation (writeAuth : Subject → Addr → Prop) [DecidableRel writeAuth]
    (ops : List Op) (m : Mem) (a : Addr) :
    run writeAuth ops m a = run writeAuth (ops.filter (keepA writeAuth a)) m a := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | write s a' v =>
      by_cases hk : keepA writeAuth a (Op.write s a' v) = true
      · have hfilter : (Op.write s a' v :: ops).filter (keepA writeAuth a)
                     = Op.write s a' v :: ops.filter (keepA writeAuth a) := by
          simp [List.filter_cons, hk]
        rw [hfilter]
        show run writeAuth ops (stepOp writeAuth (Op.write s a' v) m) a
           = run writeAuth (ops.filter (keepA writeAuth a))
               (stepOp writeAuth (Op.write s a' v) m) a
        exact ih (stepOp writeAuth (Op.write s a' v) m)
      · have hk' : keepA writeAuth a (Op.write s a' v) = false := by
          cases hcv : keepA writeAuth a (Op.write s a' v) with
          | true => exact absurd hcv hk
          | false => rfl
        have hfilter : (Op.write s a' v :: ops).filter (keepA writeAuth a)
                     = ops.filter (keepA writeAuth a) := by
          simp [List.filter_cons, hk']
        rw [hfilter]
        show run writeAuth ops (stepOp writeAuth (Op.write s a' v) m) a
           = run writeAuth (ops.filter (keepA writeAuth a)) m a
        rw [ih (stepOp writeAuth (Op.write s a' v) m)]
        apply run_filtered_indep writeAuth a
        · intro o ho
          exact (List.mem_filter.mp ho).2
        · have hcond : ¬ (writeAuth s a ∧ a' = a) := by
            have hh0 : keepA writeAuth a (Op.write s a' v) = false := hk'
            simp only [keepA] at hh0
            exact of_decide_eq_false hh0
          simp only [stepOp]
          by_cases hh : writeAuth s a' ∧ a = a'
          · exact absurd ⟨by rw [hh.2]; exact hh.1, hh.2.symm⟩ hcond
          · rw [if_neg hh]

/-! ## Non-vacuity: a concrete two-subject policy

Subject `0` may write addresses `0` and `1`; subject `1` may write address `2`.
Their write authority is disjoint. -/

/-- Concrete static policy. -/
def demoAuth : Subject → Addr → Prop :=
  fun s a => (s = 0 ∧ (a = 0 ∨ a = 1)) ∨ (s = 1 ∧ a = 2)

instance : DecidableRel demoAuth := by
  intro s a
  unfold demoAuth
  infer_instance

/-- (a) An **authorized** write genuinely changes memory: starting from the
all-zero memory, subject `0`'s write of `42` to address `0` yields `42` there
(whereas it was `0`). -/
example : run demoAuth [Op.write 0 0 42] (fun _ => 0) 0 = 42 := by
  have hc : demoAuth 0 0 ∧ True := ⟨Or.inl ⟨rfl, Or.inl rfl⟩, trivial⟩
  simp only [run, stepOp]
  rw [if_pos hc]

/-- The initial value at address `0` was `0`, so the authorized write above is a
genuine state change, not a no-op. -/
example : (fun _ : Addr => (0 : Val)) 0 = 0 := rfl

/-- (b) An **unauthorized** write is a provable no-op: subject `1` is not
authorized for address `0`, so its write leaves memory identical. -/
example (m : Mem) : stepOp demoAuth (Op.write 1 0 99) m = m :=
  unauth_write_noop demoAuth 1 0 99 m (by decide)

/-- The two subjects have disjoint write authority. -/
theorem demoAuth_disjoint : ∀ a, demoAuth 0 a → ¬ demoAuth 1 a := by
  intro a ha hb
  unfold demoAuth at ha hb
  rcases hb with ⟨h, _⟩ | ⟨_, rfl⟩
  · exact absurd h (by decide)
  · rcases ha with ⟨_, h | h⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- (c) Cross-subject isolation on the concrete disjoint policy: any sequence of
subject `0`'s operations leaves address `2` (which only subject `1` may write)
untouched. Verified against the concrete policy with `decide`. -/
example (m : Mem) : run demoAuth [Op.write 0 0 5, Op.write 0 1 7] m 2 = m 2 := by
  apply cross_subject_isolation demoAuth 0 1 demoAuth_disjoint
  · intro o ho
    fin_cases ho
    · exact ⟨5, 0, rfl⟩
    · exact ⟨7, 1, rfl⟩
  · decide
  · decide

end Brockian.HighAssurance.MemorySeparation
