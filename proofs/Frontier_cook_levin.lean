/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

/-! ## An injective pairing function -/

/-- A pairing function on `Nat`. -/
def npair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem npair_succ_left (a b : Nat) : npair (a + 1) b = 2 * npair a b := by
  rw [npair, npair, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]

theorem npair_zero_left (b : Nat) : npair 0 b = 2 * b + 1 := by
  rw [npair, Nat.pow_zero, Nat.one_mul]

theorem npair_inj : ∀ a c b d : Nat, npair a b = npair c d → a = c ∧ b = d := by
  intro a
  induction a with
  | zero =>
      intro c b d h
      cases c with
      | zero =>
          rw [npair_zero_left, npair_zero_left] at h
          omega
      | succ c =>
          exfalso
          rw [npair_zero_left, npair_succ_left] at h
          generalize npair c d = m at h
          omega
  | succ a ih =>
      intro c b d h
      cases c with
      | zero =>
          exfalso
          rw [npair_zero_left, npair_succ_left] at h
          generalize npair a b = m at h
          omega
      | succ c =>
          rw [npair_succ_left, npair_succ_left] at h
          have h' : npair a b = npair c d := by omega
          have := ih c b d h'
          omega

theorem npair_left {a b c d : Nat} (h : npair a b = npair c d) : a = c :=
  (npair_inj a c b d h).1

theorem npair_right {a b c d : Nat} (h : npair a b = npair c d) : b = d :=
  (npair_inj a c b d h).2

/-! ## Boolean expressions (circuits given as formulas) -/

/-- Boolean expressions over variables indexed by `Nat`. -/
inductive BoolExpr : Type
  | var (i : Nat) : BoolExpr
  | tru : BoolExpr
  | fls : BoolExpr
  | neg (a : BoolExpr) : BoolExpr
  | conj (a b : BoolExpr) : BoolExpr
  | disj (a b : BoolExpr) : BoolExpr

namespace BoolExpr

/-- Semantics of a boolean expression under an assignment. -/
def eval (σ : Nat → Bool) : BoolExpr → Bool
  | var i => σ i
  | tru => true
  | fls => false
  | neg a => !(eval σ a)
  | conj a b => (eval σ a) && (eval σ b)
  | disj a b => (eval σ a) || (eval σ b)

/-- Number of nodes of a boolean expression. -/
def size : BoolExpr → Nat
  | var _ => 1
  | tru => 1
  | fls => 1
  | neg a => a.size + 1
  | conj a b => a.size + b.size + 1
  | disj a b => a.size + b.size + 1

/-- An injective encoding of boolean expressions by natural numbers. -/
def enc : BoolExpr → Nat
  | var i => npair 0 i
  | tru => npair 1 0
  | fls => npair 2 0
  | neg a => npair 3 a.enc
  | conj a b => npair 4 (npair a.enc b.enc)
  | disj a b => npair 5 (npair a.enc b.enc)

theorem enc_inj : ∀ a b : BoolExpr, enc a = enc b → a = b := by
  intro a
  induction a with
  | var i =>
      intro b; cases b <;> intro h <;> simp only [enc] at h <;>
        first
          | exact absurd (npair_left h) (by decide)
          | exact congrArg BoolExpr.var (npair_right h)
  | tru =>
      intro b; cases b <;> intro h <;> simp only [enc] at h <;>
        first
          | exact absurd (npair_left h) (by decide)
          | rfl
  | fls =>
      intro b; cases b <;> intro h <;> simp only [enc] at h <;>
        first
          | exact absurd (npair_left h) (by decide)
          | rfl
  | neg a ih =>
      intro b; cases b <;> intro h <;> simp only [enc] at h <;>
        first
          | exact absurd (npair_left h) (by decide)
          | exact congrArg BoolExpr.neg (ih _ (npair_right h))
  | conj a b iha ihb =>
      intro c; cases c <;> intro h <;> simp only [enc] at h <;>
        first
          | exact absurd (npair_left h) (by decide)
          | (have h' := npair_right h
             rw [iha _ (npair_left h'), ihb _ (npair_right h')])
  | disj a b iha ihb =>
      intro c; cases c <;> intro h <;> simp only [enc] at h <;>
        first
          | exact absurd (npair_left h) (by decide)
          | (have h' := npair_right h
             rw [iha _ (npair_left h'), ihb _ (npair_right h')])

/-- Simultaneous substitution of expressions for variables. -/
def subst (f : Nat → BoolExpr) : BoolExpr → BoolExpr
  | var i => f i
  | tru => tru
  | fls => fls
  | neg a => neg (subst f a)
  | conj a b => conj (subst f a) (subst f b)
  | disj a b => disj (subst f a) (subst f b)

theorem eval_subst (σ : Nat → Bool) (f : Nat → BoolExpr) :
    ∀ e : BoolExpr, eval σ (subst f e) = eval (fun i => eval σ (f i)) e := by
  intro e
  induction e with
  | var i => rfl
  | tru => rfl
  | fls => rfl
  | neg a ih => simp [subst, eval, ih]
  | conj a b iha ihb => simp [subst, eval, iha, ihb]
  | disj a b iha ihb => simp [subst, eval, iha, ihb]

theorem size_subst (f : Nat → BoolExpr) (hf : ∀ i, (f i).size = 1) :
    ∀ e : BoolExpr, (subst f e).size = e.size := by
  intro e
  induction e with
  | var i => simpa [subst, size] using hf i
  | tru => rfl
  | fls => rfl
  | neg a ih => simp [subst, size, ih]
  | conj a b iha ihb => simp [subst, size, iha, ihb]
  | disj a b iha ihb => simp [subst, size, iha, ihb]

end BoolExpr

/-! ## CNF formulas -/

/-- A literal: a variable index together with a sign (`true` = positive). -/
abbrev Lit : Type := Nat × Bool
/-- A clause: a disjunction of literals. -/
abbrev Clause : Type := List Lit
/-- A CNF formula: a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- Value of a literal under an assignment. -/
def evalLit (σ : Nat → Bool) (l : Lit) : Bool := σ l.1 == l.2

/-- Value of a clause under an assignment. -/
def evalClause (σ : Nat → Bool) (c : Clause) : Bool := c.any (evalLit σ)

/-- Value of a CNF formula under an assignment. -/
def evalCNF (σ : Nat → Bool) (φ : CNF) : Bool := φ.all (evalClause σ)

/-- A CNF formula is satisfiable if some assignment makes it true. -/
def Satisfiable (φ : CNF) : Prop := ∃ σ : Nat → Bool, evalCNF σ φ = true

theorem evalCNF_append (σ : Nat → Bool) (φ ψ : CNF) :
    evalCNF σ (φ ++ ψ) = (evalCNF σ φ && evalCNF σ ψ) := by
  simp [evalCNF, List.all_append]

/-! ## The Tseitin transformation -/

/-- The gate variable attached to a subexpression (an odd number). -/
def gv (e : BoolExpr) : Nat := 2 * e.enc + 1

/-- The variable carrying the circuit input `i` (an even number). -/
def xv (i : Nat) : Nat := 2 * i

theorem gv_inj (e e' : BoolExpr) (h : gv e = gv e') : e = e' :=
  BoolExpr.enc_inj _ _ (by simp only [gv] at h; omega)

theorem xv_ne_gv (i : Nat) (e : BoolExpr) : xv i ≠ gv e := by
  simp only [xv, gv]; omega

/-- The Tseitin clauses of an expression: they force the gate variable of every
subexpression to carry the value of that subexpression. -/
def cls : BoolExpr → CNF
  | .var i => [[(gv (.var i), true), (xv i, false)], [(gv (.var i), false), (xv i, true)]]
  | .tru => [[(gv .tru, true)]]
  | .fls => [[(gv .fls, false)]]
  | .neg a =>
      cls a ++ [[(gv (.neg a), true), (gv a, true)], [(gv (.neg a), false), (gv a, false)]]
  | .conj a b =>
      cls a ++ cls b ++
        [[(gv (.conj a b), false), (gv a, true)], [(gv (.conj a b), false), (gv b, true)],
         [(gv (.conj a b), true), (gv a, false), (gv b, false)]]
  | .disj a b =>
      cls a ++ cls b ++
        [[(gv (.disj a b), true), (gv a, false)], [(gv (.disj a b), true), (gv b, false)],
         [(gv (.disj a b), false), (gv a, true), (gv b, true)]]

/-- The CNF formula produced from a boolean expression by the Tseitin transformation. -/
def toCNF (e : BoolExpr) : CNF := cls e ++ [[(gv e, true)]]

theorem cls_sound (τ : Nat → Bool) :
    ∀ e : BoolExpr, evalCNF τ (cls e) = true →
      τ (gv e) = BoolExpr.eval (fun i => τ (xv i)) e := by
  intro e
  induction e with
  | var i =>
      intro h
      simp only [cls, evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, BoolExpr.eval] at h ⊢
      revert h
      cases τ (gv (BoolExpr.var i)) <;> cases τ (xv i) <;> simp
  | tru =>
      intro h
      simp only [cls, evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, BoolExpr.eval] at h ⊢
      revert h
      cases τ (gv BoolExpr.tru) <;> simp
  | fls =>
      intro h
      simp only [cls, evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, BoolExpr.eval] at h ⊢
      revert h
      cases τ (gv BoolExpr.fls) <;> simp
  | neg a ih =>
      intro h
      rw [cls, evalCNF_append] at h
      simp only [Bool.and_eq_true] at h
      have ha := ih h.1
      simp only [BoolExpr.eval]
      rw [← ha]
      have h2 := h.2
      simp only [evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil] at h2 ⊢
      revert h2
      cases τ (gv (BoolExpr.neg a)) <;> cases τ (gv a) <;> simp
  | conj a b iha ihb =>
      intro h
      rw [cls, evalCNF_append, evalCNF_append] at h
      simp only [Bool.and_eq_true] at h
      have ha := iha h.1.1
      have hb := ihb h.1.2
      simp only [BoolExpr.eval]
      rw [← ha, ← hb]
      have h2 := h.2
      simp only [evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil] at h2 ⊢
      revert h2
      cases τ (gv (BoolExpr.conj a b)) <;> cases τ (gv a) <;> cases τ (gv b) <;> simp
  | disj a b iha ihb =>
      intro h
      rw [cls, evalCNF_append, evalCNF_append] at h
      simp only [Bool.and_eq_true] at h
      have ha := iha h.1.1
      have hb := ihb h.1.2
      simp only [BoolExpr.eval]
      rw [← ha, ← hb]
      have h2 := h.2
      simp only [evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil] at h2 ⊢
      revert h2
      cases τ (gv (BoolExpr.disj a b)) <;> cases τ (gv a) <;> cases τ (gv b) <;> simp

open scoped Classical in
/-- The canonical assignment extending `σ`: input variables get their value from `σ`,
and the gate variable of a subexpression gets the value of that subexpression. -/
noncomputable def canon (σ : Nat → Bool) : Nat → Bool := fun v =>
  if h : ∃ e : BoolExpr, gv e = v then BoolExpr.eval σ h.choose else σ (v / 2)

theorem canon_xv (σ : Nat → Bool) (i : Nat) : canon σ (xv i) = σ i := by
  have h : ¬ ∃ e : BoolExpr, gv e = xv i := by
    rintro ⟨e, he⟩
    exact xv_ne_gv i e he.symm
  rw [canon, dif_neg h]
  show σ (2 * i / 2) = σ i
  congr 1
  omega

theorem canon_gv (σ : Nat → Bool) (e : BoolExpr) : canon σ (gv e) = BoolExpr.eval σ e := by
  have h : ∃ e' : BoolExpr, gv e' = gv e := ⟨e, rfl⟩
  have hc : h.choose = e := gv_inj _ _ h.choose_spec
  rw [canon, dif_pos h, hc]

theorem cls_complete (σ : Nat → Bool) : ∀ e : BoolExpr, evalCNF (canon σ) (cls e) = true := by
  intro e
  induction e with
  | var i =>
      simp only [cls, evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, canon_gv, canon_xv, BoolExpr.eval]
      cases σ i <;> simp
  | tru =>
      simp only [cls, evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, canon_gv, BoolExpr.eval]
      simp
  | fls =>
      simp only [cls, evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, canon_gv, BoolExpr.eval]
      simp
  | neg a ih =>
      rw [cls, evalCNF_append, ih]
      simp only [evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, canon_gv, BoolExpr.eval]
      cases BoolExpr.eval σ a <;> simp
  | conj a b iha ihb =>
      rw [cls, evalCNF_append, evalCNF_append, iha, ihb]
      simp only [evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, canon_gv, BoolExpr.eval]
      cases BoolExpr.eval σ a <;> cases BoolExpr.eval σ b <;> simp
  | disj a b iha ihb =>
      rw [cls, evalCNF_append, evalCNF_append, iha, ihb]
      simp only [evalCNF, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, canon_gv, BoolExpr.eval]
      cases BoolExpr.eval σ a <;> cases BoolExpr.eval σ b <;> simp

/-- **Tseitin correctness**: a boolean expression is satisfiable iff the CNF formula
produced from it by the Tseitin transformation is satisfiable. -/
theorem tseitin_correct (e : BoolExpr) :
    Satisfiable (toCNF e) ↔ ∃ σ : Nat → Bool, BoolExpr.eval σ e = true := by
  constructor
  · rintro ⟨τ, hτ⟩
    rw [toCNF, evalCNF_append] at hτ
    simp only [Bool.and_eq_true] at hτ
    refine ⟨fun i => τ (xv i), ?_⟩
    rw [← cls_sound τ e hτ.1]
    have h2 := hτ.2
    simpa [evalCNF, evalClause, evalLit] using h2
  · rintro ⟨σ, hσ⟩
    refine ⟨canon σ, ?_⟩
    rw [toCNF, evalCNF_append, cls_complete σ e]
    simp [evalCNF, evalClause, evalLit, canon_gv, hσ]

/-- The Tseitin transformation produces a CNF formula of linear size. -/
theorem toCNF_length_le (e : BoolExpr) : (toCNF e).length ≤ 3 * e.size + 1 := by
  have key : ∀ e' : BoolExpr, (cls e').length ≤ 3 * e'.size := by
    intro e'
    induction e' with
    | var i => simp [cls, BoolExpr.size]
    | tru => simp [cls, BoolExpr.size]
    | fls => simp [cls, BoolExpr.size]
    | neg a ih => simp only [cls, BoolExpr.size, List.length_append] at ih ⊢; simp at ih ⊢; omega
    | conj a b iha ihb =>
        simp only [cls, BoolExpr.size, List.length_append] at iha ihb ⊢; simp at iha ihb ⊢; omega
    | disj a b iha ihb =>
        simp only [cls, BoolExpr.size, List.length_append] at iha ihb ⊢; simp at iha ihb ⊢; omega
  have h := key e
  simp only [toCNF, List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## Short witnesses for SAT -/

/-- An upper bound (exclusive) for the variables occurring in a clause. -/
def clauseBound (c : Clause) : Nat := c.foldr (fun l b => max b (l.1 + 1)) 0

/-- An upper bound (exclusive) for the variables occurring in a CNF formula. -/
def varBound (φ : CNF) : Nat := φ.foldr (fun c a => max a (clauseBound c)) 0

/-- The assignment described by a list of bits (missing bits are `false`). -/
def listAssign (w : List Bool) : Nat → Bool := fun i => w.getD i false

theorem getD_of_lt (w : List Bool) (i : Nat) (h : i < w.length) : w.getD i false = w[i] :=
  (List.getElem_eq_getD false).symm

theorem getD_of_le (w : List Bool) (i : Nat) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none h]

theorem evalClause_congr (σ σ' : Nat → Bool) (c : Clause)
    (h : ∀ i, i < clauseBound c → σ i = σ' i) : evalClause σ c = evalClause σ' c := by
  induction c with
  | nil => rfl
  | cons l t ih =>
      have hb : clauseBound (l :: t) = max (clauseBound t) (l.1 + 1) := rfl
      have hl : σ l.1 = σ' l.1 := h l.1 (by rw [hb]; omega)
      have ht : evalClause σ t = evalClause σ' t := by
        refine ih (fun i hi => h i ?_)
        rw [hb]; omega
      simp only [evalClause, List.any_cons, evalLit, hl] at ht ⊢
      rw [ht]

theorem evalCNF_congr (σ σ' : Nat → Bool) (φ : CNF)
    (h : ∀ i, i < varBound φ → σ i = σ' i) : evalCNF σ φ = evalCNF σ' φ := by
  induction φ with
  | nil => rfl
  | cons c t ih =>
      have hb : varBound (c :: t) = max (varBound t) (clauseBound c) := rfl
      have hc : evalClause σ c = evalClause σ' c := by
        refine evalClause_congr _ _ _ (fun i hi => h i ?_)
        rw [hb]; omega
      have ht : evalCNF σ t = evalCNF σ' t := by
        refine ih (fun i hi => h i ?_)
        rw [hb]; omega
      simp only [evalCNF, List.all_cons] at ht ⊢
      rw [hc, ht]

theorem listAssign_range_map (σ : Nat → Bool) (n i : Nat) (hi : i < n) :
    listAssign ((List.range n).map σ) i = σ i := by
  have hlen : ((List.range n).map σ).length = n := by simp
  have h : i < ((List.range n).map σ).length := by omega
  rw [listAssign, getD_of_lt _ _ h]
  simp

/-- **SAT has short, efficiently checkable witnesses** (the "SAT ∈ NP" half):
a CNF formula is satisfiable iff it is satisfied by the assignment given by some
bit string whose length is the number of variables of the formula.  Checking a
candidate bit string is the evaluation `evalCNF`, a linear-time computation. -/
theorem sat_short_witness (φ : CNF) :
    Satisfiable φ ↔ ∃ w : List Bool, w.length = varBound φ ∧ evalCNF (listAssign w) φ = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range (varBound φ)).map σ, by simp, ?_⟩
    rw [evalCNF_congr _ σ φ (fun i hi => listAssign_range_map σ _ i hi)]
    exact hσ
  · rintro ⟨w, _, hw⟩
    exact ⟨listAssign w, hw⟩

/-! ## NP and the reduction to SAT -/

/-- The assignment used by a verifier circuit on input `x` and witness `w`:
variables `0, …, |x| - 1` carry the input, later variables carry the witness. -/
def inputAssign (x w : List Bool) : Nat → Bool := fun i =>
  if i < x.length then x.getD i false else w.getD (i - x.length) false

/-- A language of bit strings is in `NP` when membership is certified by witnesses
of polynomially bounded length, checked by a family of polynomial-size boolean
circuits. -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (V : Nat → BoolExpr) (c k : Nat),
    (∀ n, (V n).size ≤ c * (n + 1) ^ k) ∧
    ∀ x : List Bool, L x ↔ ∃ w : List Bool,
      w.length ≤ c * (x.length + 1) ^ k ∧
        BoolExpr.eval (inputAssign x w) (V x.length) = true

/-- Hard-wire the input `x` into a verifier circuit, and restrict the witness
variables to the first `B` of them. -/
def fixInput (x : List Bool) (B : Nat) (e : BoolExpr) : BoolExpr :=
  BoolExpr.subst (fun i =>
    if i < x.length then (if x.getD i false then BoolExpr.tru else BoolExpr.fls)
    else if i - x.length < B then BoolExpr.var (i - x.length) else BoolExpr.fls) e

theorem eval_fixInput (x : List Bool) (B : Nat) (e : BoolExpr) (σ : Nat → Bool) :
    BoolExpr.eval σ (fixInput x B e)
      = BoolExpr.eval (inputAssign x ((List.range B).map σ)) e := by
  rw [fixInput, BoolExpr.eval_subst]
  congr 1
  funext i
  by_cases hi : i < x.length
  · simp only [if_pos hi, inputAssign]
    cases hx : x.getD i false <;> simp [BoolExpr.eval]
  · by_cases hB : i - x.length < B
    · have hval : listAssign ((List.range B).map σ) (i - x.length) = σ (i - x.length) :=
        listAssign_range_map σ B _ hB
      simp only [hi, hB, if_false, if_true, inputAssign, BoolExpr.eval]
      simpa [listAssign] using hval.symm
    · have hlen : ((List.range B).map σ).length = B := by simp
      have hz : ((List.range B).map σ).getD (i - x.length) false = false := by
        refine getD_of_le _ _ ?_
        omega
      simp only [hi, hB, if_false, inputAssign, BoolExpr.eval, hz]

theorem size_fixInput (x : List Bool) (B : Nat) (e : BoolExpr) :
    (fixInput x B e).size = e.size := by
  refine BoolExpr.size_subst _ (fun i => ?_) e
  by_cases hi : i < x.length
  · simp only [if_pos hi]
    cases hx : x.getD i false <;> simp [BoolExpr.size]
  · by_cases hB : i - x.length < B <;> simp [hi, hB, BoolExpr.size]

theorem one_le_pow_succ (n k : Nat) : 1 ≤ (n + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

/-- **SAT is NP-hard**: every language in NP reduces to SAT by a map producing
CNF formulas of polynomial size. -/
theorem sat_np_hard (L : List Bool → Prop) (hL : InNP L) :
    ∃ f : List Bool → CNF,
      (∃ c k : Nat, ∀ x : List Bool, (f x).length ≤ c * (x.length + 1) ^ k) ∧
      (∀ x : List Bool, L x ↔ Satisfiable (f x)) := by
  obtain ⟨V, c, k, hsize, hL⟩ := hL
  refine ⟨fun x => toCNF (fixInput x (c * (x.length + 1) ^ k) (V x.length)), ?_, ?_⟩
  · refine ⟨3 * c + 1, k, fun x => ?_⟩
    show (toCNF (fixInput x (c * (x.length + 1) ^ k) (V x.length))).length
        ≤ (3 * c + 1) * (x.length + 1) ^ k
    have h1 := toCNF_length_le (fixInput x (c * (x.length + 1) ^ k) (V x.length))
    rw [size_fixInput] at h1
    have h2 := hsize x.length
    have h4 : 1 ≤ (x.length + 1) ^ k := one_le_pow_succ _ _
    have hid : (3 * c + 1) * (x.length + 1) ^ k
        = 3 * (c * (x.length + 1) ^ k) + (x.length + 1) ^ k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    refine Nat.le_trans h1 ?_
    rw [hid]
    have h5 : 3 * (V x.length).size ≤ 3 * (c * (x.length + 1) ^ k) :=
      Nat.mul_le_mul (Nat.le_refl 3) h2
    omega
  · intro x
    rw [tseitin_correct, hL x]
    constructor
    · rintro ⟨w, hwlen, hw⟩
      refine ⟨listAssign w, ?_⟩
      rw [eval_fixInput]
      have hfun : inputAssign x ((List.range (c * (x.length + 1) ^ k)).map (listAssign w))
          = inputAssign x w := by
        funext i
        by_cases hi : i < x.length
        · simp [inputAssign, hi]
        · by_cases hlt : i - x.length < c * (x.length + 1) ^ k
          · have hval := listAssign_range_map (listAssign w) (c * (x.length + 1) ^ k) _ hlt
            simp only [inputAssign, if_neg hi]
            simpa [listAssign] using hval
          · have h1 : ((List.range (c * (x.length + 1) ^ k)).map
                (listAssign w)).getD (i - x.length) false = false := by
              refine getD_of_le _ _ ?_
              simp only [List.length_map, List.length_range]
              omega
            have h2 : w.getD (i - x.length) false = false := by
              refine getD_of_le _ _ ?_
              omega
            simp only [inputAssign, if_neg hi, h1, h2]
      rw [hfun]
      exact hw
    · rintro ⟨σ, hσ⟩
      rw [eval_fixInput] at hσ
      exact ⟨(List.range (c * (x.length + 1) ^ k)).map σ, by simp, hσ⟩

/-! ## A sanity check: the class `InNP` is inhabited by a nontrivial language -/

/-- The language of bit strings whose first bit is `true` lies in `NP`
(no witness is needed), so the hardness statement below is not vacuous. -/
example : InNP (fun x : List Bool => x ≠ [] ∧ x.getD 0 false = true) := by
  refine ⟨fun n => if n = 0 then BoolExpr.fls else BoolExpr.var 0, 1, 0, fun n => ?_, fun x => ?_⟩
  · by_cases hn : n = 0 <;> simp [hn, BoolExpr.size]
  · constructor
    · rintro ⟨hne, h0⟩
      have hlen : x.length ≠ 0 := by
        intro h
        exact hne (List.eq_nil_of_length_eq_zero h)
      have hpos : 0 < x.length := by omega
      refine ⟨[], by simp, ?_⟩
      simp only [hlen, if_false, BoolExpr.eval, inputAssign, if_pos hpos]
      exact h0
    · rintro ⟨w, -, hw⟩
      by_cases hlen : x.length = 0
      · rw [hlen] at hw
        simp [BoolExpr.eval] at hw
      · have hpos : 0 < x.length := by omega
        refine ⟨fun h => hlen (by rw [h]; rfl), ?_⟩
        simp only [hlen, if_false, BoolExpr.eval, inputAssign, if_pos hpos] at hw
        exact hw

/-! ## The Cook–Levin theorem -/

/-- **Cook–Levin**: SAT is NP-complete.

The first conjunct is the membership half: satisfiability of a CNF formula is
certified by a bit string of length the number of variables of the formula, and
the certificate is checked by the (linear-time) evaluation `evalCNF`.

The second conjunct is the hardness half: every language in `NP` — that is, every
language whose membership is certified by polynomially long witnesses checked by
a family of polynomial-size boolean circuits — is reduced to SAT by a map sending
an input `x` to a CNF formula of size polynomial in `|x|` which is satisfiable
exactly when `x` belongs to the language.

Here `NP` is modelled by verification with polynomial-size boolean circuits, and
the reduction is a map whose output size is polynomially bounded; the reduction
is obtained by hard-wiring the input into the verifier circuit and applying the
Tseitin transformation (`tseitin_correct`). -/
theorem cook_levin :
    (∀ φ : CNF, Satisfiable φ ↔
        ∃ w : List Bool, w.length = varBound φ ∧ evalCNF (listAssign w) φ = true) ∧
    (∀ L : List Bool → Prop, InNP L →
      ∃ f : List Bool → CNF,
        (∃ c k : Nat, ∀ x : List Bool, (f x).length ≤ c * (x.length + 1) ^ k) ∧
        (∀ x : List Bool, L x ↔ Satisfiable (f x))) :=
  ⟨sat_short_witness, sat_np_hard⟩

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

