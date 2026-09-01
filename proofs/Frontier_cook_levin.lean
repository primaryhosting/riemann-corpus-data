/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

/-! ## CNF formulas -/

/-- A literal: a variable index together with a sign (`true` = positive). -/
abbrev Lit : Type := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause : Type := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- Value of a literal under an assignment. -/
def litEval (a : ℕ → Bool) (l : Lit) : Bool := if l.2 then a l.1 else !(a l.1)

/-- Value of a clause (disjunction). -/
def clauseEval (a : ℕ → Bool) (c : Clause) : Bool := c.any (litEval a)

/-- Value of a CNF formula (conjunction). -/
def cnfEval (a : ℕ → Bool) (f : CNF) : Bool := f.all (clauseEval a)

/-- Satisfiability of a CNF formula. -/
def Satisfiable (f : CNF) : Prop := ∃ a : ℕ → Bool, cnfEval a f = true

/-! ## Boolean circuits as straight-line programs -/

/-- A single gate of a straight-line Boolean program.  Gates refer to previously
computed gates by their absolute position in the program; a reference to a
position that has not been computed yet evaluates to `false`. -/
inductive Gate : Type
  | inp (i : ℕ) : Gate
  | cst (b : Bool) : Gate
  | neg (j : ℕ) : Gate
  | conj (j k : ℕ) : Gate
  | disj (j k : ℕ) : Gate
  deriving DecidableEq, Inhabited

/-- Value of a gate given the input assignment `x` and the list `vs` of values of
the gates computed so far. -/
def gateVal (x : ℕ → Bool) (vs : List Bool) : Gate → Bool
  | .inp i => x i
  | .cst b => b
  | .neg j => !(vs.getD j false)
  | .conj j k => (vs.getD j false) && (vs.getD k false)
  | .disj j k => (vs.getD j false) || (vs.getD k false)

/-- Running the gates of a program, accumulating the list of computed values. -/
def evalAux (x : ℕ → Bool) : List Gate → List Bool → List Bool
  | [], vs => vs
  | g :: gs, vs => evalAux x gs (vs ++ [gateVal x vs g])

/-- The list of all gate values of a program. -/
def vals (p : List Gate) (x : ℕ → Bool) : List Bool := evalAux x p []

/-- The output of a program is the value of its last gate. -/
def evalProg (p : List Gate) (x : ℕ → Bool) : Bool := (vals p x).getD (p.length - 1) false

/-! ### Basic lemmas about program evaluation -/

theorem evalAux_append (x : ℕ → Bool) (p q : List Gate) (vs : List Bool) :
    evalAux x (p ++ q) vs = evalAux x q (evalAux x p vs) := by
  induction p generalizing vs with
  | nil => simp [evalAux]
  | cons g gs ih => simp [evalAux, ih]

theorem evalAux_length (x : ℕ → Bool) (p : List Gate) (vs : List Bool) :
    (evalAux x p vs).length = vs.length + p.length := by
  induction p generalizing vs with
  | nil => simp [evalAux]
  | cons g gs ih => simp [evalAux, ih]; omega

theorem evalAux_prefix (x : ℕ → Bool) (p : List Gate) (vs : List Bool) :
    vs <+: evalAux x p vs := by
  induction p generalizing vs with
  | nil => simp [evalAux]
  | cons g gs ih =>
      exact (List.prefix_append vs [gateVal x vs g]).trans (ih _)

theorem vals_length (p : List Gate) (x : ℕ → Bool) : (vals p x).length = p.length := by
  simp [vals, evalAux_length]

theorem getD_of_prefix {vs ws : List Bool} (h : vs <+: ws) {k : ℕ} (hk : k < vs.length) :
    ws.getD k false = vs.getD k false := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append vs t false k hk

/-! ## Composition of programs -/

/-- Shift all gate references in a gate by `d`. -/
def shiftGate (d : ℕ) : Gate → Gate
  | .inp i => .inp i
  | .cst b => .cst b
  | .neg j => .neg (j + d)
  | .conj j k => .conj (j + d) (k + d)
  | .disj j k => .disj (j + d) (k + d)

theorem gateVal_shift (x : ℕ → Bool) (vs ws : List Bool) (g : Gate) :
    gateVal x (vs ++ ws) (shiftGate vs.length g) = gateVal x ws g := by
  cases g <;>
    simp [gateVal, shiftGate, List.getD, List.getElem?_append_right]

theorem evalAux_map_shift (x : ℕ → Bool) (q : List Gate) (vs ws : List Bool) :
    evalAux x (q.map (shiftGate vs.length)) (vs ++ ws) = vs ++ evalAux x q ws := by
  induction q generalizing ws with
  | nil => simp [evalAux]
  | cons g gs ih =>
      simp only [List.map_cons, evalAux, gateVal_shift]
      rw [List.append_assoc]
      exact ih _

/-- Combine two programs with a binary gate. -/
def comb (op : ℕ → ℕ → Gate) (p q : List Gate) : List Gate :=
  p ++ q.map (shiftGate p.length) ++ [op (p.length - 1) (p.length + q.length - 1)]

theorem vals_comb (op : ℕ → ℕ → Gate) (p q : List Gate) (x : ℕ → Bool) :
    vals (comb op p q) x =
      (vals p x ++ vals q x) ++
        [gateVal x (vals p x ++ vals q x) (op (p.length - 1) (p.length + q.length - 1))] := by
  have h1 : vals (p ++ q.map (shiftGate p.length)) x = vals p x ++ vals q x := by
    have := evalAux_map_shift x q (vals p x) []
    simp only [vals] at *
    rw [evalAux_append]
    rw [show (evalAux x p [] : List Bool) = evalAux x p [] ++ [] by simp] at *
    simpa [vals_length, evalAux_length] using this
  simp only [comb, vals] at *
  rw [evalAux_append, h1]
  simp [evalAux]

/-! ## Tseitin transformation -/

/-- CNF variable holding the value of program input `i`. -/
def xvar (i : ℕ) : ℕ := 2 * i + 2

/-- CNF variable holding the value of gate `j`. -/
def gvar (j : ℕ) : ℕ := 2 * j + 3

/-- Literal for the reference to gate `k` from position `j`; an out-of-range
reference uses the designated always-false variable `0`. -/
def refLit (j k : ℕ) (b : Bool) : Lit := if k < j then (gvar k, b) else (0, b)

/-- The defining clauses of the gate at position `j`. -/
def gateClauses (j : ℕ) : Gate → CNF
  | .inp i => [[(gvar j, false), (xvar i, true)], [(gvar j, true), (xvar i, false)]]
  | .cst b => if b then [[(gvar j, true)]] else [[(gvar j, false)]]
  | .neg k => [[(gvar j, false), refLit j k false], [(gvar j, true), refLit j k true]]
  | .conj k l =>
      [[(gvar j, false), refLit j k true], [(gvar j, false), refLit j l true],
       [(gvar j, true), refLit j k false, refLit j l false]]
  | .disj k l =>
      [[(gvar j, true), refLit j k false], [(gvar j, true), refLit j l false],
       [(gvar j, false), refLit j k true, refLit j l true]]

/-- The Tseitin CNF encoding of a straight-line program: it is satisfiable iff
the program outputs `true` on some input. -/
def tseitin (p : List Gate) : CNF :=
  [(0, false)] :: [(gvar (p.length - 1), true)] ::
    ((if p.isEmpty then [([] : Clause)] else []) ++
      (List.range p.length).flatMap (fun j => gateClauses j (p.getD j (.cst false))))

/-! ## Substituting the instance bits into a verifier program -/

/-- Replace the first `n` inputs by the constants `x`, renaming the remaining
inputs down by `n`. -/
def substGate (n : ℕ) (x : Fin n → Bool) : Gate → Gate
  | .inp i => if h : i < n then .cst (x ⟨i, h⟩) else .inp (i - n)
  | g => g

/-! ## Circuits checking a CNF assignment -/

/-- Program computing the value of a literal. -/
def litProg (l : Lit) : List Gate :=
  if l.2 then [.inp l.1] else [.inp l.1, .neg 0]

/-- Program computing the value of a clause. -/
def clauseProg : Clause → List Gate
  | [] => [.cst false]
  | l :: c => comb Gate.disj (litProg l) (clauseProg c)

/-- Program computing the value of a CNF formula. -/
def cnfProg : CNF → List Gate
  | [] => [.cst true]
  | c :: f => comb Gate.conj (clauseProg c) (cnfProg f)

/-! ## Languages and NP certificates -/

/-- A language: for every length `n`, a predicate on `n`-bit strings. -/
def Language : Type := (n : ℕ) → (Fin n → Bool) → Prop

/-- A certificate that a language is in NP: a polynomial-size family of
straight-line Boolean verifier programs.  Inputs `0, …, n-1` of `prog n` receive
the instance bits, the remaining inputs receive the witness bits. -/
structure NPCert (L : Language) : Type where
  prog : ℕ → List Gate
  bnd : ℕ
  deg : ℕ
  size_le : ∀ n, (prog n).length ≤ bnd * (n + 1) ^ deg
  spec : ∀ (n : ℕ) (x : Fin n → Bool), L n x ↔
    ∃ w : ℕ → Bool,
      evalProg (prog n) (fun i => if h : i < n then x ⟨i, h⟩ else w (i - n)) = true

/-! ### Helper lemmas -/

theorem getD_append_add (vs ws : List Bool) (k : ℕ) :
    (vs ++ ws).getD (vs.length + k) false = ws.getD k false := by
  simp [List.getD, List.getElem?_append_right]

theorem sum_le_of_forall_le (l : List ℕ) (n : ℕ) (h : ∀ x ∈ l, x ≤ n) : l.sum ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.sum_cons, List.length_cons]
      have h1 := h a (by simp)
      have h2 := ih (fun x hx => h x (by simp [hx]))
      nlinarith [h2]

theorem comb_length (op : ℕ → ℕ → Gate) (p q : List Gate) :
    (comb op p q).length = p.length + q.length + 1 := by
  simp [comb]; omega

theorem comb_ne_nil (op : ℕ → ℕ → Gate) (p q : List Gate) : comb op p q ≠ [] := by
  intro h
  have := comb_length op p q
  rw [h] at this
  simp at this

theorem evalProg_comb (op : ℕ → ℕ → Gate) (p q : List Gate) (x : ℕ → Bool) :
    evalProg (comb op p q) x =
      gateVal x (vals p x ++ vals q x) (op (p.length - 1) (p.length + q.length - 1)) := by
  have hlen : (vals p x ++ vals q x).length = p.length + q.length := by
    simp [vals_length]
  rw [evalProg, vals_comb, comb_length]
  have : p.length + q.length + 1 - 1 = (vals p x ++ vals q x).length + 0 := by
    simp [hlen]
  rw [this, getD_append_add]
  simp

theorem evalProg_comb_disj (p q : List Gate) (x : ℕ → Bool) (hp : p ≠ []) (hq : q ≠ []) :
    evalProg (comb Gate.disj p q) x = (evalProg p x || evalProg q x) := by
  have hp' : 0 < p.length := List.length_pos_iff.2 hp
  have hq' : 0 < q.length := List.length_pos_iff.2 hq
  rw [evalProg_comb]
  have e1 : (vals p x ++ vals q x).getD (p.length - 1) false = evalProg p x := by
    rw [List.getD_append _ _ _ _ (by rw [vals_length]; omega)]
    rfl
  have e2 : (vals p x ++ vals q x).getD (p.length + q.length - 1) false = evalProg q x := by
    have : p.length + q.length - 1 = (vals p x).length + (q.length - 1) := by
      rw [vals_length]; omega
    rw [this, getD_append_add]
    rfl
  simp only [gateVal, e1, e2]

theorem evalProg_comb_conj (p q : List Gate) (x : ℕ → Bool) (hp : p ≠ []) (hq : q ≠ []) :
    evalProg (comb Gate.conj p q) x = (evalProg p x && evalProg q x) := by
  have hp' : 0 < p.length := List.length_pos_iff.2 hp
  have hq' : 0 < q.length := List.length_pos_iff.2 hq
  rw [evalProg_comb]
  have e1 : (vals p x ++ vals q x).getD (p.length - 1) false = evalProg p x := by
    rw [List.getD_append _ _ _ _ (by rw [vals_length]; omega)]
    rfl
  have e2 : (vals p x ++ vals q x).getD (p.length + q.length - 1) false = evalProg q x := by
    have : p.length + q.length - 1 = (vals p x).length + (q.length - 1) := by
      rw [vals_length]; omega
    rw [this, getD_append_add]
    rfl
  simp only [gateVal, e1, e2]

theorem litProg_ne_nil (l : Lit) : litProg l ≠ [] := by
  unfold litProg; split <;> simp

theorem clauseProg_ne_nil (c : Clause) : clauseProg c ≠ [] := by
  cases c with
  | nil => simp [clauseProg]
  | cons l c => exact comb_ne_nil _ _ _

theorem cnfProg_ne_nil (f : CNF) : cnfProg f ≠ [] := by
  cases f with
  | nil => simp [cnfProg]
  | cons c f => exact comb_ne_nil _ _ _

theorem litProg_correct (l : Lit) (a : ℕ → Bool) : evalProg (litProg l) a = litEval a l := by
  unfold litProg litEval
  cases hl : l.2 with
  | true => simp [evalProg, vals, evalAux, gateVal]
  | false => simp [evalProg, vals, evalAux, gateVal, List.getD]

theorem clauseProg_correct (c : Clause) (a : ℕ → Bool) :
    evalProg (clauseProg c) a = clauseEval a c := by
  induction c with
  | nil => simp [clauseProg, clauseEval, evalProg, vals, evalAux, gateVal]
  | cons l c ih =>
      rw [clauseProg, evalProg_comb_disj _ _ _ (litProg_ne_nil l) (clauseProg_ne_nil c),
        litProg_correct, ih]
      simp [clauseEval]

/-! ## Main lemmas -/

/-- Gate value in terms of an abstract function giving the referenced values. -/
def gateValR (x : ℕ → Bool) (r : ℕ → Bool) : Gate → Bool
  | .inp i => x i
  | .cst b => b
  | .neg j => !(r j)
  | .conj j k => (r j) && (r k)
  | .disj j k => (r j) || (r k)

theorem gateVal_eq_gateValR (x : ℕ → Bool) (vs : List Bool) (g : Gate) :
    gateVal x vs g = gateValR x (fun k => vs.getD k false) g := by
  cases g <;> rfl

theorem vals_take_prefix (p : List Gate) (x : ℕ → Bool) (j : ℕ) :
    vals (p.take j) x <+: vals p x := by
  have h : p = p.take j ++ p.drop j := (List.take_append_drop j p).symm
  conv_rhs => rw [vals, h, evalAux_append]
  exact evalAux_prefix x (p.drop j) (vals (p.take j) x)

theorem vals_take_getD (p : List Gate) (x : ℕ → Bool) {j : ℕ} (hj : j ≤ p.length) (k : ℕ) :
    (vals (p.take j) x).getD k false = if k < j then (vals p x).getD k false else false := by
  have hlen : (vals (p.take j) x).length = j := by
    rw [vals_length, List.length_take]; omega
  by_cases hk : k < j
  · rw [if_pos hk]
    exact (getD_of_prefix (vals_take_prefix p x j) (by omega)).symm
  · rw [if_neg hk]
    exact List.getD_eq_default _ false (by omega)

theorem getD_append_singleton (L : List Bool) (b : Bool) (j : ℕ) (h : L.length = j) :
    (L ++ [b]).getD j false = b := by
  subst h
  simp

theorem vals_getD_step (p : List Gate) (x : ℕ → Bool) {j : ℕ} (hj : j < p.length) :
    (vals p x).getD j false =
      gateVal x (vals (p.take j) x) (p.getD j (.cst false)) := by
  have hlen : (vals (p.take j) x).length = j := by
    rw [vals_length, List.length_take]; omega
  have hd : p.drop j = p.getD j (.cst false) :: p.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem p (.cst false) hj]
  have hsplit : vals p x =
      evalAux x (p.drop (j + 1))
        (vals (p.take j) x ++ [gateVal x (vals (p.take j) x) (p.getD j (.cst false))]) := by
    have h : p = p.take j ++ p.drop j := (List.take_append_drop j p).symm
    simp only [vals]
    conv_lhs => rw [h]
    rw [evalAux_append, hd]
    simp only [evalAux]
  have hpref := evalAux_prefix x (p.drop (j + 1))
      (vals (p.take j) x ++ [gateVal x (vals (p.take j) x) (p.getD j (.cst false))])
  rw [← hsplit] at hpref
  rw [getD_of_prefix hpref (k := j) (by simp [hlen])]
  exact getD_append_singleton _ _ _ hlen

theorem refLit_eval_true (a : ℕ → Bool) (j : ℕ) (R : ℕ → Bool) (hzero : a 0 = false)
    (h1 : ∀ k, k < j → a (gvar k) = R k) (h2 : ∀ k, j ≤ k → R k = false) (k : ℕ) :
    litEval a (refLit j k true) = R k := by
  by_cases hk : k < j
  · simp [refLit, litEval, hk, h1 k hk]
  · have hR : R k = false := h2 k (by omega)
    simp [refLit, litEval, hk, hzero, hR]

theorem refLit_eval_false (a : ℕ → Bool) (j : ℕ) (R : ℕ → Bool) (hzero : a 0 = false)
    (h1 : ∀ k, k < j → a (gvar k) = R k) (h2 : ∀ k, j ≤ k → R k = false) (k : ℕ) :
    litEval a (refLit j k false) = !(R k) := by
  by_cases hk : k < j
  · simp [refLit, litEval, hk, h1 k hk]
  · have hR : R k = false := h2 k (by omega)
    simp [refLit, litEval, hk, hzero, hR]

theorem gateClauses_true_iff (a : ℕ → Bool) (j : ℕ) (g : Gate) (X R : ℕ → Bool)
    (hX : ∀ i, a (xvar i) = X i)
    (hrefT : ∀ k, litEval a (refLit j k true) = R k)
    (hrefF : ∀ k, litEval a (refLit j k false) = !(R k)) :
    (∀ c ∈ gateClauses j g, clauseEval a c = true) ↔ a (gvar j) = gateValR X R g := by
  have hgT : litEval a ((gvar j, true) : Lit) = a (gvar j) := by simp [litEval]
  have hgF : litEval a ((gvar j, false) : Lit) = !(a (gvar j)) := by simp [litEval]
  have hXT : ∀ i, litEval a ((xvar i, true) : Lit) = X i := by
    intro i; simp [litEval, hX]
  have hXF : ∀ i, litEval a ((xvar i, false) : Lit) = !(X i) := by
    intro i; simp [litEval, hX]
  cases g with
  | inp i =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hXT, hXF, hgT, hgF,
        Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : X i <;> simp_all
  | cst b =>
      cases b <;>
        (simp only [gateClauses, gateValR, if_true, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq, clauseEval, List.any_cons, List.any_nil, hgT,
          Bool.or_false]
         try simp_all)
  | neg k =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hrefT, hrefF,
        hgT, hgF, Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : R k <;> simp_all
  | conj k l =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hrefT, hrefF,
        hgT, hgF, Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : R k <;> cases h3 : R l <;> simp_all
  | disj k l =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hrefT, hrefF,
        hgT, hgF, Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : R k <;> cases h3 : R l <;> simp_all

theorem mem_tseitin_of_gateClauses (p : List Gate) (j : ℕ) (hj : j < p.length) (c : Clause)
    (hc : c ∈ gateClauses j (p.getD j (.cst false))) : c ∈ tseitin p := by
  simp only [tseitin, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr (Or.inr (Or.inr ⟨j, hj, hc⟩))

/-- The canonical satisfying assignment built from an input of the program. -/
def tseitinAssign (p : List Gate) (x : ℕ → Bool) : ℕ → Bool := fun v =>
  if v = 0 then false else if v % 2 = 0 then x ((v - 2) / 2)
  else (vals p x).getD ((v - 3) / 2) false

theorem tseitinAssign_zero (p : List Gate) (x : ℕ → Bool) : tseitinAssign p x 0 = false := rfl

theorem tseitinAssign_xvar (p : List Gate) (x : ℕ → Bool) (i : ℕ) :
    tseitinAssign p x (xvar i) = x i := by
  have h0 : ¬ (xvar i = 0) := by unfold xvar; omega
  have h1 : xvar i % 2 = 0 := by unfold xvar; omega
  have h2 : (xvar i - 2) / 2 = i := by unfold xvar; omega
  simp only [tseitinAssign, if_neg h0, if_pos h1, h2]

theorem tseitinAssign_gvar (p : List Gate) (x : ℕ → Bool) (j : ℕ) :
    tseitinAssign p x (gvar j) = (vals p x).getD j false := by
  have h0 : ¬ (gvar j = 0) := by unfold gvar; omega
  have h1 : ¬ (gvar j % 2 = 0) := by unfold gvar; omega
  have h2 : (gvar j - 3) / 2 = j := by unfold gvar; omega
  simp only [tseitinAssign, if_neg h0, if_neg h1, h2]

theorem tseitin_sat_iff (p : List Gate) :
    Satisfiable (tseitin p) ↔ ∃ x : ℕ → Bool, evalProg p x = true := by
  constructor
  · rintro ⟨a, ha⟩
    simp only [cnfEval, List.all_eq_true] at ha
    have hzero : a 0 = false := by
      have h := ha [(0, false)] (by simp [tseitin])
      simpa [clauseEval, litEval] using h
    have hne : p ≠ [] := by
      intro h
      subst h
      have h2 := ha [] (by simp [tseitin])
      simp [clauseEval] at h2
    refine ⟨fun i => a (xvar i), ?_⟩
    have key : ∀ j, j < p.length → a (gvar j) = (vals p (fun i => a (xvar i))).getD j false := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj
        have hR2 : ∀ k, j ≤ k →
            (vals (p.take j) (fun i => a (xvar i))).getD k false = false := by
          intro k hk
          rw [vals_take_getD p _ (le_of_lt hj) k, if_neg (by omega)]
        have hR1 : ∀ k, k < j →
            a (gvar k) = (vals (p.take j) (fun i => a (xvar i))).getD k false := by
          intro k hk
          rw [vals_take_getD p _ (le_of_lt hj) k, if_pos hk]
          exact ih k hk (by omega)
        have hgc : ∀ c ∈ gateClauses j (p.getD j (.cst false)), clauseEval a c = true :=
          fun c hc => ha c (mem_tseitin_of_gateClauses p j hj c hc)
        have hmain := (gateClauses_true_iff a j (p.getD j (.cst false)) (fun i => a (xvar i))
          (fun k => (vals (p.take j) (fun i => a (xvar i))).getD k false) (fun _ => rfl)
          (refLit_eval_true a j _ hzero hR1 hR2) (refLit_eval_false a j _ hzero hR1 hR2)).1 hgc
        rw [vals_getD_step p _ hj, gateVal_eq_gateValR]
        exact hmain
    have hout := ha [(gvar (p.length - 1), true)] (by simp [tseitin])
    have h2 : a (gvar (p.length - 1)) = true := by
      simpa [clauseEval, litEval] using hout
    have hlen : p.length - 1 < p.length := by
      have : 0 < p.length := List.length_pos_iff.2 hne
      omega
    rw [evalProg, ← key _ hlen]
    exact h2
  · rintro ⟨x, hx⟩
    have hne : p ≠ [] := by
      intro h
      subst h
      simp [evalProg, vals, evalAux] at hx
    refine ⟨tseitinAssign p x, ?_⟩
    simp only [cnfEval, List.all_eq_true]
    intro c hc
    simp only [tseitin, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range] at hc
    rcases hc with rfl | rfl | hc | ⟨j, hj, hjc⟩
    · simp [clauseEval, litEval, tseitinAssign_zero]
    · have : tseitinAssign p x (gvar (p.length - 1)) = true := by
        rw [tseitinAssign_gvar]
        exact hx
      simp [clauseEval, litEval, this]
    · rw [if_neg (by simp [List.isEmpty_iff, hne])] at hc
      simp at hc
    · have hR2 : ∀ k, j ≤ k → (vals (p.take j) x).getD k false = false := by
        intro k hk
        rw [vals_take_getD p x (le_of_lt hj) k, if_neg (by omega)]
      have hR1 : ∀ k, k < j → tseitinAssign p x (gvar k) = (vals (p.take j) x).getD k false := by
        intro k hk
        rw [tseitinAssign_gvar, vals_take_getD p x (le_of_lt hj) k, if_pos hk]
      refine (gateClauses_true_iff (tseitinAssign p x) j (p.getD j (.cst false)) x
        (fun k => (vals (p.take j) x).getD k false) (tseitinAssign_xvar p x)
        (refLit_eval_true _ j _ (tseitinAssign_zero p x) hR1 hR2)
        (refLit_eval_false _ j _ (tseitinAssign_zero p x) hR1 hR2)).2 ?_ c hjc
      rw [tseitinAssign_gvar, vals_getD_step p x hj, gateVal_eq_gateValR]

theorem gateClauses_card (j : ℕ) (g : Gate) : (gateClauses j g).length ≤ 3 := by
  cases g with
  | cst b => cases b <;> simp [gateClauses]
  | _ => simp [gateClauses]

theorem gateClauses_clause_length (j : ℕ) (g : Gate) (c : Clause) (hc : c ∈ gateClauses j g) :
    c.length ≤ 3 := by
  cases g with
  | inp i => simp [gateClauses] at hc; rcases hc with h | h <;> subst h <;> simp
  | cst b => cases b <;> (simp [gateClauses] at hc; subst hc; simp)
  | neg k => simp [gateClauses] at hc; rcases hc with h | h <;> subst h <;> simp
  | conj k l => simp [gateClauses] at hc; rcases hc with h | h | h <;> subst h <;> simp
  | disj k l => simp [gateClauses] at hc; rcases hc with h | h | h <;> subst h <;> simp

theorem tseitin_length (p : List Gate) : (tseitin p).length ≤ 3 * p.length + 3 := by
  have hsum : ((List.range p.length).flatMap
      (fun j => gateClauses j (p.getD j (.cst false)))).length ≤ 3 * p.length := by
    rw [List.length_flatMap]
    have h1 := sum_le_of_forall_le
      ((List.range p.length).map
        (fun j => (gateClauses j (p.getD j (.cst false))).length)) 3 (by
          intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨j, _, rfl⟩ := hy
          exact gateClauses_card _ _)
    have h2 : ((List.range p.length).map
        (fun j => (gateClauses j (p.getD j (.cst false))).length)).length = p.length := by
      simp
    rw [h2] at h1
    omega
  have hif : (if p.isEmpty then [([] : Clause)] else []).length ≤ 1 := by
    split <;> simp
  simp only [tseitin, List.length_cons, List.length_append]
  omega

theorem tseitin_clause_length (p : List Gate) (c : Clause) (hc : c ∈ tseitin p) :
    c.length ≤ 3 := by
  simp only [tseitin, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with rfl | rfl | hc | ⟨j, _, hj⟩
  · simp
  · simp
  · revert hc
    split
    · intro hc
      simp at hc
      subst hc
      simp
    · intro hc
      simp at hc
  · exact gateClauses_clause_length _ _ _ hj

theorem gateVal_substGate (n : ℕ) (x : Fin n → Bool) (w : ℕ → Bool) (vs : List Bool) (g : Gate) :
    gateVal w vs (substGate n x g) =
      gateVal (fun i => if h : i < n then x ⟨i, h⟩ else w (i - n)) vs g := by
  cases g with
  | inp i =>
      by_cases h : i < n <;> simp [substGate, gateVal, h]
  | _ => rfl

theorem evalAux_map_substGate (p : List Gate) (n : ℕ) (x : Fin n → Bool) (w : ℕ → Bool)
    (vs : List Bool) :
    evalAux w (p.map (substGate n x)) vs =
      evalAux (fun i => if h : i < n then x ⟨i, h⟩ else w (i - n)) p vs := by
  induction p generalizing vs with
  | nil => simp [evalAux]
  | cons g gs ih => simp only [List.map_cons, evalAux, gateVal_substGate, ih]

theorem evalProg_map_substGate (p : List Gate) (n : ℕ) (x : Fin n → Bool) (w : ℕ → Bool) :
    evalProg (p.map (substGate n x)) w =
      evalProg p (fun i => if h : i < n then x ⟨i, h⟩ else w (i - n)) := by
  simp only [evalProg, vals, evalAux_map_substGate, List.length_map]

theorem cnfProg_correct (f : CNF) (a : ℕ → Bool) : evalProg (cnfProg f) a = cnfEval a f := by
  induction f with
  | nil => simp [cnfProg, cnfEval, evalProg, vals, evalAux, gateVal]
  | cons c f ih =>
      rw [cnfProg, evalProg_comb_conj _ _ _ (clauseProg_ne_nil c) (cnfProg_ne_nil f),
        clauseProg_correct, ih]
      simp [cnfEval]

theorem clauseProg_length (c : Clause) : (clauseProg c).length ≤ 3 * c.length + 1 := by
  induction c with
  | nil => simp [clauseProg]
  | cons l c ih =>
      have hl : (litProg l).length ≤ 2 := by unfold litProg; split <;> simp
      rw [clauseProg, comb_length]
      simp only [List.length_cons]
      omega

theorem cnfProg_length_aux (f : CNF) :
    (cnfProg f).length ≤ 3 * (f.map List.length).sum + 2 * f.length + 1 := by
  induction f with
  | nil => simp [cnfProg]
  | cons c f ih =>
      have hc := clauseProg_length c
      rw [cnfProg, comb_length]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem cnfProg_length (f : CNF) :
    (cnfProg f).length ≤ 4 * (f.length + (f.map List.length).sum) + 1 := by
  have := cnfProg_length_aux f
  omega

/-! ## Cook–Levin -/

/-- **Cook–Levin theorem** (Boolean-circuit formulation).

The first conjunct is NP-*membership* of CNF-SAT: for every CNF formula `f`
there is a straight-line Boolean program of size linear in `f` which, given an
assignment, checks whether the assignment satisfies `f`; so satisfiability is
witnessed by an assignment that can be verified efficiently.

The second conjunct is NP-*hardness* of CNF-SAT: for every language `L` that
admits a polynomial-size verifier (an `NPCert`) there is a many-one reduction
`f` from `L` to CNF-SAT producing formulas of polynomial size with clauses of
at most three literals (so in fact a reduction to 3-SAT). -/
theorem cook_levin :
    (∀ f : CNF, ∃ p : List Gate,
        p.length ≤ 4 * (f.length + (f.map List.length).sum) + 1 ∧
        ∀ a : ℕ → Bool, evalProg p a = cnfEval a f) ∧
    (∀ (L : Language) (C : NPCert L), ∃ F : (n : ℕ) → (Fin n → Bool) → CNF,
        (∀ (n : ℕ) (x : Fin n → Bool), L n x ↔ Satisfiable (F n x)) ∧
        (∀ (n : ℕ) (x : Fin n → Bool), (F n x).length ≤ 3 * (C.bnd * (n + 1) ^ C.deg) + 3) ∧
        (∀ (n : ℕ) (x : Fin n → Bool) (c : Clause), c ∈ F n x → c.length ≤ 3)) := by
  refine ⟨fun f => ⟨cnfProg f, cnfProg_length f, fun a => cnfProg_correct f a⟩, ?_⟩
  intro L C
  refine ⟨fun n x => tseitin ((C.prog n).map (substGate n x)), ?_, ?_, ?_⟩
  · intro n x
    rw [C.spec n x, tseitin_sat_iff]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [evalProg_map_substGate]; exact hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [← evalProg_map_substGate]; exact hw⟩
  · intro n x
    have h1 := tseitin_length ((C.prog n).map (substGate n x))
    have h2 := C.size_le n
    simp only [List.length_map] at h1
    show (tseitin ((C.prog n).map (substGate n x))).length ≤ _
    omega
  · intro n x c hc
    exact tseitin_clause_length _ c hc

/-! ## Sanity checks

A few concrete instances, confirming that the definitions behave as intended. -/

/-- The program computing `x₀ ∧ ¬x₀` outputs `false` on every input, so its Tseitin
encoding is unsatisfiable. -/
example : ¬ Satisfiable (tseitin [Gate.inp 0, Gate.neg 0, Gate.conj 0 1]) := by
  rw [tseitin_sat_iff]
  rintro ⟨x, hx⟩
  cases h : x 0 <;> simp [evalProg, vals, evalAux, gateVal, List.getD, h] at hx

/-- The program computing `x₀ ∨ ¬x₀` outputs `true`, so its Tseitin encoding is
satisfiable. -/
example : Satisfiable (tseitin [Gate.inp 0, Gate.neg 0, Gate.disj 0 1]) := by
  rw [tseitin_sat_iff]
  exact ⟨fun _ => true, by simp [evalProg, vals, evalAux, gateVal, List.getD]⟩

/-- The checking circuit of a concrete CNF formula computes its value. -/
example (a : ℕ → Bool) :
    evalProg (cnfProg [[(0, true), (1, false)], [(2, true)]]) a =
      ((a 0 || !(a 1)) && a 2) := by
  rw [cnfProg_correct]
  simp [cnfEval, clauseEval, litEval]

end Frontier

