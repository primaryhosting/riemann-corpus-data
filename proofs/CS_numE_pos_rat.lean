/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is repeated below as the module docstring.)

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A *constraint graph* over the alphabet `Fin q`: a finite (multi)graph on the vertex
set `Fin numV` with `numE` edges, each edge carrying a binary constraint on the values
assigned to its endpoints.  This is the combinatorial object manipulated throughout
Dinur's proof of the PCP theorem. -/
structure ConstraintGraph (q : ℕ) where
  /-- number of vertices -/
  numV : ℕ
  /-- number of edges -/
  numE : ℕ
  /-- the endpoints of each edge -/
  edge : Fin numE → Fin numV × Fin numV
  /-- the constraint attached to each edge -/
  sat : Fin numE → (Fin q → Fin q → Bool)
  /-- constraint graphs have at least one edge -/
  edge_pos : 0 < numE

variable {q : ℕ} [NeZero q]

/-- The set of edges violated by an assignment `σ`. -/
def badEdges (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) : Finset (Fin G.numE) :=
  Finset.univ.filter (fun e => ¬ (G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true))

/-- The fraction of edges violated by the assignment `σ`. -/
def unsatFrac (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) : ℚ :=
  ((badEdges G σ).card : ℚ) / (G.numE : ℚ)

/-- The UNSAT value of a constraint graph: the minimum, over all assignments, of the
fraction of violated edges.  `unsat G = 0` means `G` is satisfiable. -/
noncomputable def unsat (G : ConstraintGraph q) : ℚ :=
  Finset.univ.inf' (Finset.univ_nonempty (α := Fin G.numV → Fin q)) (unsatFrac G)

omit [NeZero q] in
lemma numE_pos_rat (G : ConstraintGraph q) : (0 : ℚ) < (G.numE : ℚ) := by
  exact_mod_cast G.edge_pos

omit [NeZero q] in
lemma unsatFrac_nonneg (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) :
    0 ≤ unsatFrac G σ := by
  apply div_nonneg (by positivity) (le_of_lt (numE_pos_rat G))

omit [NeZero q] in
lemma unsatFrac_le_one (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) :
    unsatFrac G σ ≤ 1 := by
  rw [unsatFrac, div_le_one (numE_pos_rat G)]
  have : (badEdges G σ).card ≤ G.numE := by
    simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin G.numE)) _)
  exact_mod_cast this

lemma exists_unsat_eq (G : ConstraintGraph q) :
    ∃ σ : Fin G.numV → Fin q, unsat G = unsatFrac G σ := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty
    (α := Fin G.numV → Fin q)) (unsatFrac G)
  exact ⟨σ, hσ⟩

lemma unsat_nonneg (G : ConstraintGraph q) : 0 ≤ unsat G := by
  obtain ⟨σ, hσ⟩ := exists_unsat_eq G
  rw [hσ]; exact unsatFrac_nonneg G σ

lemma unsat_le_one (G : ConstraintGraph q) : unsat G ≤ 1 := by
  obtain ⟨σ, hσ⟩ := exists_unsat_eq G
  rw [hσ]; exact unsatFrac_le_one G σ

/-- If a constraint graph is unsatisfiable, then at least one edge is violated by every
assignment, so its UNSAT value is at least `1 / numE`. -/
lemma one_div_numE_le_unsat (G : ConstraintGraph q) (h : 0 < unsat G) :
    1 / (G.numE : ℚ) ≤ unsat G := by
  obtain ⟨σ, hσ⟩ := exists_unsat_eq G
  rw [hσ] at h ⊢
  have hc : 1 ≤ ((badEdges G σ).card : ℚ) := by
    by_contra hlt
    push_neg at hlt
    have : (badEdges G σ).card = 0 := by
      have : ((badEdges G σ).card : ℚ) < 1 := hlt
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [unsatFrac, this] at h
    simp at h
  rw [unsatFrac]
  gcongr

end CS

namespace CS

variable {q : ℕ} [NeZero q]

section Amplification

variable (A : ConstraintGraph q → ConstraintGraph q) (C α : ℚ)

/-- Iterating the amplification step `k` times multiplies the UNSAT value by `2 ^ k`,
until it saturates at the constant `α`. -/
lemma iterate_amp (hα0 : 0 < α)
    (hamp : ∀ G : ConstraintGraph q, min (2 * unsat G) α ≤ unsat (A G))
    (k : ℕ) (G : ConstraintGraph q) :
    min (2 ^ k * unsat G) α ≤ unsat (A^[k] G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h1 : min (2 ^ k * unsat (A G)) α ≤ unsat (A^[k] (A G)) := ih (A G)
      have h2 : min (2 * unsat G) α ≤ unsat (A G) := hamp G
      refine le_trans ?_ h1
      rcases le_total (2 * unsat G) α with h | h
      · have : min (2 * unsat G) α = 2 * unsat G := min_eq_left h
        rw [this] at h2
        have : (2 : ℚ) ^ (k + 1) * unsat G ≤ 2 ^ k * unsat (A G) := by
          have hk : (0 : ℚ) ≤ 2 ^ k := by positivity
          calc (2 : ℚ) ^ (k + 1) * unsat G = 2 ^ k * (2 * unsat G) := by ring
            _ ≤ 2 ^ k * unsat (A G) := by nlinarith
        exact min_le_min this le_rfl
      · have hmin : min (2 * unsat G) α = α := min_eq_right h
        rw [hmin] at h2
        have hk1 : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have : α ≤ 2 ^ k * unsat (A G) := by nlinarith
        calc min ((2 : ℚ) ^ (k + 1) * unsat G) α ≤ α := min_le_right _ _
          _ ≤ min (2 ^ k * unsat (A G)) α := le_min this le_rfl

/-- Iterating a satisfiability-preserving step preserves satisfiability. -/
lemma iterate_sat (hsat : ∀ G : ConstraintGraph q, unsat G = 0 → unsat (A G) = 0)
    (k : ℕ) (G : ConstraintGraph q) (h : unsat G = 0) : unsat (A^[k] G) = 0 := by
  induction k generalizing G with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih (A G) (hsat G h)

omit [NeZero q] in
/-- Iterating a step which blows up the size by at most a factor `C` blows up the size by
at most `C ^ k`. -/
lemma iterate_size (hC : 1 ≤ C)
    (hsize : ∀ G : ConstraintGraph q, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ))
    (k : ℕ) (G : ConstraintGraph q) :
    ((A^[k] G).numE : ℚ) ≤ C ^ k * (G.numE : ℚ) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h1 : ((A^[k] (A G)).numE : ℚ) ≤ C ^ k * ((A G).numE : ℚ) := ih (A G)
      have h2 : ((A G).numE : ℚ) ≤ C * (G.numE : ℚ) := hsize G
      have hk : (0 : ℚ) ≤ C ^ k := by positivity
      calc ((A^[k] (A G)).numE : ℚ) ≤ C ^ k * ((A G).numE : ℚ) := h1
        _ ≤ C ^ k * (C * (G.numE : ℚ)) := by nlinarith
        _ = C ^ (k + 1) * (G.numE : ℚ) := by ring

end Amplification

/-- Auxiliary bound: `2 ^ (Nat.clog 2 m) ≤ 2 * m` for `m ≥ 1`. -/
lemma two_pow_clog_le (m : ℕ) (hm : 0 < m) : 2 ^ (Nat.clog 2 m) ≤ 2 * m := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · simp [← h]
  · have h1 : 2 ^ (Nat.clog 2 m - 1) < m :=
      Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hclog : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    calc 2 ^ (Nat.clog 2 m) = 2 * 2 ^ (Nat.clog 2 m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * m := by omega

/--
**Dinur's gap amplification proof of the PCP theorem.**

Dinur's proof of the PCP theorem consists of a deep combinatorial *amplification step*
(preprocessing, graph powering and composition with an assignment tester), which produces
from any constraint graph `G` over a fixed alphabet a constraint graph `A G` over the same
alphabet such that

* `A G` has size at most `C` times the size of `G` (`hsize`),
* `A G` is satisfiable whenever `G` is (`hsat`),
* the UNSAT value doubles, unless it has already reached the constant `α` (`hamp`),

together with the *iteration argument* formalized here: applying the amplification step
`⌈log₂ (numE G)⌉` times turns any constraint graph into one of polynomial size whose UNSAT
value exhibits the constant gap `α` — satisfiable instances stay satisfiable, and
unsatisfiable instances become "`α`-far" from satisfiable.  This gap version of constraint
satisfaction is exactly the PCP theorem in its equivalent CSP formulation.

Here the amplification step is taken as a hypothesis (`A`, `hsize`, `hsat`, `hamp`) and the
iteration argument is proved, including the explicit polynomial size bound
`(2 · numE G) ^ t · numE G`, where `2 ^ t` bounds the blow-up constant `C`.
-/
theorem pcp_dinur
    (A : ConstraintGraph q → ConstraintGraph q) (C α : ℚ)
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (t : ℕ) (hCt : C ≤ 2 ^ t)
    (hsize : ∀ G : ConstraintGraph q, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ))
    (hsat : ∀ G : ConstraintGraph q, unsat G = 0 → unsat (A G) = 0)
    (hamp : ∀ G : ConstraintGraph q, min (2 * unsat G) α ≤ unsat (A G))
    (G : ConstraintGraph q) :
    ∃ H : ConstraintGraph q,
      H = A^[Nat.clog 2 G.numE] G ∧
      (unsat G = 0 → unsat H = 0) ∧
      (0 < unsat G → α ≤ unsat H) ∧
      ((H.numE : ℚ) ≤ (2 * (G.numE : ℚ)) ^ t * (G.numE : ℚ)) := by
  classical
  set k : ℕ := Nat.clog 2 G.numE with hk
  refine ⟨A^[k] G, rfl, ?_, ?_, ?_⟩
  · intro h; exact iterate_sat A hsat k G h
  · intro hpos
    have hamp' : min ((2 : ℚ) ^ k * unsat G) α ≤ unsat (A^[k] G) :=
      iterate_amp A α hα0 hamp k G
    have hlow : 1 / (G.numE : ℚ) ≤ unsat G := one_div_numE_le_unsat G hpos
    have hpow : (G.numE : ℚ) ≤ (2 : ℚ) ^ k := by
      have : G.numE ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) _
      exact_mod_cast this
    have hmpos : (0 : ℚ) < (G.numE : ℚ) := numE_pos_rat G
    have : (1 : ℚ) ≤ 2 ^ k * unsat G := by
      have h1 : (2 : ℚ) ^ k * (1 / (G.numE : ℚ)) ≤ 2 ^ k * unsat G := by
        have : (0:ℚ) ≤ (2:ℚ) ^ k := by positivity
        nlinarith
      have h2 : (1 : ℚ) ≤ (2 : ℚ) ^ k * (1 / (G.numE : ℚ)) := by
        rw [mul_one_div, le_div_iff₀ hmpos]
        linarith [hpow]
      linarith
    have : α ≤ min ((2:ℚ) ^ k * unsat G) α := le_min (by linarith) le_rfl
    linarith [hamp', this]
  · have h1 : ((A^[k] G).numE : ℚ) ≤ C ^ k * (G.numE : ℚ) := iterate_size A C hC hsize k G
    have hCk : C ^ k ≤ (2 * (G.numE : ℚ)) ^ t := by
      have hC0 : (0:ℚ) ≤ C := by linarith
      have h2 : C ^ k ≤ ((2:ℚ) ^ t) ^ k := pow_le_pow_left₀ hC0 hCt k
      have h3 : ((2:ℚ) ^ t) ^ k = ((2:ℚ) ^ k) ^ t := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h4 : (2:ℚ) ^ k ≤ 2 * (G.numE : ℚ) := by
        have := two_pow_clog_le G.numE G.edge_pos
        have : ((2 ^ k : ℕ) : ℚ) ≤ ((2 * G.numE : ℕ) : ℚ) := by exact_mod_cast this
        push_cast at this
        linarith
      have h5 : ((2:ℚ) ^ k) ^ t ≤ (2 * (G.numE : ℚ)) ^ t :=
        pow_le_pow_left₀ (by positivity) h4 t
      calc C ^ k ≤ ((2:ℚ) ^ t) ^ k := h2
        _ = ((2:ℚ) ^ k) ^ t := h3
        _ ≤ (2 * (G.numE : ℚ)) ^ t := h5
    have hmpos : (0 : ℚ) ≤ (G.numE : ℚ) := le_of_lt (numE_pos_rat G)
    calc ((A^[k] G).numE : ℚ) ≤ C ^ k * (G.numE : ℚ) := h1
      _ ≤ (2 * (G.numE : ℚ)) ^ t * (G.numE : ℚ) := by nlinarith


/-!
### The PCP reading: a two-query verifier

Given a constraint graph `H`, the associated verifier picks one of the `numE` edges
uniformly at random (using `⌈log₂ numE⌉` random bits), queries the two symbols of the
purported proof `σ : Fin numV → Fin q` sitting at the endpoints of that edge, and accepts
iff the constraint of that edge is satisfied.  Its acceptance probability is `accProb`.
-/

omit [NeZero q] in
/-- The probability that the two-query verifier accepts the proof `σ`. -/
lemma accProb_eq (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) :
    ((Finset.univ.filter
        (fun e : Fin G.numE => G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true)).card : ℚ)
      / (G.numE : ℚ) = 1 - unsatFrac G σ := by
  classical
  have hsplit : (Finset.univ.filter
      (fun e : Fin G.numE => G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true)).card
      + (badEdges G σ).card = G.numE := by
    rw [badEdges]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin G.numE)))
      (p := fun e => G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true)
    simpa using this
  have hne : (G.numE : ℚ) ≠ 0 := ne_of_gt (numE_pos_rat G)
  rw [unsatFrac, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hne]
  exact_mod_cast hsplit

lemma unsat_le_unsatFrac (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) :
    unsat G ≤ unsatFrac G σ :=
  Finset.inf'_le _ (Finset.mem_univ σ)

/-- **The PCP theorem in verifier form, via Dinur's iteration.**  Under the amplification
hypotheses, every constraint graph `G` can be turned, in polynomially many steps, into a
constraint graph `H` of polynomial size whose associated two-query verifier has perfect
completeness and soundness error at most `1 - α`. -/
theorem pcp_dinur_verifier
    (A : ConstraintGraph q → ConstraintGraph q) (C α : ℚ)
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (t : ℕ) (hCt : C ≤ 2 ^ t)
    (hsize : ∀ G : ConstraintGraph q, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ))
    (hsat : ∀ G : ConstraintGraph q, unsat G = 0 → unsat (A G) = 0)
    (hamp : ∀ G : ConstraintGraph q, min (2 * unsat G) α ≤ unsat (A G))
    (G : ConstraintGraph q) :
    ∃ H : ConstraintGraph q,
      H = A^[Nat.clog 2 G.numE] G ∧
      ((H.numE : ℚ) ≤ (2 * (G.numE : ℚ)) ^ t * (G.numE : ℚ)) ∧
      (unsat G = 0 → ∃ σ : Fin H.numV → Fin q,
        ((Finset.univ.filter
          (fun e : Fin H.numE => H.sat e (σ (H.edge e).1) (σ (H.edge e).2) = true)).card : ℚ)
            / (H.numE : ℚ) = 1) ∧
      (0 < unsat G → ∀ σ : Fin H.numV → Fin q,
        ((Finset.univ.filter
          (fun e : Fin H.numE => H.sat e (σ (H.edge e).1) (σ (H.edge e).2) = true)).card : ℚ)
            / (H.numE : ℚ) ≤ 1 - α) := by
  classical
  obtain ⟨H, hH, hcomp, hsound, hsz⟩ :=
    pcp_dinur A C α hC hα0 hα1 t hCt hsize hsat hamp G
  refine ⟨H, hH, hsz, ?_, ?_⟩
  · intro h0
    obtain ⟨σ, hσ⟩ := exists_unsat_eq H
    refine ⟨σ, ?_⟩
    rw [accProb_eq, ← hσ, hcomp h0, sub_zero]
  · intro hpos σ
    have h1 : α ≤ unsat H := hsound hpos
    have h2 : unsat H ≤ unsatFrac H σ := unsat_le_unsatFrac H σ
    rw [accProb_eq]
    linarith


/-!
### Non-vacuity of the hypotheses

The amplification step `A` is the deep content of Dinur's proof; here we merely record
that the hypothesis package of `CS.pcp_dinur` is consistent, so that the theorem is not
vacuous, by exhibiting a (degenerate) amplification step over the one-letter alphabet.
-/

lemma unsat_of_const (G : ConstraintGraph q) (c : ℚ)
    (h : ∀ σ : Fin G.numV → Fin q, unsatFrac G σ = c) : unsat G = c := by
  classical
  rw [unsat]
  rw [Finset.inf'_congr (Finset.univ_nonempty (α := Fin G.numV → Fin q)) rfl
      (g := fun _ => c) (fun σ _ => h σ)]
  simp

omit [NeZero q] in
lemma unsatFrac_of_all_true (G : ConstraintGraph q)
    (h : ∀ (e : Fin G.numE) (a b : Fin q), G.sat e a b = true) (σ : Fin G.numV → Fin q) :
    unsatFrac G σ = 0 := by
  have : badEdges G σ = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e _
    simp [h e]
  simp [unsatFrac, this]

omit [NeZero q] in
lemma unsatFrac_of_all_false (G : ConstraintGraph q)
    (h : ∀ (e : Fin G.numE) (a b : Fin q), G.sat e a b = false) (σ : Fin G.numV → Fin q) :
    unsatFrac G σ = 1 := by
  have hb : badEdges G σ = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro e _
    simp [h e]
  have : ((badEdges G σ).card : ℚ) = (G.numE : ℚ) := by
    rw [hb]; simp
  rw [unsatFrac, this]
  exact div_self (ne_of_gt (numE_pos_rat G))

/-- A degenerate amplification step over the one-letter alphabet: it keeps satisfiable
instances satisfiable and sends unsatisfiable instances to instances with UNSAT value `1`. -/
noncomputable def trivialAmp (G : ConstraintGraph 1) : ConstraintGraph 1 where
  numV := G.numV
  numE := G.numE
  edge := G.edge
  sat := fun _ _ _ => decide (unsat G = 0)
  edge_pos := G.edge_pos

lemma unsat_trivialAmp_of_sat {G : ConstraintGraph 1} (h : unsat G = 0) :
    unsat (trivialAmp G) = 0 := by
  have hall : ∀ (e : Fin (trivialAmp G).numE) (a b : Fin 1),
      (trivialAmp G).sat e a b = true := by
    intro e a b
    simp [trivialAmp, h]
  exact unsat_of_const _ 0 (fun σ => unsatFrac_of_all_true _ hall σ)

lemma unsat_trivialAmp_of_unsat {G : ConstraintGraph 1} (h : unsat G ≠ 0) :
    unsat (trivialAmp G) = 1 := by
  have hall : ∀ (e : Fin (trivialAmp G).numE) (a b : Fin 1),
      (trivialAmp G).sat e a b = false := by
    intro e a b
    simp [trivialAmp, h]
  exact unsat_of_const _ 1 (fun σ => unsatFrac_of_all_false _ hall σ)

/-- The hypotheses of `CS.pcp_dinur` are consistent: there is an amplification step
satisfying all of them (over the one-letter alphabet, with `C = 1` and `α = 1`). -/
theorem pcp_dinur_hypotheses_consistent :
    ∃ (A : ConstraintGraph 1 → ConstraintGraph 1) (C α : ℚ),
      1 ≤ C ∧ 0 < α ∧ α ≤ 1 ∧
      (∀ G : ConstraintGraph 1, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ)) ∧
      (∀ G : ConstraintGraph 1, unsat G = 0 → unsat (A G) = 0) ∧
      (∀ G : ConstraintGraph 1, min (2 * unsat G) α ≤ unsat (A G)) := by
  classical
  refine ⟨trivialAmp, 1, 1, le_rfl, one_pos, le_rfl, ?_, ?_, ?_⟩
  · intro G; simp [trivialAmp]
  · intro G h; exact unsat_trivialAmp_of_sat h
  · intro G
    by_cases h : unsat G = 0
    · rw [unsat_trivialAmp_of_sat h, h]
      simp
    · rw [unsat_trivialAmp_of_unsat h]
      exact min_le_right _ _

end CS

