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

/-- A *constraint graph* over the alphabet `Fin q`: a finite nonempty list (multiset) of
constraints, each of which is a pair of vertices together with a boolean predicate on the
pair of values assigned to them. -/
structure ConstraintGraph (q : ℕ) where
  /-- Number of vertices. -/
  numVerts : ℕ
  /-- The constraints (edges): a pair of endpoints and a boolean relation on their values. -/
  edges : List (Fin numVerts × Fin numVerts × (Fin q → Fin q → Bool))
  /-- Constraint graphs have at least one constraint. -/
  edges_ne : edges ≠ []

namespace ConstraintGraph

variable {q : ℕ} [NeZero q]

/-- The size of a constraint graph is its number of constraints. -/
def size (G : ConstraintGraph q) : ℕ := G.edges.length

/-- An assignment of alphabet values to the vertices of `G`. -/
abbrev Assignment (G : ConstraintGraph q) : Type := Fin G.numVerts → Fin q

/-- Whether the assignment `a` satisfies the constraint `e`. -/
def SatEdge (G : ConstraintGraph q) (a : G.Assignment)
    (e : Fin G.numVerts × Fin G.numVerts × (Fin q → Fin q → Bool)) : Prop :=
  e.2.2 (a e.1) (a e.2.1) = true

/-- The number of constraints of `G` violated by the assignment `a`. -/
def unsatCount (G : ConstraintGraph q) (a : G.Assignment) : ℕ :=
  G.edges.countP (fun e => !(e.2.2 (a e.1) (a e.2.1)))

/-- The fraction of constraints of `G` violated by the assignment `a`. -/
def unsatFrac (G : ConstraintGraph q) (a : G.Assignment) : ℚ :=
  (G.unsatCount a : ℚ) / (G.size : ℚ)

/-- The `UNSAT` value of a constraint graph: the minimum, over all assignments, of the
fraction of violated constraints. -/
noncomputable def unsat (G : ConstraintGraph q) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : G.Assignment => G.unsatFrac a)

/-- A constraint graph is satisfiable if some assignment satisfies all of its constraints. -/
def Satisfiable (G : ConstraintGraph q) : Prop :=
  ∃ a : G.Assignment, ∀ e ∈ G.edges, G.SatEdge a e

omit [NeZero q] in
lemma size_pos (G : ConstraintGraph q) : 0 < G.size :=
  List.length_pos_of_ne_nil G.edges_ne

omit [NeZero q] in
lemma unsatFrac_nonneg (G : ConstraintGraph q) (a : G.Assignment) : 0 ≤ G.unsatFrac a := by
  unfold unsatFrac
  positivity

omit [NeZero q] in
lemma unsatFrac_le_one (G : ConstraintGraph q) (a : G.Assignment) : G.unsatFrac a ≤ 1 := by
  unfold unsatFrac
  rw [div_le_one (by exact_mod_cast G.size_pos)]
  exact_mod_cast (List.countP_le_length (l := G.edges))

lemma unsat_nonneg (G : ConstraintGraph q) : 0 ≤ G.unsat := by
  unfold unsat
  exact Finset.le_inf' _ _ (fun a _ => G.unsatFrac_nonneg a)

lemma unsat_le_one (G : ConstraintGraph q) : G.unsat ≤ 1 := by
  unfold unsat
  obtain ⟨a, -⟩ := (Finset.univ_nonempty (α := G.Assignment))
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ a)) (G.unsatFrac_le_one a)

/-- The `UNSAT` value is attained by some assignment. -/
lemma exists_unsat_eq (G : ConstraintGraph q) : ∃ a : G.Assignment, G.unsat = G.unsatFrac a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G.Assignment))
    (fun a : G.Assignment => G.unsatFrac a)
  exact ⟨a, ha⟩

lemma unsat_le (G : ConstraintGraph q) (a : G.Assignment) : G.unsat ≤ G.unsatFrac a :=
  Finset.inf'_le _ (Finset.mem_univ a)

omit [NeZero q] in
lemma unsatCount_eq_zero_iff (G : ConstraintGraph q) (a : G.Assignment) :
    G.unsatCount a = 0 ↔ ∀ e ∈ G.edges, G.SatEdge a e := by
  unfold unsatCount SatEdge
  rw [List.countP_eq_zero]
  constructor
  · intro h e he
    have := h e he
    simpa using this
  · intro h e he
    simpa using h e he

omit [NeZero q] in
lemma unsatFrac_eq_zero_iff (G : ConstraintGraph q) (a : G.Assignment) :
    G.unsatFrac a = 0 ↔ ∀ e ∈ G.edges, G.SatEdge a e := by
  rw [← G.unsatCount_eq_zero_iff a]
  unfold unsatFrac
  rw [div_eq_zero_iff]
  have hs : (G.size : ℚ) ≠ 0 := by
    exact_mod_cast G.size_pos.ne'
  simp [hs]

/-- `UNSAT(G) = 0` exactly when `G` is satisfiable. -/
lemma unsat_eq_zero_iff (G : ConstraintGraph q) : G.unsat = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := G.exists_unsat_eq
    exact ⟨a, (G.unsatFrac_eq_zero_iff a).mp (by rw [← ha, h])⟩
  · rintro ⟨a, ha⟩
    refine le_antisymm ?_ G.unsat_nonneg
    have := G.unsat_le a
    rwa [(G.unsatFrac_eq_zero_iff a).mpr ha] at this

/-- The base gap: an unsatisfiable constraint graph violates at least one out of its `size`
constraints, i.e. `UNSAT(G) ≥ 1 / size G`. -/
lemma one_le_size_mul_unsat (G : ConstraintGraph q) (h : ¬ G.Satisfiable) :
    1 ≤ (G.size : ℚ) * G.unsat := by
  obtain ⟨a, ha⟩ := G.exists_unsat_eq
  have h1 : 1 ≤ G.unsatCount a := by
    rcases Nat.eq_zero_or_pos (G.unsatCount a) with h0 | h0
    · exact absurd ⟨a, (G.unsatCount_eq_zero_iff a).mp h0⟩ h
    · exact h0
  have hs : (0 : ℚ) < (G.size : ℚ) := by exact_mod_cast G.size_pos
  rw [ha]
  unfold unsatFrac
  rw [mul_div_cancel₀ _ hs.ne']
  exact_mod_cast h1

end ConstraintGraph

open ConstraintGraph

/-! ## Iterating the amplification step -/

section Amplification

variable {q : ℕ} [NeZero q]
variable (C : ℕ) (alpha : ℚ) (step : ConstraintGraph q → ConstraintGraph q)

omit [NeZero q] in
/-- Iterating the amplification step preserves satisfiability. -/
lemma satisfiable_iterate
    (hsat : ∀ G, G.Satisfiable → (step G).Satisfiable) (t : ℕ) (G : ConstraintGraph q)
    (hG : G.Satisfiable) : (step^[t] G).Satisfiable := by
  induction t with
  | zero => simp only [Function.iterate_zero_apply]; exact hG
  | succ t ih => rw [Function.iterate_succ_apply']; exact hsat _ ih

omit [NeZero q] in
/-- Iterating the amplification step `t` times multiplies the size by at most `C ^ t`. -/
lemma size_iterate_le
    (hsize : ∀ G, (step G).size ≤ C * G.size) (t : ℕ) (G : ConstraintGraph q) :
    (step^[t] G).size ≤ C ^ t * G.size := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc (step (step^[t] G)).size ≤ C * (step^[t] G).size := hsize _
        _ ≤ C * (C ^ t * G.size) := by exact Nat.mul_le_mul_left _ ih
        _ = C ^ (t + 1) * G.size := by ring

/-- Iterating the amplification step `t` times doubles the `UNSAT` value `t` times, until it
reaches the constant `alpha`. -/
lemma unsat_iterate_ge (halpha : 0 ≤ alpha)
    (hunsat : ∀ G, min (2 * G.unsat) alpha ≤ (step G).unsat) (t : ℕ) (G : ConstraintGraph q) :
    min (2 ^ t * G.unsat) alpha ≤ (step^[t] G).unsat := by
  induction t with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]; exact min_le_left _ _
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (hunsat (step^[t] G))
      have h2 : 2 * min (2 ^ t * G.unsat) alpha ≤ 2 * (step^[t] G).unsat := by linarith
      rcases le_total (2 ^ t * G.unsat) alpha with h | h
      · rw [min_eq_left h] at h2
        have : (2 : ℚ) ^ (t + 1) * G.unsat = 2 * (2 ^ t * G.unsat) := by ring
        rw [this]
        exact min_le_min h2 le_rfl
      · rw [min_eq_right h] at h2
        refine le_trans (min_le_right _ _) ?_
        exact le_min (by linarith) le_rfl

end Amplification

/-! ## Dinur's theorem

Starting from Dinur's *Main Lemma* (gap amplification: a size-linear transformation of
constraint graphs over a fixed alphabet which preserves satisfiability and doubles the `UNSAT`
value until it exceeds an absolute constant `alpha`), iterating it `⌈log₂ n⌉` times turns the
inverse-linear gap `1/n` of an unsatisfiable instance into the constant gap `alpha`, at a
polynomial cost in size.  This is the gap-amplification argument underlying the PCP theorem:
deciding whether a constraint graph is satisfiable or has `UNSAT` value at least `alpha` is as
hard as deciding satisfiability of constraint graphs, which is the "gap" (equivalently,
proof-checking) form of the PCP theorem. -/

/-- Auxiliary arithmetic fact: `2 ^ ⌈log₂ n⌉ ≤ 2 * n` for `n ≥ 1`. -/
lemma two_pow_clog_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp
  · have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) h
    have : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    omega

/-- **Dinur's gap amplification theorem (PCP theorem, gap form).**

Assume Dinur's Main Lemma for constraint graphs over the fixed alphabet `Fin q`: there are
constants `C` and `alpha ∈ (0, 1]` and a transformation `step` of constraint graphs which
* preserves satisfiability,
* increases the size by at most a factor `C`,
* and doubles the `UNSAT` value, up to the ceiling `alpha`.

Then there is a *gap-producing* reduction `R`, of polynomial size blow-up, that maps satisfiable
constraint graphs to satisfiable constraint graphs, and unsatisfiable ones to constraint graphs
whose `UNSAT` value is at least the absolute constant `alpha`. -/
theorem pcp_dinur {q : ℕ} [NeZero q]
    (C : ℕ) (alpha : ℚ) (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (step : ConstraintGraph q → ConstraintGraph q)
    (hsat : ∀ G, G.Satisfiable → (step G).Satisfiable)
    (hsize : ∀ G, (step G).size ≤ C * G.size)
    (hunsat : ∀ G, min (2 * G.unsat) alpha ≤ (step G).unsat) :
    ∃ (R : ConstraintGraph q → ConstraintGraph q) (d : ℕ),
      (∀ G, G.Satisfiable → (R G).Satisfiable) ∧
      (∀ G, ¬ G.Satisfiable → alpha ≤ (R G).unsat) ∧
      (∀ G, (R G).size ≤ (2 * G.size) ^ d * G.size) := by
  classical
  refine ⟨fun G => step^[Nat.clog 2 G.size] G, Nat.clog 2 C, ?_, ?_, ?_⟩
  · intro G hG
    exact satisfiable_iterate step hsat _ G hG
  · intro G hG
    have key := unsat_iterate_ge alpha step halpha0.le hunsat (Nat.clog 2 G.size) G
    refine le_trans ?_ key
    refine le_min ?_ le_rfl
    -- `2 ^ ⌈log₂ n⌉ * UNSAT(G) ≥ n * (1/n) = 1 ≥ alpha`
    have hbase : 1 ≤ (G.size : ℚ) * G.unsat := G.one_le_size_mul_unsat hG
    have hle : (G.size : ℚ) ≤ (2 : ℚ) ^ Nat.clog 2 G.size := by
      have : G.size ≤ 2 ^ Nat.clog 2 G.size := Nat.le_pow_clog (by norm_num) _
      exact_mod_cast this
    have hu : 0 ≤ G.unsat := G.unsat_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hle hu]
  · intro G
    have h1 : (step^[Nat.clog 2 G.size] G).size ≤ C ^ Nat.clog 2 G.size * G.size :=
      size_iterate_le C step hsize _ G
    have h2 : C ^ Nat.clog 2 G.size ≤ (2 * G.size) ^ Nat.clog 2 C := by
      calc C ^ Nat.clog 2 G.size ≤ (2 ^ Nat.clog 2 C) ^ Nat.clog 2 G.size :=
            Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
        _ = (2 ^ Nat.clog 2 G.size) ^ Nat.clog 2 C := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (2 * G.size) ^ Nat.clog 2 C :=
            Nat.pow_le_pow_left (two_pow_clog_le G.size G.size_pos) _
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)

/-! ## Non-degeneracy

Two concrete constraint graphs, witnessing that satisfiability of constraint graphs is a
nontrivial notion (both satisfiable and unsatisfiable instances exist) and that the base gap
lemma has real content. -/

/-- A satisfiable constraint graph: two vertices with the single constraint `x = y`. -/
def demoSat : ConstraintGraph 2 where
  numVerts := 2
  edges := [(0, 1, fun x y => x == y)]
  edges_ne := by simp

/-- An unsatisfiable constraint graph: two vertices carrying both `x = y` and `x ≠ y`. -/
def demoUnsat : ConstraintGraph 2 where
  numVerts := 2
  edges := [(0, 1, fun x y => x == y), (0, 1, fun x y => !(x == y))]
  edges_ne := by simp

lemma demoSat_satisfiable : demoSat.Satisfiable := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he
  simp only [demoSat, ConstraintGraph.SatEdge, List.mem_singleton] at he ⊢
  subst he
  simp

lemma demoUnsat_not_satisfiable : ¬ demoUnsat.Satisfiable := by
  rintro ⟨a, ha⟩
  simp [demoUnsat, ConstraintGraph.SatEdge] at ha

/-- The base gap in action: the unsatisfiable example violates at least one of its two
constraints under every assignment, so its `UNSAT` value is at least `1/2`. -/
lemma demoUnsat_unsat_ge : (1 : ℚ) / 2 ≤ demoUnsat.unsat := by
  have h := demoUnsat.one_le_size_mul_unsat demoUnsat_not_satisfiable
  have hsize : demoUnsat.size = 2 := by simp [ConstraintGraph.size, demoUnsat]
  rw [hsize] at h
  push_cast at h
  linarith

end CS

