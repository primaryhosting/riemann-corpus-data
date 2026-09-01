import Mathlib

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Notes on the formalisation

Hilbert's tenth problem asks for an algorithm deciding whether a Diophantine equation has a
solution.  Its unsolvability is the combination of two facts:

* **MRDP / DPRM**: every recursively enumerable set of naturals is Diophantine;
* the halting problem is recursively enumerable and undecidable.

Mathlib contains Matiyasevich's contribution to the first fact — the power function is
Diophantine, `Dioph.pow_dioph` — but not the MRDP theorem itself; the module
`Mathlib.NumberTheory.Dioph` carries the explicit `TODO: Finish the solution of Hilbert's tenth
problem`.  MRDP is therefore an explicit hypothesis of `CS.hilbert10_undecidable`, stated in
Mathlib's own `Dioph` vocabulary, so that the theorem becomes unconditional as soon as MRDP is
available.  Everything else in this file is proved unconditionally: the passage from Mathlib's
`Dioph` (whose unknowns range over an arbitrary type) to an honest polynomial in finitely many
unknowns, and the reduction of the halting problem.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

open Fin2 Function Sum

namespace CS

/-- `CS.DiophantineSet S` says that `S ⊆ ℕ` is a Diophantine set: there are a number `k` of
unknowns and an integer polynomial `p` in `1 + k` variables such that

`a ∈ S ↔ ∃ x : Fin k → ℕ, p (a, x 0, …, x (k-1)) = 0`.

This is the classical notion of a Diophantine subset of `ℕ` with one parameter, phrased with
`MvPolynomial (Fin (k+1)) ℤ` so that the number of unknowns is explicitly finite. -/
def DiophantineSet (S : Set ℕ) : Prop :=
  ∃ (k : ℕ) (p : MvPolynomial (Fin (k + 1)) ℤ),
    ∀ a : ℕ, a ∈ S ↔
      ∃ x : Fin k → ℕ, MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) p = 0

/-- Every function in Mathlib's class `IsPoly` of integer polynomial functions is the evaluation
of a genuine multivariate polynomial. -/
theorem exists_mvPolynomial_of_isPoly {γ : Type} {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ P : MvPolynomial γ ℤ, ∀ x : γ → ℕ, f x = MvPolynomial.eval (fun i => (x i : ℤ)) P := by
  induction hf with
  | proj i => exact ⟨MvPolynomial.X i, fun x => by simp⟩
  | const n => exact ⟨MvPolynomial.C n, fun x => by simp⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨P, hP⟩ := ih1; obtain ⟨Q, hQ⟩ := ih2
      exact ⟨P - Q, fun x => by simp [hP, hQ]⟩
  | mul _ _ ih1 ih2 =>
      obtain ⟨P, hP⟩ := ih1; obtain ⟨Q, hQ⟩ := ih2
      exact ⟨P * Q, fun x => by simp [hP, hQ]⟩

/-- A set of naturals that is Diophantine in the sense of Mathlib's `Dioph` — where the unknowns
range over an arbitrary type and the polynomial is an element of Mathlib's `Poly` — is
Diophantine in the sense of `CS.DiophantineSet`: finitely many unknowns, and an honest
multivariate polynomial. -/
theorem diophantineSet_of_dioph {S : Set ℕ}
    (h : Dioph {v : Fin2 1 → ℕ | v Fin2.fz ∈ S}) : DiophantineSet S := by
  classical
  obtain ⟨β, p, hp⟩ := h
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_isPoly p.isPoly
  obtain ⟨n, f, hfinj, q, rfl⟩ := MvPolynomial.exists_fin_rename P
  refine ⟨n, MvPolynomial.rename (fun i : Fin n => if f i = Sum.inl Fin2.fz then 0 else i.succ) q,
    fun a => ?_⟩
  refine Iff.trans (hp (fun _ => a)) ?_
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i => (Sum.elim (fun _ => a) t) (f i), ?_⟩
    rw [MvPolynomial.eval_rename, hP, MvPolynomial.eval_rename] at *
    rw [← ht]
    congr 2
    funext i
    by_cases hfi : f i = Sum.inl Fin2.fz
    · simp [Function.comp, hfi]
    · simp [Function.comp, hfi]
  · rintro ⟨x, hx⟩
    refine ⟨fun b => if hb : ∃ i, f i = Sum.inr b then x (Classical.choose hb) else 0, ?_⟩
    rw [hP, MvPolynomial.eval_rename]
    rw [MvPolynomial.eval_rename] at hx
    rw [← hx]
    congr 2
    funext i
    by_cases hfi : f i = Sum.inl Fin2.fz
    · simp [Function.comp, hfi]
    · have hb2 : ∃ b, f i = Sum.inr b := by
        cases hfe : f i with
        | inl u => cases u with
          | fz => exact absurd hfe hfi
          | fs j => cases j
        | inr b => exact ⟨b, rfl⟩
      obtain ⟨b, hb⟩ := hb2
      have hex : ∃ j, f j = Sum.inr b := ⟨i, hb⟩
      have hch : Classical.choose hex = i := hfinj (by rw [Classical.choose_spec hex, hb])
      simp [Function.comp, hb, hex, hch]

/-- The halting set, as a set of natural numbers: `c ∈ haltingSet` iff the partial recursive
function with code `c` halts on input `0`. -/
def haltingSet : Set ℕ :=
  {c : ℕ | (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code c) 0).Dom}

/-- The halting set is recursively enumerable. -/
theorem rePred_haltingSet : REPred (· ∈ haltingSet) :=
  (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Nat.Partrec.Code)

/-- The halting set is undecidable. -/
theorem not_computablePred_haltingSet : ¬ ComputablePred (· ∈ haltingSet) := by
  intro h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_of_manyOneReducible ?_ h)
  exact ⟨fun c => Encodable.encode c, Computable.encode,
    fun c => by simp [haltingSet, Denumerable.ofNat_encode]⟩

/-- If the halting set is Diophantine, then Hilbert's tenth problem is undecidable: there is a
single integer polynomial `p (a, x 0, …, x (k-1))` for which no algorithm decides, given the
parameter `a`, whether `p (a, ·) = 0` has a solution in natural numbers. -/
theorem undecidable_of_diophantineSet_haltingSet (h : DiophantineSet haltingSet) :
    ∃ (k : ℕ) (p : MvPolynomial (Fin (k + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ =>
        ∃ x : Fin k → ℕ, MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) p = 0 := by
  obtain ⟨k, p, hp⟩ := h
  refine ⟨k, p, fun hcomp => not_computablePred_haltingSet ?_⟩
  exact hcomp.of_eq fun a => (hp a).symm

/-- **Hilbert's tenth problem is undecidable.**

Given the MRDP (Matiyasevich–Robinson–Davis–Putnam) theorem — every recursively enumerable set
of naturals is Diophantine — there is a single integer polynomial `p (a, x 0, …, x (k-1))` such
that no algorithm decides, given `a`, whether the Diophantine equation `p (a, x) = 0` has a
solution in the natural numbers.  A fortiori there is no algorithm for the general problem of
deciding solvability of Diophantine equations.

MRDP is not available in Mathlib (see the notes at the top of this file) and is taken here as
the hypothesis `mrdp`, stated in Mathlib's own `Dioph` vocabulary. -/
theorem hilbert10_undecidable
    (mrdp : ∀ S : Set ℕ, REPred (· ∈ S) → Dioph {v : Fin2 1 → ℕ | v Fin2.fz ∈ S}) :
    ∃ (k : ℕ) (p : MvPolynomial (Fin (k + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ =>
        ∃ x : Fin k → ℕ, MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) p = 0 :=
  undecidable_of_diophantineSet_haltingSet
    (diophantineSet_of_dioph (mrdp haltingSet rePred_haltingSet))

end CS

