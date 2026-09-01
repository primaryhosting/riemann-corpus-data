import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` statements to precede every other command, including module
docstrings, so the required header comment appears immediately after `import Mathlib`.
-/

open Nat.Partrec Nat.Partrec.Code Denumerable Encodable

namespace CS

/-- A language is a decision predicate on (natural-number encoded) inputs. -/
abbrev Lang := ℕ → Bool

/-- `TIME t` is the class of languages decided by some partial-recursive code within
`t n` steps of the step-indexed evaluator `Nat.Partrec.Code.evaln` on input `n`. -/
def TIME (t : ℕ → ℕ) : Set Lang :=
  {L | ∃ c : Code, ∀ n, evaln (t n) c n = some (cond (L n) 1 0)}

/-- More time can only decide more languages. -/
theorem TIME_mono {t T : ℕ → ℕ} (h : ∀ n, t n ≤ T n) : TIME t ⊆ TIME T := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun n => evaln_mono (h n) (hc n)⟩

/-- Sanity check: the classes `TIME t` are non-trivial, e.g. the empty language is decided
in `n + 1` steps by the code `zero`. -/
theorem constFalse_mem_TIME : (fun _ => false) ∈ TIME (fun n => n + 1) :=
  ⟨Code.zero, fun n => by simp [Nat.Partrec.Code.evaln]⟩

/-- The diagonal language for the time bound `t`: on input `n`, run the `n`-th code on `n`
for `t n` steps and output the opposite answer. -/
def diag (t : ℕ → ℕ) : Lang := fun n => !decide (evaln (t n) (ofNat Code n) n = some 1)

/-- **Diagonalization**: the diagonal language is not decidable within time `t`. -/
theorem diag_not_mem_TIME (t : ℕ → ℕ) : diag t ∉ TIME t := by
  rintro ⟨c, hc⟩
  have hn := hc (encode c)
  have hd : diag t (encode c) = !decide (evaln (t (encode c)) c (encode c) = some 1) := by
    simp only [diag, Denumerable.ofNat_encode]
  cases hb : diag t (encode c) with
  | false => rw [hb] at hn hd; simp [hn] at hd
  | true => rw [hb] at hn hd; simp [hn] at hd

/-- The diagonal language is decidable, hence lies in `TIME T` for a suitable bound `T`. -/
theorem diag_mem_TIME (t : ℕ → ℕ) (ht : Computable t) :
    ∃ T : ℕ → ℕ, (∀ n, t n ≤ T n) ∧ diag t ∈ TIME T := by
  have hE : Computable fun n => evaln (t n) (ofNat Code n) n :=
    primrec_evaln.to_comp.comp ((ht.pair (Primrec.ofNat Code).to_comp).pair Computable.id)
  have hprim : Primrec₂ (fun a b : Option ℕ => decide (a = b)) :=
    (Primrec.eq (α := Option ℕ)).decide
  have hd : Computable (diag t) :=
    Primrec.not.to_comp.comp
      (hprim.to_comp.comp hE (Computable.const (some 1)))
  have hf : Computable fun n => cond (diag t n) 1 0 :=
    hd.cond (Computable.const 1) (Computable.const 0)
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf.partrec)
  have hk : ∀ n, ∃ k, cond (diag t n) 1 0 ∈ evaln k c n := by
    intro n
    refine Nat.Partrec.Code.evaln_complete.1 ?_
    rw [hcode]
    simp
  refine ⟨fun n => max (t n) (Nat.find (hk n)), fun n => le_max_left _ _, c, fun n => ?_⟩
  exact evaln_mono (le_max_right _ _) (Nat.find_spec (hk n))

/-- **Time hierarchy theorem**: for every computable time bound `t` there is a strictly
larger time bound `T` whose complexity class strictly contains that of `t`; the witnessing
language is obtained by diagonalization. -/
theorem time_hierarchy (t : ℕ → ℕ) (ht : Computable t) :
    ∃ T : ℕ → ℕ, (∀ n, t n ≤ T n) ∧ TIME t ⊂ TIME T := by
  obtain ⟨T, hT, hmem⟩ := diag_mem_TIME t ht
  exact ⟨T, hT, ⟨TIME_mono hT, fun h => diag_not_mem_TIME t (h hmem)⟩⟩

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

