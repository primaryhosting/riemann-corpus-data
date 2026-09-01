/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Blum speedup: a problem with no fastest algorithm

(The header comment above is kept verbatim, except that it is a plain block comment: Lean 4 does
not allow a module docstring to precede the `import` commands.)

We work inside Mathlib's model of computation: programs are `Nat.Partrec.Code`s, the semantics of
a program `c` is `Nat.Partrec.Code.eval c : ℕ →. ℕ`, and the *running time* of `c` on input `x`,
`CS.cost c x`, is the least amount of fuel `k` for which the step-bounded interpreter
`Nat.Partrec.Code.evaln k c x` returns a value.  This is a genuine (Blum) complexity measure:
it is defined exactly on the inputs where `c` halts, and the relation `cost c x ≤ k` is decidable.

`CS.blum_speedup` exhibits a computable `{0,1}`-valued function `diag` (a decision problem) which
is solvable, but for which **no algorithm is fastest**: for every program `c` solving it there is
another program `c'` solving it which runs strictly faster than `c` on infinitely many inputs.
`CS.no_fastest_algorithm` records the resulting non-existence of an optimal program.

The construction is a diagonalisation.  For a program index `e`, the *patched* program `patch e`
answers `1` immediately on every input `x` whose first pairing component is `e`, and otherwise
simulates the program with index `e`.  The time bound `bound x` used in the diagonalisation is
defined to be exactly the running time of `patch (Nat.unpair x).1` on `x`, and `diag r x` is `0`
if the program with index `(Nat.unpair x).1` outputs `1` on `x` within `r (bound x)` steps and
`1` otherwise.  Then any program `c` computing `diag r` must fail to halt within `r (bound x)`
steps on all the (infinitely many) inputs `x` with `(Nat.unpair x).1 = encode c`, on which
`diag r` takes the value `1`; hence the patched program `patch (encode c)` also computes `diag r`
and beats `c` on all of those inputs.

`CS.blum_speedup_factor` is the quantitative version: the same construction, run with a time
bound inflated by a prescribed computable factor `r`, produces for each computable `r` a decision
problem on which every program `c` is beaten by a program `c'` with `r (cost c' x) < cost c x` on
infinitely many inputs `x`.

Scope: this is the "infinitely often" form of the speedup phenomenon (no algorithm is optimal;
every algorithm is beaten by an arbitrary prescribed computable factor on infinitely many
inputs).  Blum's original speedup theorem gives the stronger "almost everywhere" form, which is
not formalised here.
-/

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

namespace CS

/-- `Computes c f` says that the program (code) `c` computes the total function `f`. -/
def Computes (c : Code) (f : ℕ → ℕ) : Prop := ∀ x, eval c x = Part.some (f x)

/-- The running time of the program `c` on input `x`: the least amount of fuel `k` for which the
step-bounded interpreter `Nat.Partrec.Code.evaln` returns a value.  (Junk value `0` if `c`
diverges on `x`.) -/
noncomputable def cost (c : Code) (x : ℕ) : ℕ := sInf {k | (evaln k c x).isSome}

theorem cost_le {c : Code} {x k : ℕ} (h : (evaln k c x).isSome) : cost c x ≤ k :=
  Nat.sInf_le h

theorem evaln_cost {c : Code} {x : ℕ} (h : ∃ k, (evaln k c x).isSome) :
    (evaln (cost c x) c x).isSome :=
  Nat.sInf_mem h

theorem lt_cost {c : Code} {x k : ℕ} (hd : ∃ j, (evaln j c x).isSome)
    (h : ¬ (evaln k c x).isSome) : k < cost c x := by
  by_contra hk
  push_neg at hk
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (evaln_cost hd)
  have h2 : v ∈ evaln k c x := evaln_mono hk hv
  rw [Option.mem_def] at h2
  simp [h2] at h

/-- The partial function underlying the "patched" programs: on input `Nat.pair e x` it returns `1`
if `x` has first pairing component `e`, and otherwise runs the program with index `e` on `x`. -/
def patchPartial (z : ℕ) : Part ℕ :=
  eval (if (Nat.unpair (Nat.unpair z).2).1 = (Nat.unpair z).1 then Nat.Partrec.Code.const 1
        else ofNat Code (Nat.unpair z).1) (Nat.unpair z).2

theorem patchPartial_partrec : Nat.Partrec patchPartial := by
  have hcode : Computable fun z : ℕ =>
      (if (Nat.unpair (Nat.unpair z).2).1 = (Nat.unpair z).1 then Nat.Partrec.Code.const 1
        else ofNat Code (Nat.unpair z).1) := by
    refine Primrec.to_comp (Primrec.ite ?_ (Primrec.const _) ?_)
    · exact Primrec.eq.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.fst.comp Primrec.unpair)
    · exact (Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair)
  have hinput : Computable fun z : ℕ => (Nat.unpair z).2 :=
    Primrec.to_comp (Primrec.snd.comp Primrec.unpair)
  exact Partrec.nat_iff.1 (eval_part.comp hcode hinput)

/-- A fixed code for `patchPartial`. -/
noncomputable def branchCode : Code := Classical.choose (exists_code.1 patchPartial_partrec)

theorem branchCode_eval : eval branchCode = patchPartial :=
  Classical.choose_spec (exists_code.1 patchPartial_partrec)

/-- `patch e` is the program: "on input `x`, if the first pairing component of `x` is `e`, output
`1` immediately; otherwise run the program with index `e` on `x`". -/
noncomputable def patch (e : ℕ) : Code := curry branchCode e

theorem patch_eval (e x : ℕ) :
    eval (patch e) x =
      if (Nat.unpair x).1 = e then Part.some 1 else eval (ofNat Code e) x := by
  rw [patch, eval_curry, branchCode_eval]
  simp only [patchPartial, Nat.unpair_pair]
  split <;> simp [eval_const]

theorem patch_halts (x : ℕ) : eval (patch (Nat.unpair x).1) x = Part.some 1 := by
  rw [patch_eval]; simp

/-- The time bound used in the diagonalisation: the running time of the patched program
`patch (Nat.unpair x).1` on the input `x` (which is always defined). -/
noncomputable def bound (x : ℕ) : ℕ := cost (patch (Nat.unpair x).1) x

theorem patch_dom (x : ℕ) : ∃ k, (evaln k (patch (Nat.unpair x).1) x).isSome := by
  have h : (1 : ℕ) ∈ eval (patch (Nat.unpair x).1) x := by rw [patch_halts]; simp
  obtain ⟨k, hk⟩ := evaln_complete.1 h
  exact ⟨k, Option.isSome_of_mem hk⟩

theorem bound_spec (x : ℕ) : (evaln (bound x) (patch (Nat.unpair x).1) x).isSome :=
  Nat.sInf_mem (patch_dom x)

theorem bound_min {x m : ℕ} (h : m < bound x) :
    ¬ (evaln m (patch (Nat.unpair x).1) x).isSome :=
  fun hm => absurd (Nat.sInf_le hm) (not_le.2 h)

theorem bound_computable : Computable bound := by
  have hpatch : Computable fun x : ℕ => patch (Nat.unpair x).1 :=
    Primrec.to_comp (primrec₂_curry.comp (Primrec.const branchCode)
      (Primrec.fst.comp Primrec.unpair))
  have hev : Computable fun q : ℕ × ℕ => evaln q.2 (patch (Nat.unpair q.1).1) q.1 :=
    primrec_evaln.to_comp.comp (((Computable.snd).pair (hpatch.comp Computable.fst)).pair
      Computable.fst)
  have hb : Computable₂ fun (x k : ℕ) => (evaln k (patch (Nat.unpair x).1) x).isSome := by
    have h := Computable.option_casesOn hev (Computable.const false) (Computable.const true).to₂
    exact h.of_eq fun q => by cases h : evaln q.2 (patch (Nat.unpair q.1).1) q.1 <;> simp [h]
  have hp : Partrec fun x : ℕ =>
      Nat.rfind (fun k => (Part.some ((evaln k (patch (Nat.unpair x).1) x).isSome))) :=
    Partrec.rfind (Computable₂.partrec₂ hb)
  refine hp.of_eq fun x => ?_
  apply Part.eq_some_iff.2
  refine Nat.mem_rfind.2 ⟨?_, ?_⟩
  · simpa using bound_spec x
  · intro m hm
    simpa using bound_min hm

/-- The hard problem associated with a "speedup factor" `r`: `diag r x = 0` if the program with
index `(Nat.unpair x).1` outputs `1` on `x` within `r (bound x)` steps, and `diag r x = 1`
otherwise.  This is a decision problem (`diag r` takes only the values `0` and `1`). -/
noncomputable def diag (r : ℕ → ℕ) (x : ℕ) : ℕ :=
  if evaln (r (bound x)) (ofNat Code (Nat.unpair x).1) x = some 1 then 0 else 1

theorem diag_le_one (r : ℕ → ℕ) (x : ℕ) : diag r x ≤ 1 := by
  simp only [diag]
  split <;> omega

theorem diag_computable {r : ℕ → ℕ} (hr : Computable r) : Computable (diag r) := by
  have hE : Computable fun x : ℕ => evaln (r (bound x)) (ofNat Code (Nat.unpair x).1) x :=
    primrec_evaln.to_comp.comp
      (((hr.comp bound_computable).pair
        ((Computable.ofNat Code).comp (Primrec.fst.comp Primrec.unpair).to_comp)).pair
        Computable.id)
  have hg : Computable₂ fun (_ : ℕ) (b : ℕ) => if b = 1 then 0 else 1 :=
    Primrec.to_comp (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (Primrec.const 0) (Primrec.const 1))
  have h := Computable.option_casesOn hE (Computable.const 1) hg
  exact h.of_eq fun x => by
    cases h : evaln (r (bound x)) (ofNat Code (Nat.unpair x).1) x <;> simp [diag, h]

/-- The heart of the diagonalisation: a program `c` computing `diag r` cannot halt on the input
`x` within `r (bound x)` steps, whenever the first pairing component of `x` is the index of `c`;
and on all such inputs the answer is `1`. -/
theorem diag_slow {r : ℕ → ℕ} {c : Code} (hc : Computes c (diag r)) {x : ℕ}
    (hx : (Nat.unpair x).1 = encode c) :
    diag r x = 1 ∧ r (bound x) < cost c x := by
  have hcx : ofNat Code (Nat.unpair x).1 = c := by rw [hx, Denumerable.ofNat_encode]
  have hne : evaln (r (bound x)) c x ≠ some 1 := by
    intro h
    have h1 : (1 : ℕ) ∈ eval c x := evaln_sound h
    rw [hc x] at h1
    have hd1 : diag r x = 1 := (Part.mem_some_iff.1 h1).symm
    have hd0 : diag r x = 0 := by simp [diag, hcx, h]
    omega
  have hdiag : diag r x = 1 := by
    simp only [diag, hcx]
    rw [if_neg hne]
  have hnone : evaln (r (bound x)) c x = Option.none := by
    rcases h : evaln (r (bound x)) c x with - | v
    · rfl
    · have hv : v ∈ eval c x := evaln_sound h
      rw [hc x] at hv
      have hvd : v = diag r x := by simpa using hv
      rw [hvd, hdiag] at h
      exact absurd h hne
  refine ⟨hdiag, ?_⟩
  have hdom : ∃ j, (evaln j c x).isSome := by
    have h1 : diag r x ∈ eval c x := by rw [hc x]; simp
    obtain ⟨k, hk⟩ := evaln_complete.1 h1
    exact ⟨k, Option.isSome_of_mem hk⟩
  exact lt_cost hdom (by simp [hnone])

/-- The patched version of a program `c` for `diag r` is again a program for `diag r`. -/
theorem patch_computes {r : ℕ → ℕ} {c : Code} (hc : Computes c (diag r)) :
    Computes (patch (encode c)) (diag r) := by
  intro x
  rw [patch_eval]
  by_cases hx : (Nat.unpair x).1 = encode c
  · rw [if_pos hx, (diag_slow hc hx).1]
  · rw [if_neg hx, Denumerable.ofNat_encode, hc x]

/-- **Speedup with a prescribed factor.**  For every computable `r : ℕ → ℕ` there is a decision
problem `f` (a computable `{0,1}`-valued function) which is solvable, but such that every program
`c` computing `f` is beaten by some program `c'` computing `f` by the factor `r` on infinitely
many inputs: `r (cost c' x) < cost c x`. -/
theorem blum_speedup_factor {r : ℕ → ℕ} (hr : Computable r) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ x, f x ≤ 1) ∧ (∃ c : Code, Computes c f) ∧
      ∀ c : Code, Computes c f →
        ∃ c' : Code, Computes c' f ∧ {x | r (cost c' x) < cost c x}.Infinite := by
  refine ⟨diag r, diag_computable hr, diag_le_one r, ?_, ?_⟩
  · obtain ⟨c, hcode⟩ := exists_code.1 (Partrec.nat_iff.1 (diag_computable hr).partrec)
    exact ⟨c, fun x => by rw [hcode]; rfl⟩
  · intro c hc
    refine ⟨patch (encode c), patch_computes hc, ?_⟩
    have hsub : (Set.range fun y : ℕ => Nat.pair (encode c) y) ⊆
        {x | r (cost (patch (encode c)) x) < cost c x} := by
      rintro _ ⟨y, rfl⟩
      have hx : (Nat.unpair (Nat.pair (encode c) y)).1 = encode c := by simp
      have h1 : cost (patch (encode c)) (Nat.pair (encode c) y)
          = bound (Nat.pair (encode c) y) := by rw [bound, hx]
      rw [Set.mem_setOf_eq, h1]
      exact (diag_slow hc hx).2
    refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
    intro a b hab
    simpa using hab

/-- **Blum speedup (there are problems with no fastest algorithm).**  There is a decision problem
`f` (a computable `{0,1}`-valued function) which is solvable, but for which every algorithm can be
beaten: for every program `c` computing `f` there is another program `c'` computing `f` which is
strictly faster than `c` on infinitely many inputs. -/
theorem blum_speedup :
    ∃ f : ℕ → ℕ, Computable f ∧ (∀ x, f x ≤ 1) ∧ (∃ c : Code, Computes c f) ∧
      ∀ c : Code, Computes c f →
        ∃ c' : Code, Computes c' f ∧ {x | cost c' x < cost c x}.Infinite :=
  blum_speedup_factor (r := id) Computable.id

/-- Consequence: for the problem `f` produced above there is no fastest algorithm, i.e. no program
computing `f` whose running time is at most that of every other program computing `f`. -/
theorem no_fastest_algorithm :
    ∃ f : ℕ → ℕ, Computable f ∧ (∃ c : Code, Computes c f) ∧
      ¬ ∃ c : Code, Computes c f ∧ ∀ c' : Code, Computes c' f → ∀ x, cost c x ≤ cost c' x := by
  obtain ⟨f, hf, -, hex, hspeed⟩ := blum_speedup
  refine ⟨f, hf, hex, ?_⟩
  rintro ⟨c, hc, hmin⟩
  obtain ⟨c', hc', hinf⟩ := hspeed c hc
  obtain ⟨x, hx⟩ := hinf.nonempty
  exact absurd (hmin c' hc' x) (not_le.2 hx)

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

