import Mathlib

/-!
# Refinement via Forward Simulation — a mechanized seL4-style data refinement

This module demonstrates, end to end and machine-checked, the proof METHODOLOGY at
the heart of the seL4 verified microkernel: **refinement** established by **forward
simulation** (data refinement), used to **transport** a safety property proved at the
abstract level down onto the executable/implementation level.

The running example is a tiny capability-allocator kernel operation set.

* ABSTRACT layer  — `AState := Finset ℕ`  (the set of currently allocated capabilities;
  a mathematical set, no duplicates, no order).
* CONCRETE layer  — `CState := List ℕ`   (an implementation-like allocation log: an
  ordered list that CAN contain duplicates), together with a validity invariant
  `Inv` = "the log has no duplicates" (`List.Nodup`).
* COUPLING relation `R s l := s = l.toFinset` — the abstract set is the *set of elements*
  of the concrete log. This is a genuine abstraction: the concrete rep carries order and
  potential duplication that `R` deliberately forgets.

We prove the standard **forward simulation** obligation (`Inv` and `R` are preserved by
matching steps), lift it to whole **runs** by induction, and then **transport** a safety
property (`SafeA` = "the null/reserved capability `0` is never allocated") from the
abstract kernel model to the concrete implementation on every reachable concrete state.

NON-VACUITY. `R` couples structurally different representations (a `Finset` vs a `List`
that may have order and — absent the invariant — duplicates). The invariant `Inv` is
load-bearing: the `revoke` step is modelled realistically as `List.erase`, which removes
only the *first* occurrence. If the log held a duplicate `[n, n]`, `erase` would leave an
`n` behind, so the concrete state would still contain `n` while the abstract state has
dropped it — breaking `R`. `Nodup` rules that out. See `forward_simulation_needs_Inv`
below for the concrete witness where `R` FAILS without the invariant.
-/

namespace Brockian.HighAssurance.Refinement

/-- Kernel operations, shared by both layers. `alloc n` requests capability `n`;
`revoke n` releases it. Capability `0` is the reserved *null capability* and must
never be handed out (kernel policy enforced by `alloc`). -/
inductive Op where
  | alloc  (n : ℕ)
  | revoke (n : ℕ)
  deriving DecidableEq, Repr

/-! ## Abstract layer: capabilities as a `Finset` -/

/-- Abstract state: the *set* of allocated capabilities. -/
abbrev AState : Type := Finset ℕ

/-- Abstract step. `alloc n` inserts `n` unless it is the reserved null cap `0`;
`revoke n` deletes `n`. -/
def aStep : Op → AState → AState
  | Op.alloc n,  s => if n = 0 then s else insert n s
  | Op.revoke n, s => s.erase n

/-! ## Concrete layer: an allocation log as a `List` (may be duplicated/ordered) -/

/-- Concrete state: an implementation-like allocation log. -/
abbrev CState : Type := List ℕ

/-- Concrete step, mirroring `aStep` on the list representation. `alloc n` pushes `n`
(guarding both the null cap and — for realism and to maintain the invariant — a
double-allocation), while `revoke n` uses `List.erase`, which removes only the FIRST
occurrence of `n`. -/
def cStep : Op → CState → CState
  | Op.alloc n,  l => if n = 0 then l else (if n ∈ l then l else n :: l)
  | Op.revoke n, l => l.erase n

/-- Concrete validity invariant: the allocation log has no duplicates. -/
def Inv (l : CState) : Prop := l.Nodup

/-- Abstraction / coupling relation: the abstract set is the set of log elements. -/
def R (s : AState) (l : CState) : Prop := s = l.toFinset

/-! ## Forward simulation (the core data-refinement obligation) -/

/-- **Forward simulation.** From a valid concrete state (`Inv c`) coupled to an abstract
state (`R a c`), a matching step on both layers preserves BOTH the invariant and the
coupling: the concrete implementation refines the abstract spec one step at a time.

The `revoke` case is exactly where `Inv` (no duplicates) is required — see the note in
the header and `forward_simulation_needs_Inv`. -/
theorem forward_simulation (op : Op) (a : AState) (c : CState)
    (hInv : Inv c) (hR : R a c) :
    Inv (cStep op c) ∧ R (aStep op a) (cStep op c) := by
  subst hR
  cases op with
  | alloc n =>
      by_cases h0 : n = 0
      · subst h0
        refine ⟨?_, ?_⟩
        · simpa [cStep] using hInv
        · simp [aStep, cStep, R]
      · by_cases hmem : n ∈ c
        · -- already allocated: no-op on both layers
          refine ⟨?_, ?_⟩
          · simpa [cStep, h0, hmem] using hInv
          · have hins : insert n c.toFinset = c.toFinset :=
              Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hmem)
            simp [aStep, cStep, R, h0, hmem, hins]
        · -- fresh allocation: push front
          refine ⟨?_, ?_⟩
          · simp only [cStep, if_neg h0, if_neg hmem]
            exact List.nodup_cons.mpr ⟨hmem, hInv⟩
          · simp [aStep, cStep, R, h0, hmem, List.toFinset_cons]
  | revoke n =>
      refine ⟨?_, ?_⟩
      · -- Inv preserved: erase keeps Nodup
        simpa [cStep, Inv] using hInv.erase n
      · -- R preserved: HERE the Nodup invariant is essential
        simp only [aStep, cStep, R]
        ext x
        simp only [Finset.mem_erase, List.mem_toFinset, hInv.mem_erase_iff, ne_eq]

/-! ## Lifting to whole runs by induction -/

/-- Run the abstract kernel through a whole list of operations (left to right). -/
def run_a (ops : List Op) (a : AState) : AState :=
  ops.foldl (fun s op => aStep op s) a

/-- Run the concrete kernel through a whole list of operations (left to right). -/
def run_c (ops : List Op) (c : CState) : CState :=
  ops.foldl (fun l op => cStep op l) c

/-- **Refinement of runs.** By induction on the operation sequence, forward simulation
composes: the invariant and the coupling hold after any number of matching steps.
This is the whole-system refinement statement (abstract run ⊒ concrete run). -/
theorem refinement_run (ops : List Op) (a : AState) (c : CState)
    (hInv : Inv c) (hR : R a c) :
    Inv (run_c ops c) ∧ R (run_a ops a) (run_c ops c) := by
  induction ops generalizing a c with
  | nil => exact ⟨hInv, hR⟩
  | cons op rest ih =>
      obtain ⟨hInv', hR'⟩ := forward_simulation op a c hInv hR
      simpa [run_a, run_c] using ih (aStep op a) (cStep op c) hInv' hR'

/-! ## Transporting a safety property abstract → concrete -/

/-- Abstract safety: the reserved null capability `0` is never allocated. -/
def SafeA (s : AState) : Prop := (0 : ℕ) ∉ s

/-- Concrete safety: the reserved null capability `0` is never present in the log. -/
def SafeC (l : CState) : Prop := (0 : ℕ) ∉ l

/-- `SafeA` is an abstract invariant: every abstract step preserves it. This is the
"easy", high-level proof one does against the clean mathematical spec — precisely the
kind of property seL4 establishes on its abstract model. -/
theorem safeA_step (op : Op) (s : AState) (h : SafeA s) : SafeA (aStep op s) := by
  cases op with
  | alloc n =>
      by_cases h0 : n = 0
      · subst h0; simpa [aStep] using h
      · simp only [aStep, if_neg h0, SafeA, Finset.mem_insert, not_or]
        exact ⟨fun hz => h0 hz.symm, h⟩
  | revoke n =>
      simp only [aStep, SafeA]
      exact fun hmem => h (Finset.mem_of_mem_erase hmem)

/-- `SafeA` holds along an entire abstract run, given it holds initially. -/
theorem safeA_run (ops : List Op) (s : AState) (h : SafeA s) : SafeA (run_a ops s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => simpa [run_a] using ih (aStep op s) (safeA_step op s h)

/-- Safety pulls back across the coupling relation: if the abstract state is safe and
`R` holds, the concrete state is safe. (`0 ∉ c.toFinset ↔ 0 ∉ c`.) -/
theorem safeC_of_safeA (a : AState) (c : CState) (hR : R a c) (h : SafeA a) : SafeC c := by
  intro hmem
  exact h (by rw [hR]; exact List.mem_toFinset.mpr hmem)

/-- **Safety transported.** The abstract safety proof, carried through refinement, secures
the concrete implementation on every reachable concrete state. This is exactly how seL4
obtains its C/executable-level guarantees: prove the property once on the abstract spec
(`safeA_run`), then transport it down the refinement (`refinement_run` + `R`). -/
theorem safety_transported (ops : List Op) (a : AState) (c : CState)
    (hInv : Inv c) (hR : R a c) (hSafeA0 : SafeA a) : SafeC (run_c ops c) := by
  obtain ⟨_, hR'⟩ := refinement_run ops a c hInv hR
  exact safeC_of_safeA (run_a ops a) (run_c ops c) hR' (safeA_run ops a hSafeA0)

/-! ## Non-vacuity witnesses -/

/-- The coupling relates STRUCTURALLY different representations: an unordered `Finset`
`{1, 2}` and a concrete log `[2, 1]` with the opposite order. `R` holds because it looks
only at the underlying set. -/
example : R ({1, 2} : Finset ℕ) [2, 1] := by unfold R; decide

/-- The invariant is non-trivial: it rules out the duplicated log `[1, 1]`. -/
example : ¬ Inv [1, 1] := by unfold Inv; decide

/-- **Why the invariant is essential.** Take the invalid concrete state `[1, 1]`
(duplicated — `Inv` fails) coupled by `R` to the abstract `{1}`. After `revoke 1` the
abstract set becomes `∅`, but the concrete `List.erase` removes only ONE `1`, leaving
`[1]` whose element set is `{1} ≠ ∅`. So `R` is BROKEN by the step — forward simulation
would be false here. `Inv` (no duplicates) is exactly what excludes this state. -/
theorem forward_simulation_needs_Inv :
    R ({1} : Finset ℕ) [1, 1] ∧ ¬ Inv [1, 1] ∧
      ¬ R (aStep (Op.revoke 1) {1}) (cStep (Op.revoke 1) [1, 1]) := by
  refine ⟨by unfold R; decide, by unfold Inv; decide, ?_⟩
  -- aStep revoke 1 {1} = ∅ ; cStep revoke 1 [1,1] = [1] ; R would require ∅ = {1}
  simp only [R, aStep, cStep]
  decide

end Brockian.HighAssurance.Refinement
