import Mathlib

/-!
# Refinement COMPOSES — a mechanized 3-level seL4-style refinement chain

This module generalizes the single-step forward-simulation (data-refinement) pattern of
`Brockian/HighAssuranceRefinement.lean` from ONE refinement to a whole **chain**, and
proves the two facts that make the seL4 proof architecture work:

1. **Refinement is transitive** — forward simulations *compose*.  Given a simulation of
   layer B by A and a simulation of layer C by B (over a shared operation alphabet), their
   relational composition is again a forward simulation of C by A (`sim_compose`), and this
   lifts to whole runs by induction (`Sim.run`, `chain_run`).
2. **Safety transports across the whole chain** — a safety property proved once on the most
   abstract layer is carried, through *both* refinement layers, down onto the most concrete
   layer on every reachable concrete state (`safety_transported_chain`).

This mirrors seL4's ACTUAL structure, which is a 3-level chain
        abstract spec  ⊒  executable spec  ⊒  C implementation,
where the top-level security theorems are obtained on the abstract spec and then transported
to C precisely *because* the two refinement steps compose.

## Part A (general).  A reusable forward-simulation combinator.

`Sim Op SA SB stepA stepB` packages a forward simulation of transition system
`(SB, stepB)` by `(SA, stepA)` over a shared op alphabet `Op`: a coupling relation `R`, a
*source* invariant `invA`, a *target* invariant `invB`, and the single-step obligation that a
matching op on both systems preserves both invariants and the coupling.  Carrying invariants
on **both** sides is essential and faithful: the invariant needed to discharge a layer's
obligation may live on that layer's *source* (as `Nodup` does for the executable⊒C step
below), and it is exactly the *target* invariant of the layer above.  `sim_compose` threads
that shared middle invariant through the composition.

## Part B (concrete 3-level instance).

Three genuinely different representations of a capability set:
* ABSTRACT     `Finset ℕ`   — a mathematical set (no order, no duplicates).
* INTERMEDIATE `List ℕ`     — an ordered allocation log that may duplicate (invariant `Nodup`).
* CONCRETE     `ℕ → Bool`   — a bitmap / bit-array, exactly how a kernel stores presence.
The three couplings, composed, refine the bitmap by the abstract set, and the abstract safety
property `0 ∉ set` transports to the concrete `bitmap 0 = false`.
-/

namespace Brockian.HighAssurance.RefinementChain

/-! ## Part A — the general forward-simulation combinator -/

/-- **Forward simulation** of the transition system `(SB, stepB)` by `(SA, stepA)` over a
shared operation alphabet `Op`.  `R` couples the two state spaces; `invA`/`invB` are the
source/target validity invariants; `step` is the one-step data-refinement obligation. -/
structure Sim (Op : Type) (SA SB : Type)
    (stepA : Op → SA → SA) (stepB : Op → SB → SB) where
  /-- Coupling / abstraction relation between the two layers. -/
  R : SA → SB → Prop
  /-- Validity invariant of the source (more abstract) layer. -/
  invA : SA → Prop
  /-- Validity invariant of the target (more concrete) layer. -/
  invB : SB → Prop
  /-- One matching step preserves both invariants and the coupling. -/
  step : ∀ (op : Op) (a : SA) (b : SB),
    invA a → invB b → R a b →
      invA (stepA op a) ∧ invB (stepB op b) ∧ R (stepA op a) (stepB op b)

/-- Run a transition system through a whole list of ops (left to right). -/
def runWith {Op S : Type} (step : Op → S → S) (ops : List Op) (s : S) : S :=
  ops.foldl (fun s op => step op s) s

/-- **Refinement of runs.**  A single forward simulation lifts, by induction on the op
sequence, to preservation of both invariants and the coupling over an ARBITRARY run. -/
theorem Sim.run {Op SA SB : Type} {stepA : Op → SA → SA} {stepB : Op → SB → SB}
    (S : Sim Op SA SB stepA stepB) :
    ∀ (ops : List Op) (a : SA) (b : SB),
      S.invA a → S.invB b → S.R a b →
        S.invA (runWith stepA ops a) ∧ S.invB (runWith stepB ops b)
          ∧ S.R (runWith stepA ops a) (runWith stepB ops b) := by
  intro ops
  induction ops with
  | nil => intro a b ha hb hR; exact ⟨ha, hb, hR⟩
  | cons op rest ih =>
      intro a b ha hb hR
      obtain ⟨ha', hb', hR'⟩ := S.step op a b ha hb hR
      simpa [runWith, List.foldl_cons] using ih (stepA op a) (stepB op b) ha' hb' hR'

/-- **Composition of forward simulations (refinement is transitive).**  Given a simulation
of `(SB, stepB)` by `(SA, stepA)` and one of `(SC, stepC)` by `(SB, stepB)`, whose middle
invariants agree (`hInvMid`), their relational composition
`R_AC a c := ∃ b, invB b ∧ R_AB a b ∧ R_BC b c` — which explicitly REMEMBERS the middle
invariant — is again a forward simulation, of `(SC, stepC)` by `(SA, stepA)`. -/
def sim_compose {Op SA SB SC : Type}
    {stepA : Op → SA → SA} {stepB : Op → SB → SB} {stepC : Op → SC → SC}
    (sAB : Sim Op SA SB stepA stepB) (sBC : Sim Op SB SC stepB stepC)
    (hInvMid : ∀ b, sAB.invB b ↔ sBC.invA b) :
    Sim Op SA SC stepA stepC where
  R := fun a c => ∃ b, sAB.invB b ∧ sAB.R a b ∧ sBC.R b c
  invA := sAB.invA
  invB := sBC.invB
  step := by
    intro op a c ha hc hR
    obtain ⟨b, hbInv, hRab, hRbc⟩ := hR
    obtain ⟨ha', hb', hRab'⟩ := sAB.step op a b ha hbInv hRab
    have hbInv' : sBC.invA b := (hInvMid b).mp hbInv
    obtain ⟨_, hc', hRbc'⟩ := sBC.step op b c hbInv' hc hRbc
    exact ⟨ha', hc', stepB op b, hb', hRab', hRbc'⟩

/-- **Chain run.**  Composition plus run-lifting: two composed forward simulations preserve
the (existentially middle-witnessed) coupling and both end invariants over an ARBITRARY run
across the whole `SA ⊒ SB ⊒ SC` chain. -/
theorem chain_run {Op SA SB SC : Type}
    {stepA : Op → SA → SA} {stepB : Op → SB → SB} {stepC : Op → SC → SC}
    (sAB : Sim Op SA SB stepA stepB) (sBC : Sim Op SB SC stepB stepC)
    (hInvMid : ∀ b, sAB.invB b ↔ sBC.invA b)
    (ops : List Op) (a : SA) (c : SC)
    (ha : sAB.invA a) (hc : sBC.invB c)
    (hR : ∃ b, sAB.invB b ∧ sAB.R a b ∧ sBC.R b c) :
    sAB.invA (runWith stepA ops a) ∧ sBC.invB (runWith stepC ops c)
      ∧ (∃ b, sAB.invB b ∧ sAB.R (runWith stepA ops a) b
                ∧ sBC.R b (runWith stepC ops c)) :=
  (sim_compose sAB sBC hInvMid).run ops a c ha hc hR

/-! ## Part B — a concrete 3-level instance (non-vacuity) -/

/-- Kernel operations, shared by all three layers.  `alloc n` requests capability `n`;
`revoke n` releases it.  Capability `0` is the reserved *null capability*. -/
inductive Op where
  | alloc  (n : ℕ)
  | revoke (n : ℕ)
  deriving DecidableEq, Repr

/-! ### Level 1 (ABSTRACT): capabilities as a `Finset ℕ`. -/

/-- Abstract step: `alloc` inserts (unless the null cap `0`), `revoke` deletes. -/
def aStep : Op → Finset ℕ → Finset ℕ
  | Op.alloc n,  s => if n = 0 then s else insert n s
  | Op.revoke n, s => s.erase n

/-! ### Level 2 (INTERMEDIATE): an allocation log as a `List ℕ` (ordered, may duplicate). -/

/-- Intermediate step, mirroring `aStep` on the list.  `alloc` pushes front (guarding the
null cap and double-allocation); `revoke` uses `List.erase` (removes the FIRST occurrence). -/
def iStep : Op → List ℕ → List ℕ
  | Op.alloc n,  l => if n = 0 then l else (if n ∈ l then l else n :: l)
  | Op.revoke n, l => l.erase n

/-! ### Level 3 (CONCRETE): a bitmap `ℕ → Bool` (a bit-array, as a kernel really stores it). -/

/-- Concrete step on the bitmap.  `alloc n` sets bit `n` (unless the null cap); `revoke n`
clears bit `n`.  Note the bitmap is naturally duplicate-free and order-free. -/
def cStep : Op → (ℕ → Bool) → (ℕ → Bool)
  | Op.alloc n,  f => if n = 0 then f else (fun m => decide (m = n) || f m)
  | Op.revoke n, f => fun m => (!decide (m = n)) && f m

/-- Coupling ABSTRACT ⊒ INTERMEDIATE: the abstract set is the set of log elements. -/
def R_AI (a : Finset ℕ) (i : List ℕ) : Prop := a = i.toFinset

/-- Coupling INTERMEDIATE ⊒ CONCRETE: the bitmap's true-set equals the log's element set. -/
def R_IC (i : List ℕ) (f : ℕ → Bool) : Prop := ∀ m, f m = true ↔ m ∈ i

/-- The intermediate validity invariant: the log has no duplicates. -/
def invLog (i : List ℕ) : Prop := i.Nodup

/-- **Layer 1 simulation: `Finset ⊒ List`.**  Source invariant trivial; target invariant
`Nodup`.  This is the reference single-step refinement, packaged as a `Sim`. -/
def simAI : Sim Op (Finset ℕ) (List ℕ) aStep iStep where
  R := R_AI
  invA := fun _ => True
  invB := invLog
  step := by
    intro op a i _ha hInv hR
    subst hR
    cases op with
    | alloc n =>
        by_cases h0 : n = 0
        · subst h0
          refine ⟨trivial, ?_, ?_⟩
          · simpa [iStep] using hInv
          · simp [aStep, iStep, R_AI]
        · by_cases hmem : n ∈ i
          · refine ⟨trivial, ?_, ?_⟩
            · simp only [iStep, if_neg h0, if_pos hmem]; exact hInv
            · have hins : insert n i.toFinset = i.toFinset :=
                Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hmem)
              simp [aStep, iStep, R_AI, h0, hmem, hins]
          · refine ⟨trivial, ?_, ?_⟩
            · simp only [iStep, if_neg h0, if_neg hmem]
              exact List.nodup_cons.mpr ⟨hmem, hInv⟩
            · simp [aStep, iStep, R_AI, h0, hmem, List.toFinset_cons]
    | revoke n =>
        refine ⟨trivial, ?_, ?_⟩
        · simpa [iStep, invLog] using hInv.erase n
        · simp only [aStep, iStep, R_AI]
          ext x
          simp only [Finset.mem_erase, List.mem_toFinset, hInv.mem_erase_iff, ne_eq]

/-- **Layer 2 simulation: `List ⊒ bitmap`.**  Source invariant `Nodup` (load-bearing on the
`revoke` case), target invariant trivial.  This is the NEW refinement layer. -/
def simIC : Sim Op (List ℕ) (ℕ → Bool) iStep cStep where
  R := R_IC
  invA := invLog
  invB := fun _ => True
  step := by
    intro op i f hInv _hf hR
    cases op with
    | alloc n =>
        by_cases h0 : n = 0
        · subst h0
          refine ⟨?_, trivial, ?_⟩
          · simpa [iStep] using hInv
          · simpa [cStep, iStep] using hR
        · by_cases hmem : n ∈ i
          · refine ⟨?_, trivial, ?_⟩
            · simp only [iStep, if_neg h0, if_pos hmem]; exact hInv
            · intro m
              simp only [cStep, iStep, if_neg h0, if_pos hmem]
              by_cases hmn : m = n
              · subst hmn; simp [hmem]
              · simp [hmn, hR m]
          · refine ⟨?_, trivial, ?_⟩
            · simp only [iStep, if_neg h0, if_neg hmem]
              exact List.nodup_cons.mpr ⟨hmem, hInv⟩
            · intro m
              simp only [cStep, iStep, if_neg h0, if_neg hmem, List.mem_cons]
              by_cases hmn : m = n
              · subst hmn; simp
              · simp [hmn, hR m]
    | revoke n =>
        refine ⟨?_, trivial, ?_⟩
        · simpa [iStep, invLog] using hInv.erase n
        · intro m
          simp only [cStep, iStep, hInv.mem_erase_iff]
          by_cases hmn : m = n
          · subst hmn; simp
          · simp [hmn, hR m]

/-- Middle-invariant compatibility: `simAI`'s target invariant IS `simIC`'s source invariant
(both are `Nodup`).  This is precisely the shared executable-spec invariant. -/
theorem invMid_compat : ∀ i, simAI.invB i ↔ simIC.invA i := fun _ => Iff.rfl

/-- **The composed 3-level refinement: `Finset ⊒ bitmap`**, obtained purely by composing the
two layers with `sim_compose`.  Its coupling remembers the intermediate `Nodup` witness. -/
def chainSim : Sim Op (Finset ℕ) (ℕ → Bool) aStep cStep :=
  sim_compose simAI simIC invMid_compat

/-! ### Transporting a safety property across the WHOLE chain -/

/-- Abstract safety: the reserved null capability `0` is never allocated. -/
def SafeA (s : Finset ℕ) : Prop := (0 : ℕ) ∉ s

/-- Concrete safety: the null-capability bit is never set. -/
def SafeC (f : ℕ → Bool) : Prop := f 0 = false

/-- `SafeA` is preserved by every abstract step (the "easy" high-level proof). -/
theorem safeA_step (op : Op) (s : Finset ℕ) (h : SafeA s) : SafeA (aStep op s) := by
  cases op with
  | alloc n =>
      by_cases h0 : n = 0
      · subst h0; simpa [aStep] using h
      · simp only [aStep, if_neg h0, SafeA, Finset.mem_insert, not_or]
        exact ⟨fun hz => h0 hz.symm, h⟩
  | revoke n =>
      simp only [aStep, SafeA]
      exact fun hmem => h (Finset.mem_of_mem_erase hmem)

/-- `SafeA` holds along an entire abstract run. -/
theorem safeA_run : ∀ (ops : List Op) (s : Finset ℕ), SafeA s → SafeA (runWith aStep ops s) := by
  intro ops
  induction ops with
  | nil => intro s h; exact h
  | cons op rest ih =>
      intro s h
      simpa [runWith, List.foldl_cons] using ih (aStep op s) (safeA_step op s h)

/-- Safety pulls back across the WHOLE composed chain relation: if the abstract state is safe
and it is chain-coupled (through an intermediate log) to the bitmap, the bitmap is safe. -/
theorem safeC_of_chain (a : Finset ℕ) (f : ℕ → Bool)
    (hR : ∃ i, i.Nodup ∧ R_AI a i ∧ R_IC i f) (h : SafeA a) : SafeC f := by
  obtain ⟨i, _hnd, hAI, hIC⟩ := hR
  have h0i : (0 : ℕ) ∉ i := by
    intro hmem
    exact h (by rw [hAI]; exact List.mem_toFinset.mpr hmem)
  show f 0 = false
  cases hf : f 0 with
  | false => rfl
  | true => exact absurd ((hIC 0).mp hf) h0i

/-- **Safety transported across the 3-level chain.**  Prove `SafeA` once on the abstract
`Finset` spec; then, through BOTH refinement layers (`chainSim = simAI ∘ simIC`), it secures
the concrete bitmap on every reachable concrete state.  This is exactly how seL4 obtains its
C-level guarantees: establish the property on the abstract spec and ride it down the composed
refinement `abstract ⊒ executable ⊒ C`. -/
theorem safety_transported_chain (ops : List Op)
    (a : Finset ℕ) (i : List ℕ) (f : ℕ → Bool)
    (hInv : i.Nodup) (hAI : R_AI a i) (hIC : R_IC i f) (hSafe : SafeA a) :
    SafeC (runWith cStep ops f) := by
  have hR0 : chainSim.R a f := ⟨i, hInv, hAI, hIC⟩
  obtain ⟨_, _, hRrun⟩ := chainSim.run ops a f trivial trivial hR0
  exact safeC_of_chain (runWith aStep ops a) (runWith cStep ops f) hRrun
    (safeA_run ops a hSafe)

/-! ### Non-vacuity witnesses -/

/-- The three levels are GENUINELY different objects: a `Finset` (unordered, dedup'd), a
`List` in the OPPOSITE order that could carry duplicates, and a `Bool`-valued bitmap. -/
def demoBmp : ℕ → Bool := fun m => decide (m = 1) || decide (m = 2)

/-- **All three levels R-related through the composed chain relation, yet structurally
distinct.**  Abstract `{1,2}`, intermediate log `[2,1]` (reversed order), concrete bitmap
`demoBmp` — coupled by `chainSim.R`. -/
theorem three_levels_distinct_but_coupled :
    chainSim.R ({1, 2} : Finset ℕ) demoBmp := by
  refine ⟨[2, 1], ?_, ?_, ?_⟩
  · show ([2, 1] : List ℕ).Nodup; decide
  · show ({1, 2} : Finset ℕ) = ([2, 1] : List ℕ).toFinset; decide
  · intro m
    simp only [demoBmp, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false]
    tauto

/-- The intermediate invariant is non-trivial: it excludes the duplicated log `[1,1]`. -/
example : ¬ ([1, 1] : List ℕ).Nodup := by decide

/-- The coupling genuinely forgets order: `{1,2}` couples to the reversed log `[2,1]`. -/
example : R_AI ({1, 2} : Finset ℕ) [2, 1] := by unfold R_AI; decide

/-- **Why the intermediate invariant is load-bearing for the whole chain.**  Take the invalid
log `[1,1]` (duplicated, so `Nodup` fails), coupled to abstract `{1}`.  After `revoke 1` the
abstract set becomes `∅`, but `List.erase` removes only ONE `1`, leaving `[1]` whose element
set is `{1} ≠ ∅` — so the abstract⊒intermediate coupling BREAKS, hence the whole chain breaks.
`Nodup` (threaded through `sim_compose`'s middle invariant) is exactly what excludes this. -/
theorem chain_needs_Nodup :
    R_AI ({1} : Finset ℕ) [1, 1] ∧ ¬ ([1, 1] : List ℕ).Nodup ∧
      ¬ R_AI (aStep (Op.revoke 1) {1}) (iStep (Op.revoke 1) [1, 1]) := by
  refine ⟨?_, ?_, ?_⟩
  · show ({1} : Finset ℕ) = ([1, 1] : List ℕ).toFinset; decide
  · decide
  · show ¬ (aStep (Op.revoke 1) {1} = (iStep (Op.revoke 1) [1, 1]).toFinset)
    simp only [aStep, iStep]
    decide

end Brockian.HighAssurance.RefinementChain
