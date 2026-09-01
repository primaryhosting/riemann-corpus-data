/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Coverage

universe u v

/-- The result of running the isolation engine on an input: either it produced an
answer, or it *bailed* because the input was not recognized as covered. -/
inductive Outcome (ω : Type v) : Type v
  | ok (o : ω) : Outcome ω
  | bail : Outcome ω

/-- A model of the isolation engine: a coverage test `recognized`, a `handler`
computing an answer, and the intended `spec` relating inputs to acceptable answers. -/
structure Engine (ι : Type u) (ω : Type v) where
  /-- Coverage test: does the engine claim to handle this input? -/
  recognized : ι → Bool
  /-- The answer produced on inputs that pass the coverage test. -/
  handler : ι → ω
  /-- The intended input/output specification. -/
  spec : ι → ω → Prop

variable {ι : Type u} {ω : Type v}

/-- The engine answers on recognized inputs and bails on everything else. -/
def Engine.run (E : Engine ι ω) (i : ι) : Outcome ω :=
  if E.recognized i then Outcome.ok (E.handler i) else Outcome.bail

/-- Coverage hypothesis: on every recognized input the handler meets the spec. -/
def Engine.Covers (E : Engine ι ω) : Prop :=
  ∀ i : ι, E.recognized i = true → E.spec i (E.handler i)

/-- Soundness: every answer the engine actually emits satisfies the spec. -/
def Engine.Sound (E : Engine ι ω) : Prop :=
  ∀ (i : ι) (o : ω), E.run i = Outcome.ok o → E.spec i o

/-- The engine emits `o` exactly when the input is recognized and `o` is the
handler's answer. -/
@[simp] theorem Engine.run_eq_ok_iff (E : Engine ι ω) (i : ι) (o : ω) :
    E.run i = Outcome.ok o ↔ E.recognized i = true ∧ o = E.handler i := by
  unfold Engine.run
  cases h : E.recognized i with
  | false => simp
  | true => simp [Outcome.ok.injEq, eq_comm]

/-- The engine bails exactly on the inputs outside its coverage. -/
@[simp] theorem Engine.run_eq_bail_iff (E : Engine ι ω) (i : ι) :
    E.run i = Outcome.bail ↔ E.recognized i = false := by
  unfold Engine.run
  cases h : E.recognized i with
  | false => simp
  | true => simp

/-- **Main theorem.** An engine that bails on every unrecognized input is sound,
provided its handler is correct on the inputs it does recognize: no unverified
answer can escape, because unrecognized inputs produce no answer at all. -/
theorem bail_on_unrecognized_is_sound (E : Engine ι ω) (hcov : E.Covers) : E.Sound := by
  intro i o hrun
  rw [Engine.run_eq_ok_iff] at hrun
  obtain ⟨hrec, rfl⟩ := hrun
  exact hcov i hrec

/-- Contrapositive form: if an answer would violate the spec, the engine never emits it. -/
theorem no_bad_output_of_covers (E : Engine ι ω) (hcov : E.Covers)
    (i : ι) (o : ω) (hbad : ¬ E.spec i o) : E.run i ≠ Outcome.ok o :=
  fun hrun => hbad (bail_on_unrecognized_is_sound E hcov i o hrun)

/-- Soundness of the bail-on-unrecognized engine is *equivalent* to coverage
correctness: nothing weaker than a handler correct on recognized inputs suffices. -/
theorem sound_iff_covers (E : Engine ι ω) : E.Sound ↔ E.Covers := by
  constructor
  · intro hs i hrec
    exact hs i (E.handler i) (by simp [hrec])
  · exact bail_on_unrecognized_is_sound E

/-- Completeness on covered inputs: the engine never bails on a recognized input. -/
theorem run_ne_bail_of_recognized (E : Engine ι ω) (i : ι)
    (hrec : E.recognized i = true) : E.run i ≠ Outcome.bail := by
  simp [Engine.run_eq_bail_iff, hrec]

end PCA.Coverage

