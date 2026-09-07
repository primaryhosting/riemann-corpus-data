/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Formalization

We model a bipartite finite-dimensional quantum system: Alice's degrees of freedom are
indexed by `A`, Bob's by `B`, and a joint state is a matrix `ρ : Matrix (A × B) (A × B) ℂ`
(no positivity or normalization is needed for the argument).

* `Frontier.ptraceAlice ρ` is the partial trace over Alice's system, i.e. the reduced
  state seen by Bob.
* A completely general local operation performed by Alice is a quantum channel given in
  Kraus form by operators `K i : Matrix A A ℂ` satisfying `∑ i, (K i)ᴴ * K i = 1`
  (trace preservation).  On the joint system it acts as `ρ ↦ ∑ i, (K i ⊗ 1) ρ (K i ⊗ 1)ᴴ`,
  see `Frontier.aliceChannel`.

`Frontier.no_communication` states that Bob's reduced state is completely unaffected by
any such local operation of Alice; in particular no information can be transmitted to Bob,
however entangled the state `ρ` is.
-/

namespace Frontier

open Matrix

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq A] [DecidableEq B]

/-- The partial trace over Alice's subsystem: the reduced state seen by Bob. -/
noncomputable def ptraceAlice (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- The operator `K ⊗ 1`: it acts as `K` on Alice's system and trivially on Bob's. -/
noncomputable def localOp (K : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => K p.1 q.1 * (if p.2 = q.2 then 1 else 0)

/-- The local quantum channel applied by Alice, given by the Kraus operators `K`. -/
noncomputable def aliceChannel (K : I → Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ i : I, (localOp (B := B) (K i)) * ρ * (localOp (B := B) (K i))ᴴ

/-- Auxiliary reordering of a quadruple sum. -/
private theorem sum_comm4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h1 : ∀ a : α, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ b, f a b c d := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **No-communication theorem.**  For any bipartite state `ρ` and any local quantum
channel applied by Alice (given by Kraus operators `K i` with `∑ i, (K i)ᴴ * K i = 1`),
the reduced state on Bob's side is unchanged.  Hence local operations on one half of an
entangled pair cannot transmit any information. -/
theorem no_communication (K : I → Matrix A A ℂ) (hK : ∑ i : I, (K i)ᴴ * (K i) = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceAlice (aliceChannel K ρ) = ptraceAlice ρ := by
  ext b b'
  have key : ∀ a1 a2 : A, (∑ i : I, ∑ a : A, star (K i a a2) * K i a a1)
      = if a2 = a1 then (1 : ℂ) else 0 := by
    intro a1 a2
    have h := congrArg (fun M : Matrix A A ℂ => M a2 a1) hK
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      using h
  have step : ∀ a2 a1 : A,
      (∑ a : A, ∑ i : I, K i a a1 * ρ (a1, b) (a2, b') * star (K i a a2))
        = ρ (a1, b) (a2, b') * (if a2 = a1 then (1 : ℂ) else 0) := by
    intro a2 a1
    rw [Finset.sum_comm, ← key a1 a2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [ptraceAlice, aliceChannel, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, localOp, Fintype.sum_prod_type, ite_mul, mul_ite, zero_mul,
    mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    apply_ite (star : ℂ → ℂ), star_zero, Finset.sum_mul]
  rw [sum_comm4 (fun a i a2 a1 => K i a a1 * ρ (a1, b) (a2, b') * star (K i a a2))]
  simp only [step]
  simp

/-- Sanity check: the hypotheses are satisfiable.  A single unitary Kraus operator (a
unitary local operation of Alice) is a legitimate channel. -/
example (U : Matrix A A ℂ) (hU : Uᴴ * U = 1) :
    ∑ _i : Unit, Uᴴ * U = 1 := by simp [hU]

/-- Specialization to a unitary local operation of Alice. -/
theorem no_communication_unitary (U : Matrix A A ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceAlice (localOp (B := B) U * ρ * (localOp (B := B) U)ᴴ) = ptraceAlice ρ := by
  have h := no_communication (B := B) (I := Unit) (fun _ => U) (by simp [hU]) ρ
  simpa [aliceChannel] using h

end Frontier

