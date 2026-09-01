import Mathlib
/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

set_option grind.warning false

namespace QC

/-! ## Setup

We model a two–qubit system by its amplitude function on the computational basis
`Bool × Bool`, the first component being the query register and the second the
answer register.  All gates are the usual `2 × 2` (resp. `4 × 4`) unitaries written
out on amplitudes. -/

/-- The scalar `1/√2` occurring in the Hadamard gate. -/
noncomputable def sq2inv : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- `sgn b = (-1)^b`. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- A two–qubit state, given by its amplitudes in the computational basis. -/
abbrev State := Bool × Bool → ℂ

/-- Hadamard gate on the first (query) qubit:
`H|x⟩ = 2^(-1/2) ∑_{x'} (-1)^{x·x'} |x'⟩`. -/
noncomputable def hadFirst (v : State) : State :=
  fun p => sq2inv * ∑ x : Bool, sgn (p.1 && x) * v (x, p.2)

/-- Hadamard gate on the second (answer) qubit. -/
noncomputable def hadSecond (v : State) : State :=
  fun p => sq2inv * ∑ y : Bool, sgn (p.2 && y) * v (p.1, y)

/-- The oracle `U_f |x, y⟩ = |x, y ⊕ f x⟩`.  Since `U_f` is a permutation matrix which is
its own inverse, on amplitudes it acts by `(U_f ψ)(x, y) = ψ (x, y ⊕ f x)`. -/
def oracle (f : Bool → Bool) (v : State) : State :=
  fun p => v (p.1, xor p.2 (f p.1))

/-- The input state `|0⟩ ⊗ |1⟩`. -/
def init : State := fun p => if p = (false, true) then 1 else 0

/-- The output state of Deutsch's algorithm:
`(H ⊗ I) U_f (H ⊗ H) (|0⟩ ⊗ |1⟩)`.  The oracle `U_f` is applied exactly once. -/
noncomputable def deutschFinal (f : Bool → Bool) : State :=
  hadFirst (oracle f (hadFirst (hadSecond init)))

/-- Probability that measuring the first (query) qubit of the output state yields `0`. -/
noncomputable def prob0 (f : Bool → Bool) : ℝ :=
  ‖deutschFinal f (false, false)‖ ^ 2 + ‖deutschFinal f (false, true)‖ ^ 2

/-- Probability that measuring the first (query) qubit of the output state yields `1`. -/
noncomputable def prob1 (f : Bool → Bool) : ℝ :=
  ‖deutschFinal f (true, false)‖ ^ 2 + ‖deutschFinal f (true, true)‖ ^ 2

/-! ## Correctness of Deutsch's algorithm -/

/-- **Deutsch's algorithm is correct.**  After a single query to the oracle `U_f`,
measuring the query register of `(H ⊗ I) U_f (H ⊗ H) |0,1⟩` returns `0` with
probability `1` when `f` is constant, and with probability `0` (i.e. it returns `1`
with certainty) when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    prob0 f = if f false = f true then 1 else 0 := by
  cases h0 : f false <;> cases h1 : f true <;>
    simp [prob0, deutschFinal, hadFirst, hadSecond, oracle, init, sgn, h0, h1,
      sq2inv] <;> ring_nf <;> norm_num

/-- Complementary form: the query register measures to `1` exactly when `f` is balanced. -/
theorem deutsch_prob1 (f : Bool → Bool) :
    prob1 f = if f false = f true then 0 else 1 := by
  cases h0 : f false <;> cases h1 : f true <;>
    simp [prob1, deutschFinal, hadFirst, hadSecond, oracle, init, sgn, h0, h1,
      sq2inv] <;> ring_nf <;> norm_num

/-- The two outcome probabilities sum to `1`: the output state is normalised. -/
theorem deutsch_prob_add (f : Bool → Bool) : prob0 f + prob1 f = 1 := by
  rw [deutsch_correct, deutsch_prob1]
  split <;> norm_num

end QC

