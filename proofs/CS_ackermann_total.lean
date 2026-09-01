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

namespace CS

/-- The graph of the Ackermann function, given as an inductively defined relation:
`AckRel m n v` means "the Ackermann function at `(m, n)` evaluates to `v`". -/
inductive AckRel : ℕ → ℕ → ℕ → Prop
  | zero (n : ℕ) : AckRel 0 n (n + 1)
  | succZero {m v : ℕ} : AckRel m 1 v → AckRel (m + 1) 0 v
  | succSucc {m n v w : ℕ} : AckRel (m + 1) n v → AckRel m v w → AckRel (m + 1) (n + 1) w

/-- The Ackermann function, defined by recursion on the lexicographic order on `ℕ × ℕ`. -/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

/-- `ack` computes a value in the graph `AckRel`, i.e. the Ackermann recursion always
returns a value. -/
theorem ackRel_ack : ∀ m n : ℕ, AckRel m n (ack m n)
  | 0, n => by rw [ack]; exact AckRel.zero n
  | m + 1, 0 => by rw [ack]; exact AckRel.succZero (ackRel_ack m 1)
  | m + 1, n + 1 => by
      rw [ack]
      exact AckRel.succSucc (ackRel_ack (m + 1) n) (ackRel_ack m (ack (m + 1) n))
termination_by m n => (m, n)

/-- The Ackermann recursion is deterministic: it assigns at most one value to each input. -/
theorem AckRel.det {m n v : ℕ} (h : AckRel m n v) : ∀ {w : ℕ}, AckRel m n w → v = w := by
  induction h with
  | zero n => intro w hw; cases hw; rfl
  | succZero _ ih => intro w hw; cases hw with | succZero hw => exact ih hw
  | succSucc _ _ ih1 ih2 =>
      intro u hu
      cases hu with
      | succSucc h1' h2' =>
          have hv := ih1 h1'
          subst hv
          exact ih2 h2'

/-- **The Ackermann function is total**: for every pair `(m, n)` of naturals the Ackermann
recursion (which recurses on the lexicographic order on `ℕ × ℕ`) determines exactly one
value. -/
theorem ackermann_total : ∀ m n : ℕ, ∃! v : ℕ, AckRel m n v := by
  intro m n
  exact ⟨ack m n, ackRel_ack m n, fun y hy => hy.det (ackRel_ack m n)⟩

/-- The defining equations of the Ackermann function. -/
theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]

theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw [ack]

theorem ack_succ_succ (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

end CS

