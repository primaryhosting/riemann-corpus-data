/-
  Magma-law refutation certificates (finite countermodels) — outputs of the refute
  harness `scripts/refute.py`, consolidated into one module under a single namespace.

  Each certificate exhibits an explicit order-2 magma satisfying an equational law A but
  violating a law B (kernel-checked by `decide`), and concludes A ⊬ B over order-2
  magmas. These are honest NON-implication certificates — the complement of the proving
  lane of the certificate factory. Aristotle/Harmonic-authored, independently
  AXLE-verified @4.32; axiom-clean (only `decide`).
-/
import Mathlib

namespace Brockian.MagmaLawRefutations


/-! ### assoc-not-comm -/
/-- The countermodel_assoc: an order-2 magma satisfying `x*(y*z) = (x*y)*z` but not `x*y = y*x`. -/
def op_assoc : Fin 2 → Fin 2 → Fin 2 := ![![(0 : Fin 2),(0 : Fin 2)],![(1 : Fin 2),(1 : Fin 2)]]

/-- Kernel-checked: the table satisfies A and violates B. -/
theorem countermodel_assoc : (∀ x y z : Fin 2, op_assoc (x) (op_assoc (y) (z)) = op_assoc (op_assoc (x) (y)) (z)) ∧ ¬ (∀ x y z : Fin 2, op_assoc (x) (y) = op_assoc (y) (x)) := by decide

/-- Hence A does not entail B over magmas of order 2. -/
theorem not_entails_assoc :
    ¬ ∀ (m : Fin 2 → Fin 2 → Fin 2), (∀ x y z : Fin 2, m (x) (m (y) (z)) = m (m (x) (y)) (z)) → (∀ x y z : Fin 2, m (x) (y) = m (y) (x)) :=
  fun h => countermodel_assoc.2 (h op_assoc countermodel_assoc.1)

/-! ### comm-not-assoc -/
/-- The countermodel_comm: an order-2 magma satisfying `x*y = y*x` but not `x*(y*z) = (x*y)*z`. -/
def op_comm : Fin 2 → Fin 2 → Fin 2 := ![![(1 : Fin 2),(0 : Fin 2)],![(0 : Fin 2),(0 : Fin 2)]]

/-- Kernel-checked: the table satisfies A and violates B. -/
theorem countermodel_comm : (∀ x y z : Fin 2, op_comm (x) (y) = op_comm (y) (x)) ∧ ¬ (∀ x y z : Fin 2, op_comm (x) (op_comm (y) (z)) = op_comm (op_comm (x) (y)) (z)) := by decide

/-- Hence A does not entail B over magmas of order 2. -/
theorem not_entails_comm :
    ¬ ∀ (m : Fin 2 → Fin 2 → Fin 2), (∀ x y z : Fin 2, m (x) (y) = m (y) (x)) → (∀ x y z : Fin 2, m (x) (m (y) (z)) = m (m (x) (y)) (z)) :=
  fun h => countermodel_comm.2 (h op_comm countermodel_comm.1)

/-! ### idemp-not-comm -/
/-- The countermodel_idem: an order-2 magma satisfying `x*x = x` but not `x*y = y*x`. -/
def op_idem : Fin 2 → Fin 2 → Fin 2 := ![![(0 : Fin 2),(0 : Fin 2)],![(1 : Fin 2),(1 : Fin 2)]]

/-- Kernel-checked: the table satisfies A and violates B. -/
theorem countermodel_idem : (∀ x y : Fin 2, op_idem (x) (x) = x) ∧ ¬ (∀ x y : Fin 2, op_idem (x) (y) = op_idem (y) (x)) := by decide

/-- Hence A does not entail B over magmas of order 2. -/
theorem not_entails_idem :
    ¬ ∀ (m : Fin 2 → Fin 2 → Fin 2), (∀ x y : Fin 2, m (x) (x) = x) → (∀ x y : Fin 2, m (x) (y) = m (y) (x)) :=
  fun h => countermodel_idem.2 (h op_idem countermodel_idem.1)

/-! ### mid-not-left -/
/-- The countermodel_mid: an order-2 magma satisfying `x*(y*x) = x` but not `x*y = x`. -/
def op_mid : Fin 2 → Fin 2 → Fin 2 := ![![(0 : Fin 2),(0 : Fin 2)],![(1 : Fin 2),(0 : Fin 2)]]

/-- Kernel-checked: the table satisfies A and violates B. -/
theorem countermodel_mid : (∀ x y : Fin 2, op_mid (x) (op_mid (y) (x)) = x) ∧ ¬ (∀ x y : Fin 2, op_mid (x) (y) = x) := by decide

/-- Hence A does not entail B over magmas of order 2. -/
theorem not_entails_mid :
    ¬ ∀ (m : Fin 2 → Fin 2 → Fin 2), (∀ x y : Fin 2, m (x) (m (y) (x)) = x) → (∀ x y : Fin 2, m (x) (y) = x) :=
  fun h => countermodel_mid.2 (h op_mid countermodel_mid.1)

end Brockian.MagmaLawRefutations
