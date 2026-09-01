set_option maxHeartbeats 8000000
set_option grind.warning false

class Magma (G : Type) where op : G → G → G
infixl:65 " ◇ " => Magma.op

theorem submission (G : Type) [Magma G]
    (h : ∀ (x y z w : G), x = ((y ◇ (x ◇ y)) ◇ z) ◇ w)
    : ∀ (x y z w : G), x = (y ◇ (x ◇ z)) ◇ (y ◇ w) := by
  grind

