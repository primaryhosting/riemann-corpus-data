class Magma (α : Type _) where op : α → α → α
@[inherit_doc] infix:65 " ◇ " => Magma.op

-- Prove: the law  x ◇ y = ((y ◇ x) ◇ z) ◇ x  (for all x y z)
-- implies  x ◇ x = x ◇ (y ◇ (y ◇ x))  (for all x y).
theorem euler_4160_3261 : ∀ (G : Type) [Magma G],
    (∀ (x y z : G), x ◇ y = ((y ◇ x) ◇ z) ◇ x) →
    (∀ (x y : G), x ◇ x = x ◇ (y ◇ (y ◇ x))) := by
  intro G _ h x y
  calc x ◇ x
      = ((x ◇ x) ◇ (y ◇ y)) ◇ x := h x x (y ◇ y)
    _ = ((((x ◇ x) ◇ y) ◇ x) ◇ (y ◇ y)) ◇ x :=
        congrArg (fun t => (t ◇ (y ◇ y)) ◇ x) (h x x y)
    _ = x ◇ ((x ◇ x) ◇ y) := (h x ((x ◇ x) ◇ y) (y ◇ y)).symm
    _ = x ◇ ((((x ◇ x) ◇ (x ◇ y)) ◇ x) ◇ y) :=
        congrArg (fun t => x ◇ (t ◇ y)) (h x x (x ◇ y))
    _ = x ◇ (((((((x ◇ y) ◇ (x ◇ x)) ◇ y) ◇ (x ◇ x))) ◇ x) ◇ y) :=
        congrArg (fun t => x ◇ ((t ◇ x) ◇ y)) (h (x ◇ x) (x ◇ y) y)
    _ = x ◇ ((((y ◇ x) ◇ (x ◇ x)) ◇ x) ◇ y) :=
        congrArg (fun t => x ◇ (((t ◇ (x ◇ x)) ◇ x) ◇ y)) (h y x (x ◇ x)).symm
    _ = x ◇ ((x ◇ y) ◇ y) :=
        congrArg (fun t => x ◇ (t ◇ y)) (h x y (x ◇ x)).symm
    _ = x ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ y) :=
        congrArg (fun t => x ◇ (t ◇ y)) (h x y y)
    _ = x ◇ (y ◇ (y ◇ x)) := congrArg (fun t => x ◇ t) (h y (y ◇ x) x).symm

