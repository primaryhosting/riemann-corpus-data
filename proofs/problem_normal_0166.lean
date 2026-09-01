import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210
theorem problem_normal_0166 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ z) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ x)) ◇ z := by
  have h2 : ∀ x z : G, x = (‹Magma G›.op x (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op z x) z) z)) := by
    exact fun x z => h x x z
  grind +splitIndPred

-- Problem normal_0169: eq2781 → eq2758
theorem problem_normal_0169 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ (x ◇ z)) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (z ◇ y)) ◇ y := by
  intro x y z
  have h1 := h x y y y
  have h2 := h y z y y
  grind

-- Problem normal_0171: eq3399 → eq3714
theorem problem_normal_0171 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (y ◇ (x ◇ w)))
    : ∀ (x : G) (y : G), x ◇ y = (x ◇ x) ◇ (y ◇ x) := by
  intro x y
  have h1 := h x y x x
  have h2 := h x x y x
  have h3 := h x x x x
  grind

-- Problem normal_0177: eq3640 → eq3323
theorem problem_normal_0177 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ y) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (y ◇ (z ◇ z)) := by
  intro x y z
  have h1 := h x y x y
  have h2 := h x y y (z ◇ z)
  grind

-- Problem normal_0187: eq1268 → eq1426
theorem problem_normal_0187 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ z) ◇ z) ◇ z))
    : ∀ (x : G), x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
  intro x
  have h1 := h x x x
  have h2 := h (x ◇ x) x x
  grind

-- Problem normal_0188: eq3767 → eq4431
theorem problem_normal_0188 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ y) ◇ (z ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (x ◇ y) = (z ◇ w) ◇ u := by
  grind

-- Problem normal_0206: eq3632 → eq4475
theorem problem_normal_0206 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ ((z ◇ w) ◇ u))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (x ◇ z) ◇ x := by
  grind

-- Problem normal_0212: eq3391 → eq4539
theorem problem_normal_0212 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ (w ◇ x)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (y ◇ w) ◇ u := by
  intro x
  have h_yu : ∀ y u, (‹Magma G›.op y u) = (‹Magma G›.op x (‹Magma G›.op y (‹Magma G›.op y y))) := by
    grind +qlia
  grind

/-
Problem normal_0214: eq2568 → eq2754
-/
theorem problem_normal_0214 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (z ◇ x)) ◇ y := by
  intros x y z
  have hx := h x y z
  have hy := h y z x
  have hz := h z x y;
  convert h x y z using 1;
  congr! 1;
  convert h _ _ _ using 1;
  rotate_left 1;
  exact y;
  exact y;
  convert h _ _ _ using 1;
  rotate_left;
  exact y;
  exact (x ◇ x);
  grind

-- Problem normal_0219: eq475 → eq3275
theorem problem_normal_0219 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ (x ◇ z))))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ (z ◇ y)) := by
  intro x y z
  have h1 := h x x x
  grind

/-
Problem normal_0221: eq435 → eq1651
-/
theorem problem_normal_0221 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (x ◇ (z ◇ w))))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((x ◇ z) ◇ y) := by
  intros x y z
  have := h x y z y;
  grind

-- Problem normal_0222: eq1107 → eq2016
theorem problem_normal_0222 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ (z ◇ w)) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ w)) ◇ (y ◇ z) := by
  have h_all_eq : ∀ (x y : G), x = y := by
    intro x y
    have h1 := h x y x x
    have h2 := h y x x x
    have h3 := h x x y y
    have h4 := h y y x x
    grind
  exact fun x y z w => h_all_eq _ _

-- Problem normal_0225: eq3444 → eq4001
theorem problem_normal_0225 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (z ◇ u)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ w)) ◇ y := by
  grind +splitImp

-- Problem normal_0227: eq2377 → eq1139
theorem problem_normal_0227 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((y ◇ (z ◇ z)) ◇ z) := by
  intro x y z
  have h1 := h x y z z
  have h2 := h y y z z
  have h3 := h x y z x
  grind

-- Problem normal_0232: eq2518 → eq1907
theorem problem_normal_0232 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ z) ◇ y)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ z)) ◇ (x ◇ w) := by
  grind +splitIndPred

-- Problem normal_0235: eq1554 → eq413
theorem problem_normal_0235 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ (x ◇ z)))
    : ∀ (x : G) (y : G), x = x ◇ (x ◇ (x ◇ (y ◇ x))) := by
  intro x
  have h2 := h x x
  grind

-- Problem normal_0243: eq2171 → eq4005
theorem problem_normal_0243 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (z ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ x)) ◇ x := by
  intro x y z
  have h1 := h x x x; have h2 := h x y z; have h3 := h y z x; have h4 := h z x y
  have h5 := h z y z; have h6 := h x x y; have h7 := h x y x; have h8 := h y x z
  grind +ring

/-
Problem normal_0250: eq2529 → eq1292
-/
theorem problem_normal_0250 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((x ◇ z) ◇ w)) ◇ u)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ y) ◇ z) ◇ y) := by
  intro x y z;
  convert h x y ( ‹Magma G›.op x y ) z y using 3;
  · convert h y y x x y using 1;
    grind;
  · convert h y _ _ _ _ using 1;
    rotate_left;
    convert h y x y z y using 1;
    convert h _ _ _ _ _ |> Eq.symm using 1;
    rotate_left;
    exact (x ◇ x);
    exact (x ◇ x);
    exact y;
    exact y;
    grind

/-
Problem normal_0253: eq2780 → eq4363
-/
theorem problem_normal_0253 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (x ◇ z)) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = y ◇ (x ◇ w) := by
  grind +suggestions

-- Problem normal_0256: eq521 → eq1515
theorem problem_normal_0256 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (z ◇ (x ◇ y))))
    : ∀ (x : G) (y : G), x = (y ◇ y) ◇ (x ◇ (x ◇ x)) := by
  intro x y
  have h1 := h x x x
  have h2 := h x y x
  have h3 := h y x y
  have h4 := h x x y
  have h5 := h y y x
  grind

/-
Problem normal_0257: eq573 → eq719
-/
theorem problem_normal_0257 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (z ◇ (x ◇ z))))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((y ◇ z) ◇ x)) := by
  -- Apply the hypothesis `h` with `x` and `y` swapped.
  have h_swap := fun x y z => h x y z;
  have h_swap := fun x y => h_swap x x y;
  grind

/-
Problem normal_0260: eq1808 → eq3695
-/
theorem problem_normal_0260 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((w ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ z) ◇ (x ◇ y) := by
  grind +suggestions

/-
Problem normal_0262: eq2621 → eq4442
-/
theorem problem_normal_0262 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ w) ◇ x)) ◇ w)
    : ∀ (x : G) (y : G), x ◇ (y ◇ x) = (y ◇ x) ◇ x := by
  grind +suggestions

/-
Problem normal_0263: eq502 → eq273
-/
theorem problem_normal_0263 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (x ◇ (x ◇ z))))
    : ∀ (x : G) (y : G), x = ((y ◇ x) ◇ y) ◇ x := by
  grind +suggestions

/-
Problem normal_0268: eq220 → eq1169
-/
theorem problem_normal_0268 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ y)) ◇ z) := by
  intro x y z;
  have h1 := h x y z;
  have h2 := h y x z;
  grind +suggestions

/-
Problem normal_0270: eq3026 → eq32
-/
theorem problem_normal_0270 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ w)) ◇ x) ◇ z)
    : ∀ (x : G) (y : G), x = (y ◇ y) ◇ y := by
  intro x y;
  have h1 := h x y y y;
  grind +ring

-- Problem normal_0278: eq3125 → eq583
theorem problem_normal_0278 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ x) ◇ z) ◇ x) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (z ◇ (w ◇ x))) := by
  intro x y z w
  have := h x x x x
  have := h y x x x
  grind

/-
Problem normal_0282: eq1269 → eq3875
-/
theorem problem_normal_0282 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ z) ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ (y ◇ z)) ◇ z := by
  intro x y z
  have := h x y z x
  have := h x y z z
  have := h x z y z
  have := h x z z y
  have := h x x x x
  have := h (x ◇ x) y z x
  have := h y x z x; have := h y x x z; have := h y y x z; have := h y y y x; have := h y y z x; have := h y y z y; have := h y y y y; have := h y y y z; have := h y y z z; have := h y y z y; have := h y y y y; have := h y y y z; have := h y y z z;
  grind +ring

/-
Problem normal_0285: eq1909 → eq4003
-/
theorem problem_normal_0285 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ z)) ◇ (y ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ w)) ◇ w := by
  grind +suggestions

/-
Problem normal_0287: eq2775 → eq3943
-/
theorem problem_normal_0287 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (x ◇ y)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ (z ◇ z)) ◇ y := by
  intro x y z;
  convert h ( _ ) _ _ using 1;
  convert h _ _ _ using 1;
  convert rfl;
  · convert h _ _ _ using 1;
    convert h _ _ _ using 1;
    rotate_left;
    exact (x ◇ x);
    exact (x ◇ x);
    exact (x ◇ x);
    exact (x ◇ x);
    grind;
  · exact x;
  · exact x

/-
Problem normal_0289: eq1715 → eq374
-/
theorem problem_normal_0289 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((z ◇ w) ◇ z))
    : ∀ (x : G) (y : G), x ◇ y = (x ◇ x) ◇ x := by
  intro x y;
  have := h ( ‹Magma G›.op y y ) x y y;
  grind +suggestions

-- Problem normal_0292: eq3576 → eq3958
theorem problem_normal_0292 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ z)) ◇ y := by
  intro x y z
  have := h x y z z
  grind

-- Problem normal_0300: eq2579 → eq2212
theorem problem_normal_0300 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ x) ◇ w)) ◇ x)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (x ◇ x) := by
  intro x y z w
  have h1 := h x y z w
  grind

-- Problem normal_0303: eq240 → eq1350
theorem problem_normal_0303 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ x) ◇ y) := by
  grind +revert

-- Problem normal_0313: eq2378 → eq2727
theorem problem_normal_0313 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ (z ◇ z)) ◇ w := by
  intro x y z
  have h_all_eq : ∀ x y : G, x = y := by
    intro x y
    rw [h x y y x, h y x y x]
    grind
  exact fun w => h_all_eq _ _

/-
Problem normal_0314: eq1716 → eq4500
-/
theorem problem_normal_0314 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((z ◇ w) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ z) ◇ w := by
  intro a b c d;
  convert h _ _ _ _;
  rotate_left;
  rotate_left;
  exact d;
  exact ‹Magma G›.op d d;
  · convert h _ _ _ _;
    convert h _ _ _ _;
    rotate_left;
    exact b;
    exact (a ◇ a);
    exact c;
    rotate_left;
    exact ‹Magma G›.op ( ‹Magma G›.op b b ) b;
    · convert h _ _ _ _;
      rotate_left;
      exact c;
      exact c;
      convert h c c c c using 1;
      grind +suggestions;
    · convert h _ _ _ _;
      convert h _ _ _ _;
      rotate_left;
      exact b;
      exact b;
      exact b;
      convert h b b b b using 1;
      grind +suggestions;
  · grind +suggestions

/-
Problem normal_0317: eq2715 → eq1630
-/
theorem problem_normal_0317 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ (y ◇ z)) ◇ w)
    : ∀ (x : G) (y : G), x = (x ◇ x) ◇ ((x ◇ x) ◇ y) := by
  intro x y
  have := h x x x y;
  grind

-- Problem normal_0321: eq3171 → eq1979
theorem problem_normal_0321 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ y) ◇ z) ◇ w) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ (y ◇ x) := by
  intro x y z
  have := h x (y ◇ y) z y
  grind

/-
Problem normal_0322: eq745 → eq1284
-/
theorem problem_normal_0322 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((x ◇ y) ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((x ◇ x) ◇ z) ◇ w) := by
  have eq1 := h;
  -- The provided solution uses "grind", which in our custom Lean means doing many applications. We start by having the goal and, for completeness, introducing the variables.
  intro x y z w
  have h1 := eq1 x x x
  have h2 := eq1 x y z
  have h3 := eq1 x y w
  have h4 := eq1 x x y
  grind

/-
Problem normal_0324: eq4082 → eq4108
-/
theorem problem_normal_0324 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ x) ◇ x) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ z) ◇ z) ◇ x := by
  intro x y z;
  -- We consider the two cases: $x = y$ and $x \neq y$.
  by_contra hxy; have := h x x z; have := h y x z; have := h x z x; have := h y z x; have := h x x y; have := h y x y; have := h x z y; have := h y z y;
  grind +ring

-- Problem normal_0325: eq3618 → eq312
theorem problem_normal_0325 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((z ◇ x) ◇ z))
    : ∀ (x : G) (y : G), x ◇ x = y ◇ (x ◇ x) := by
  grind +ring

/-
Problem normal_0327: eq2324 → eq3482
-/
theorem problem_normal_0327 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ (z ◇ w))) ◇ z)
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((y ◇ x) ◇ y) := by
  intro x y;
  have h1 := h x x x x;
  grind

/-
Problem normal_0328: eq2986 → eq1229
-/
theorem problem_normal_0328 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ x)) ◇ w) ◇ y)
    : ∀ (x : G) (y : G), x = x ◇ (((x ◇ y) ◇ x) ◇ y) := by
  intro x y
  have h1 := h x x x x
  have h2 := h x y x y
  grind

/-
Problem normal_0329: eq1605 → eq2627
-/
theorem problem_normal_0329 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (w ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((z ◇ w) ◇ y)) ◇ u := by
  -- All elements equal.
  have h_all_eq : ∀ x y : G, x = y := by
    intros x y
    have h1 := h x x x x
    have h2 := h y y y y
    have h3 := h x y x y
    have h4 := h y x y x
    grind +ring;
  exact fun x y z w u => h_all_eq _ _

-- Problem normal_0330: eq3114 → eq1804
theorem problem_normal_0330 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ y) ◇ x) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((z ◇ w) ◇ w) := by
  intro x y z w
  have h_eq : ∀ x y : G, x = y := by
    intro x y
    have h1 : ∀ x y : G, x = (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op y x) y) x) y) := by
      exact fun x y => h x y y
    have := h1 x y
    grind
  exact h_eq _ _

/-
Problem normal_0331: eq2524 → eq1988
-/
theorem problem_normal_0331 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((x ◇ z) ◇ z)) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ y)) ◇ (w ◇ y) := by
  intro x y z w;
  have := h x y y;
  convert this ( _ ) using 1;
  swap;
  bv_omega;
  convert h _ _ _ _ using 1;
  congr! 1;
  congr! 1;
  convert h _ _ _ _ using 1;
  exact x

-- Problem normal_0336: eq2825 → eq3995
theorem problem_normal_0336 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ (w ◇ x)) ◇ u)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ y)) ◇ w := by
  intro x y z
  have := h (x ◇ y) x y z
  intro w
  have := this (x ◇ y)
  grind

-- Problem normal_0342: eq1321 → eq2805
theorem problem_normal_0342 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((y ◇ x) ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (z ◇ x)) ◇ y := by
  intro x y z
  have := h x y z x
  have := h x x x x
  grind

/-
Problem normal_0346: eq3109 → eq450
-/
theorem problem_normal_0346 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ x) ◇ z) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (z ◇ (y ◇ x))) := by
  intro x y z;
  have h1 := h x x x;
  grind

/-
Problem normal_0352: eq2738 → eq159
-/
theorem problem_normal_0352 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (x ◇ y)) ◇ z)
    : ∀ (x : G) (y : G), x = (x ◇ y) ◇ (y ◇ x) := by
  grind +suggestions
