/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalizes **Mirzakhani's recursion** for the Weil–Petersson volumes
`V_{g,n}(L_1, …, L_n)` of moduli spaces of bordered hyperbolic surfaces of genus `g`
with `n` geodesic boundary components of lengths `L_1, …, L_n`, and proves a
Lean-checked *reduction*: the recursion, together with the two base values
`V_{0,3} = 1` and `V_{1,1}(L) = (L² + 4π²)/48`, determines **all** the volumes.

The recursion is stated in its integrated form, in terms of Mirzakhani's kernels

* `H(x, y) = 1/(1 + e^{(x+y)/2}) + 1/(1 + e^{(x-y)/2})`,
* `D(t, x, y) = 2 log ((e^{t/2} + e^{(x+y)/2}) / (e^{-t/2} + e^{(x+y)/2}))`,
* `R(t, y, x) = t - log ((cosh(y/2) + cosh((t+x)/2)) / (cosh(y/2) + cosh((t-x)/2)))`,

which are the antiderivatives (in the first variable, vanishing at `t = 0`) appearing in
Mirzakhani's integration formula.  We prove the two defining derivative identities
`∂_t D(t, x, y) = H(x + y, t)` and `∂_t R(t, y, x) = ½ (H(x, t+y) + H(x, t-y))`
(`Frontier.hasDerivAt_mirzD`, `Frontier.hasDerivAt_mirzR`), so that the integrated form
stated here is exactly the integral from `0` to `L₁` of the usual differentiated form
`∂_{L₁}(L₁ V_{g,n}) = A^{con} + A^{dcon} + B`.

What is proved here is the *reduction* step: no hyperbolic geometry is developed, and the
geometric fact that the actual Weil–Petersson volume functions satisfy the recursion is
taken as a hypothesis on the family `V`.  The theorem `Frontier.mirzakhani_WP_volume` says
that this hypothesis plus the base cases pins the family down uniquely, i.e. Mirzakhani's
recursion is a complete algorithm computing every `V_{g,n}`.
-/

open Real MeasureTheory

namespace Frontier

/-! ## Mirzakhani's kernels -/

/-- Mirzakhani's kernel `H(x, y) = 1/(1 + e^{(x+y)/2}) + 1/(1 + e^{(x-y)/2})`. -/
noncomputable def mirzH (a b : ℝ) : ℝ :=
  1 / (1 + Real.exp ((a + b) / 2)) + 1 / (1 + Real.exp ((a - b) / 2))

/-- The kernel `D(t, x, y) = 2 log ((e^{t/2} + e^{(x+y)/2}) / (e^{-t/2} + e^{(x+y)/2}))`,
the antiderivative in `t` of `H(x + y, t)` vanishing at `t = 0`. -/
noncomputable def mirzD (t x y : ℝ) : ℝ :=
  2 * Real.log ((Real.exp (t / 2) + Real.exp ((x + y) / 2)) /
    (Real.exp (-t / 2) + Real.exp ((x + y) / 2)))

/-- The kernel
`R(t, y, x) = t - log ((cosh(y/2) + cosh((t+x)/2)) / (cosh(y/2) + cosh((t-x)/2)))`,
the antiderivative in `t` of `½ (H(x, t+y) + H(x, t-y))` vanishing at `t = 0`. -/
noncomputable def mirzR (t y x : ℝ) : ℝ :=
  t - Real.log ((Real.cosh (y / 2) + Real.cosh ((t + x) / 2)) /
    (Real.cosh (y / 2) + Real.cosh ((t - x) / 2)))

theorem mirzD_zero (x y : ℝ) : mirzD 0 x y = 0 := by
  simp [mirzD]

theorem mirzR_zero (x y : ℝ) : mirzR 0 y x = 0 := by
  rw [mirzR, show (0 + x) / 2 = x / 2 by ring, show ((0 : ℝ) - x) / 2 = -(x / 2) by ring,
    Real.cosh_neg]
  simp

/-- `∂_t D(t, x, y) = H(x + y, t)`. -/
theorem hasDerivAt_mirzD (x y t : ℝ) :
    HasDerivAt (fun s => mirzD s x y) (mirzH (x + y) t) t := by
  have hA : (0 : ℝ) < Real.exp ((x + y) / 2) := Real.exp_pos _
  have h1 : (0 : ℝ) < Real.exp (t / 2) + Real.exp ((x + y) / 2) := by positivity
  have h2 : (0 : ℝ) < Real.exp (-t / 2) + Real.exp ((x + y) / 2) := by positivity
  have key : ∀ s : ℝ, mirzD s x y =
      2 * (Real.log (Real.exp (s / 2) + Real.exp ((x + y) / 2))
            - Real.log (Real.exp (-s / 2) + Real.exp ((x + y) / 2))) := by
    intro s
    have p1 : (0 : ℝ) < Real.exp (s / 2) + Real.exp ((x + y) / 2) := by positivity
    have p2 : (0 : ℝ) < Real.exp (-s / 2) + Real.exp ((x + y) / 2) := by positivity
    rw [mirzD, Real.log_div (ne_of_gt p1) (ne_of_gt p2)]
  simp only [key]
  have d1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2) + Real.exp ((x + y) / 2))
      (Real.exp (t / 2) * (1 / 2)) t := by
    have h := ((hasDerivAt_id t).div_const 2).exp
    simpa using h.add_const (Real.exp ((x + y) / 2))
  have d2 : HasDerivAt (fun s : ℝ => Real.exp (-s / 2) + Real.exp ((x + y) / 2))
      (Real.exp (-t / 2) * (-(1 / 2))) t := by
    have h0 : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2)) t := by
      have h := (hasDerivAt_neg t).div_const 2
      norm_num at h ⊢
      exact h
    simpa using (h0.exp).add_const (Real.exp ((x + y) / 2))
  have hD := ((d1.log (ne_of_gt h1)).sub (d2.log (ne_of_gt h2))).const_mul (2 : ℝ)
  convert hD using 1
  rw [mirzH, show ((x + y) + t) / 2 = (x + y) / 2 + t / 2 by ring,
    show ((x + y) - t) / 2 = (x + y) / 2 - t / 2 by ring, Real.exp_add, Real.exp_sub,
    show (-t / 2 : ℝ) = -(t / 2) by ring, Real.exp_neg]
  have ha : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  field_simp
  ring

/-- `∂_t R(t, y, x) = ½ (H(x, t + y) + H(x, t - y))`. -/
theorem hasDerivAt_mirzR (x y t : ℝ) :
    HasDerivAt (fun s => mirzR s y x) ((1 / 2) * (mirzH x (t + y) + mirzH x (t - y))) t := by
  have hc : ∀ u : ℝ, (0 : ℝ) < Real.cosh (y / 2) + Real.cosh u := by
    intro u
    have h1 := Real.one_le_cosh (y / 2)
    have h2 := Real.one_le_cosh u
    linarith
  have key : ∀ s : ℝ, mirzR s y x =
      s - (Real.log (Real.cosh (y / 2) + Real.cosh ((s + x) / 2))
            - Real.log (Real.cosh (y / 2) + Real.cosh ((s - x) / 2))) := by
    intro s
    rw [mirzR, Real.log_div (ne_of_gt (hc _)) (ne_of_gt (hc _))]
  simp only [key]
  have d1 : HasDerivAt (fun s : ℝ => Real.cosh (y / 2) + Real.cosh ((s + x) / 2))
      (Real.sinh ((t + x) / 2) * (1 / 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => (s + x) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).add_const x).div_const 2
    simpa using ((Real.hasDerivAt_cosh ((t + x) / 2)).comp t h0).const_add (Real.cosh (y / 2))
  have d2 : HasDerivAt (fun s : ℝ => Real.cosh (y / 2) + Real.cosh ((s - x) / 2))
      (Real.sinh ((t - x) / 2) * (1 / 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => (s - x) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const x).div_const 2
    simpa using ((Real.hasDerivAt_cosh ((t - x) / 2)).comp t h0).const_add (Real.cosh (y / 2))
  have hR := (hasDerivAt_id t).sub ((d1.log (ne_of_gt (hc _))).sub (d2.log (ne_of_gt (hc _))))
  convert hR using 1
  have ha : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hd : (0 : ℝ) < Real.exp (y / 2) := Real.exp_pos _
  simp only [mirzH, Real.cosh_eq, Real.sinh_eq]
  rw [show (x + (t + y)) / 2 = x / 2 + t / 2 + y / 2 by ring,
     show (x - (t + y)) / 2 = x / 2 - t / 2 - y / 2 by ring,
     show (x + (t - y)) / 2 = x / 2 + t / 2 - y / 2 by ring,
     show (x - (t - y)) / 2 = x / 2 - t / 2 + y / 2 by ring,
     show ((t + x) / 2 : ℝ) = t / 2 + x / 2 by ring,
     show ((t - x) / 2 : ℝ) = t / 2 - x / 2 by ring]
  simp only [Real.exp_add, Real.exp_sub, Real.exp_neg, neg_add_rev, neg_sub]
  have k1 : (0 : ℝ) < (rexp (y / 2) + (rexp (y / 2))⁻¹) / 2 +
      (rexp (t / 2) * rexp (x / 2) + (rexp (x / 2))⁻¹ * (rexp (t / 2))⁻¹) / 2 := by positivity
  have k2 : (0 : ℝ) < (rexp (y / 2) + (rexp (y / 2))⁻¹) / 2 +
      (rexp (t / 2) / rexp (x / 2) + rexp (x / 2) / rexp (t / 2)) / 2 := by positivity
  field_simp
  ring

/-! ## Boundary length vectors

A surface with `n` labelled boundary components carries a length vector, which we model as a
function `L : ℕ → ℝ`; only the values `L 0, …, L (n-1)` are relevant. -/

/-- The length vector of a surface whose first boundary has length `x` and whose remaining
boundaries are the boundaries of the ambient surface listed by `l`. -/
def mirzCons (x : ℝ) (L : ℕ → ℝ) (l : List ℕ) : ℕ → ℝ :=
  fun i => if i = 0 then x else L (l.getD (i - 1) 0)

/-- The length vector `(x, y, L 1, …, L (n-1))`. -/
def mirzCons₂ (x y : ℝ) (L : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then x else if i = 1 then y else L (i - 1)

/-! ## The three terms of Mirzakhani's recursion -/

/-- The *connected* term: cutting off a pair of pants along the first boundary can produce a
connected surface of genus `g - 1` with two new boundaries. -/
noncomputable def mirzAcon (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ) : ℝ :=
  if 1 ≤ g then
    ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
      x * y * mirzD (L 0) x y * V (g - 1) (n + 1) (mirzCons₂ x y L)
  else 0

/-- The *disconnected* term: the cut can also split the surface into two stable pieces, of
genera `g₁` and `g - g₁`, the remaining boundaries `{1, …, n-1}` being distributed as
`S` and its complement. -/
noncomputable def mirzAdcon (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ) : ℝ :=
  ∑ g₁ ∈ Finset.range (g + 1), ∑ S ∈ (Finset.Ico 1 n).powerset,
    if 3 ≤ 2 * g₁ + (S.card + 1) ∧ 3 ≤ 2 * (g - g₁) + ((Finset.Ico 1 n \ S).card + 1) then
      ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        x * y * mirzD (L 0) x y *
          (V g₁ (S.card + 1) (mirzCons x L (S.sort (· ≤ ·))) *
            V (g - g₁) ((Finset.Ico 1 n \ S).card + 1)
              (mirzCons y L ((Finset.Ico 1 n \ S).sort (· ≤ ·))))
    else 0

/-- The term coming from pairs of pants containing the first boundary and one other
boundary `j`. -/
noncomputable def mirzBterm (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 n,
    ∫ x in Set.Ioi (0 : ℝ),
      x * mirzR (L 0) (L j) x *
        V g (n - 1) (mirzCons x L (((Finset.Ico 1 n).erase j).sort (· ≤ ·)))

/-- **Mirzakhani's recursion** (integrated form) for a family of volume functions
`V g n : (ℕ → ℝ) → ℝ`:
`L₁ V_{g,n}(L) = ½ (A^{con} + A^{dcon}) + B`
for every stable `(g, n)` other than the two base cases `(0,3)` and `(1,1)`
(i.e. for `2g + n ≥ 4`).  Differentiating in `L₁` and using
`Frontier.hasDerivAt_mirzD`, `Frontier.hasDerivAt_mirzR` gives the familiar form
`∂_{L₁}(L₁ V_{g,n}) = A^{con} + A^{dcon} + B` with the kernel `H`. -/
def MirzakhaniRecursion (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  ∀ g n : ℕ, 1 ≤ n → 4 ≤ 2 * g + n → ∀ L : ℕ → ℝ,
    L 0 * V g n L = (1 / 2) * (mirzAcon V g n L + mirzAdcon V g n L) + mirzBterm V g n L

/-! ## Congruence lemmas for the three terms -/

/-- Two families that agree on all stable data of strictly smaller complexity `3g + n`
(for positive first boundary length) have the same connected term. -/
theorem mirzAcon_congr (V W : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (hn : 1 ≤ n) (hs : 4 ≤ 2 * g + n)
    (h : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
      V g' n' L' = W g' n' L') :
    mirzAcon V g n L = mirzAcon W g n L := by
  rw [mirzAcon, mirzAcon]
  by_cases hg : 1 ≤ g
  · simp only [if_pos hg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [h (g - 1) (n + 1) (mirzCons₂ x y L) (by omega) (by omega) (by omega)
      (by simpa [mirzCons₂] using hx)]
  · simp only [if_neg hg]

theorem mirzAdcon_congr (V W : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (hn : 1 ≤ n)
    (h : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
      V g' n' L' = W g' n' L') :
    mirzAdcon V g n L = mirzAdcon W g n L := by
  rw [mirzAdcon, mirzAdcon]
  refine Finset.sum_congr rfl (fun g₁ hg₁ => Finset.sum_congr rfl (fun S hS => ?_))
  simp only [Finset.mem_range] at hg₁
  simp only [Finset.mem_powerset] at hS
  by_cases hcond : 3 ≤ 2 * g₁ + (S.card + 1) ∧
      3 ≤ 2 * (g - g₁) + ((Finset.Ico 1 n \ S).card + 1)
  · rw [if_pos hcond, if_pos hcond]
    have hcard : S.card + (Finset.Ico 1 n \ S).card = n - 1 := by
      have h1 := Finset.card_sdiff_add_card_eq_card hS
      have h2 : (Finset.Ico 1 n).card = n - 1 := by simp
      omega
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [h g₁ (S.card + 1) _ (by omega) (by omega) hcond.1 (by simpa [mirzCons] using hx),
      h (g - g₁) ((Finset.Ico 1 n \ S).card + 1) _ (by omega) (by omega) hcond.2
        (by simpa [mirzCons] using hy)]
  · rw [if_neg hcond, if_neg hcond]

theorem mirzBterm_congr (V W : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (hn : 1 ≤ n) (hs : 4 ≤ 2 * g + n)
    (h : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
      V g' n' L' = W g' n' L') :
    mirzBterm V g n L = mirzBterm W g n L := by
  rw [mirzBterm, mirzBterm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Ico] at hj
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [h g (n - 1) _ (by omega) (by omega) (by omega) (by simpa [mirzCons] using hx)]

/-! ## The main reduction theorem -/

/-- **Mirzakhani's recursion determines all Weil–Petersson volumes.**

If two families `V` and `W` of volume functions both satisfy Mirzakhani's recursion and both
take the base values `V_{0,3} = 1` and `V_{1,1}(L) = (L² + 4π²)/48`, then they agree on every
stable pair `(g, n)` (`n ≥ 1`, `2g - 2 + n > 0`) and every boundary length vector whose first
entry is positive.

Thus the recursion, whose geometric content is Mirzakhani's integration formula over moduli
space, is a complete recursive scheme: it reduces every Weil–Petersson volume to the two base
cases. -/
theorem mirzakhani_WP_volume (V W : ℕ → ℕ → (ℕ → ℝ) → ℝ)
    (hV : MirzakhaniRecursion V) (hW : MirzakhaniRecursion W)
    (hV03 : ∀ L, V 0 3 L = 1) (hW03 : ∀ L, W 0 3 L = 1)
    (hV11 : ∀ L, V 1 1 L = (L 0 ^ 2 + 4 * Real.pi ^ 2) / 48)
    (hW11 : ∀ L, W 1 1 L = (L 0 ^ 2 + 4 * Real.pi ^ 2) / 48) :
    ∀ g n : ℕ, 1 ≤ n → 3 ≤ 2 * g + n → ∀ L : ℕ → ℝ, 0 < L 0 → V g n L = W g n L := by
  have main : ∀ m g n : ℕ, 3 * g + n = m → 1 ≤ n → 3 ≤ 2 * g + n →
      ∀ L : ℕ → ℝ, 0 < L 0 → V g n L = W g n L := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro g n hm hn hstab L hL
      rcases Nat.lt_or_ge (2 * g + n) 4 with h4 | h4
      · -- the two base cases `(0,3)` and `(1,1)`
        have hgn : (g = 0 ∧ n = 3) ∨ (g = 1 ∧ n = 1) := by omega
        rcases hgn with ⟨hg, hn3⟩ | ⟨hg, hn1⟩
        · subst hg; subst hn3; rw [hV03, hW03]
        · subst hg; subst hn1; rw [hV11, hW11]
      · -- the recursive step
        have hIH : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
            V g' n' L' = W g' n' L' := by
          intro g' n' L' hlt hn' hstab' hL'
          exact IH (3 * g' + n') (hm ▸ hlt) g' n' rfl hn' hstab' L' hL'
        have hVL := hV g n hn h4 L
        have hWL := hW g n hn h4 L
        have e1 := mirzAcon_congr V W g n L hn h4 hIH
        have e2 := mirzAdcon_congr V W g n L hn hIH
        have e3 := mirzBterm_congr V W g n L hn h4 hIH
        have : L 0 * V g n L = L 0 * W g n L := by rw [hVL, hWL, e1, e2, e3]
        exact mul_left_cancel₀ (ne_of_gt hL) this
  intro g n hn hstab L hL
  exact main (3 * g + n) g n rfl hn hstab L hL

/-! ## The recursion is consistent: a family satisfying it exists

The uniqueness theorem above is not vacuous: we build, by recursion on the complexity
`3g + n`, a family satisfying Mirzakhani's recursion together with the two base values.
(For an actual Weil–Petersson volume family the recursion is Mirzakhani's theorem; here we
only need that the recursive scheme is consistent.) -/

theorem mirzAcon_of_first_eq_zero (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (h : L 0 = 0) : mirzAcon V g n L = 0 := by
  simp [mirzAcon, h, mirzD_zero]

theorem mirzAdcon_of_first_eq_zero (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (h : L 0 = 0) : mirzAdcon V g n L = 0 := by
  simp [mirzAdcon, h, mirzD_zero]

theorem mirzBterm_of_first_eq_zero (V : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (h : L 0 = 0) : mirzBterm V g n L = 0 := by
  simp [mirzBterm, h, mirzR_zero]

/-- Auxiliary recursive construction: `mirzVaux m` computes the volumes of complexity at
most `m`. -/
noncomputable def mirzVaux : ℕ → ℕ → ℕ → (ℕ → ℝ) → ℝ
  | 0, _, _, _ => 0
  | (m + 1), g, n, L =>
      if g = 0 ∧ n = 3 then 1
      else if g = 1 ∧ n = 1 then (L 0 ^ 2 + 4 * Real.pi ^ 2) / 48
      else if L 0 = 0 then 0
      else ((1 / 2) * (mirzAcon (mirzVaux m) g n L + mirzAdcon (mirzVaux m) g n L)
        + mirzBterm (mirzVaux m) g n L) / L 0

/-- The auxiliary construction does not depend on the amount of available recursion depth. -/
theorem mirzVaux_indep : ∀ c g n : ℕ, 3 * g + n = c → 1 ≤ n → 3 ≤ 2 * g + n →
    ∀ m m' : ℕ, c ≤ m → c ≤ m' → ∀ L : ℕ → ℝ, mirzVaux m g n L = mirzVaux m' g n L := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c IH =>
    intro g n hc hn hstab m m' hm hm' L
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', m' = k' + 1 := ⟨m' - 1, by omega⟩
    simp only [mirzVaux]
    by_cases hb1 : g = 0 ∧ n = 3
    · simp only [if_pos hb1]
    by_cases hb2 : g = 1 ∧ n = 1
    · simp only [if_neg hb1, if_pos hb2]
    simp only [if_neg hb1, if_neg hb2]
    by_cases hL : L 0 = 0
    · simp only [if_pos hL]
    simp only [if_neg hL]
    have h4 : 4 ≤ 2 * g + n := by omega
    have hIH : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
        mirzVaux k g' n' L' = mirzVaux k' g' n' L' := by
      intro g' n' L' hlt hn' hstab' _
      exact IH (3 * g' + n') (by omega) g' n' rfl hn' hstab' k k' (by omega) (by omega) L'
    rw [mirzAcon_congr _ _ g n L hn h4 hIH, mirzAdcon_congr _ _ g n L hn hIH,
      mirzBterm_congr _ _ g n L hn h4 hIH]

/-- A concrete family of functions satisfying Mirzakhani's recursion and its base values. -/
noncomputable def mirzV (g n : ℕ) (L : ℕ → ℝ) : ℝ := mirzVaux (3 * g + n) g n L

theorem mirzV_zero_three (L : ℕ → ℝ) : mirzV 0 3 L = 1 := by
  simp [mirzV, mirzVaux]

theorem mirzV_one_one (L : ℕ → ℝ) : mirzV 1 1 L = (L 0 ^ 2 + 4 * Real.pi ^ 2) / 48 := by
  simp [mirzV, mirzVaux]

theorem mirzakhaniRecursion_mirzV : MirzakhaniRecursion mirzV := by
  intro g n hn h4 L
  have hc : 4 ≤ 3 * g + n := by omega
  obtain ⟨k, hk⟩ : ∃ k, 3 * g + n = k + 1 := ⟨3 * g + n - 1, by omega⟩
  have hb1 : ¬(g = 0 ∧ n = 3) := by omega
  have hb2 : ¬(g = 1 ∧ n = 1) := by omega
  have hIH : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
      mirzVaux k g' n' L' = mirzV g' n' L' := by
    intro g' n' L' hlt hn' hstab' _
    exact mirzVaux_indep (3 * g' + n') g' n' rfl hn' hstab' k (3 * g' + n')
      (by omega) (by omega) L'
  have hval : mirzV g n L = mirzVaux (k + 1) g n L := by rw [mirzV, hk]
  by_cases hL : L 0 = 0
  · rw [hL, mirzAcon_of_first_eq_zero _ _ _ _ hL, mirzAdcon_of_first_eq_zero _ _ _ _ hL,
      mirzBterm_of_first_eq_zero _ _ _ _ hL]
    ring
  · rw [hval]
    simp only [mirzVaux, if_neg hb1, if_neg hb2, if_neg hL]
    rw [mirzAcon_congr _ _ g n L hn h4 hIH, mirzAdcon_congr _ _ g n L hn hIH,
      mirzBterm_congr _ _ g n L hn h4 hIH]
    field_simp

/-- The hypotheses of `Frontier.mirzakhani_WP_volume` are consistent: some family of
functions does satisfy Mirzakhani's recursion together with the two base values. -/
theorem mirzakhani_recursion_consistent :
    ∃ V : ℕ → ℕ → (ℕ → ℝ) → ℝ, MirzakhaniRecursion V ∧ (∀ L, V 0 3 L = 1) ∧
      (∀ L, V 1 1 L = (L 0 ^ 2 + 4 * Real.pi ^ 2) / 48) :=
  ⟨mirzV, mirzakhaniRecursion_mirzV, mirzV_zero_three, mirzV_one_one⟩

end Frontier

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

