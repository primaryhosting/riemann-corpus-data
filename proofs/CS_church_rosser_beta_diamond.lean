/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation: `var n` is the variable with de Bruijn
index `n`, `app` is application and `lam` is abstraction. -/
inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- `lift c t` increments every free variable of `t` whose index is `≥ c`. -/
def lift : Nat → Term → Term
  | c, var n => if n < c then var n else var (n + 1)
  | c, app a b => app (lift c a) (lift c b)
  | c, lam a => lam (lift (c + 1) a)

/-- `subst a k b` substitutes `b` for the variable with de Bruijn index `k` in `a`,
decrementing the free variables with larger indices. -/
def subst : Term → Nat → Term → Term
  | var n, k, b => if n < k then var n else if n = k then b else var (n - 1)
  | app a₁ a₂, k, b => app (subst a₁ k b) (subst a₂ k b)
  | lam a, k, b => lam (subst a (k + 1) (lift 0 b))

@[simp] theorem lift_var (c n : Nat) :
    lift c (var n) = if n < c then var n else var (n + 1) := rfl
@[simp] theorem lift_app (c : Nat) (a b : Term) :
    lift c (app a b) = app (lift c a) (lift c b) := rfl
@[simp] theorem lift_lam (c : Nat) (a : Term) :
    lift c (lam a) = lam (lift (c + 1) a) := rfl

@[simp] theorem subst_var (n k : Nat) (b : Term) :
    subst (var n) k b = if n < k then var n else if n = k then b else var (n - 1) := rfl
@[simp] theorem subst_app (a₁ a₂ : Term) (k : Nat) (b : Term) :
    subst (app a₁ a₂) k b = app (subst a₁ k b) (subst a₂ k b) := rfl
@[simp] theorem subst_lam (a : Term) (k : Nat) (b : Term) :
    subst (lam a) k b = lam (subst a (k + 1) (lift 0 b)) := rfl

/-- Tactic handling the (index-arithmetic) variable cases of the substitution lemmas. -/
local macro "var_case" : tactic =>
  `(tactic| (simp only [lift_var, subst_var]; repeat' (first | omega | split | simp_all)))

/-- Two liftings commute. -/
theorem lift_lift (t : Term) (i j : Nat) (h : i ≤ j) :
    lift (j + 1) (lift i t) = lift i (lift j t) := by
  induction t generalizing i j with
  | var n => var_case
  | app a b iha ihb => simp [iha i j h, ihb i j h]
  | lam a ih => simp [ih (i + 1) (j + 1) (by omega)]

/-- Lifting at a cutoff at or above the substituted index. -/
theorem lift_subst_high (a : Term) : ∀ (k c : Nat) (b : Term), k ≤ c →
    lift c (subst a k b) = subst (lift (c + 1) a) k (lift c b) := by
  induction a with
  | var n => intro k c b h; var_case
  | app a₁ a₂ ih1 ih2 => intro k c b h; simp [ih1 k c b h, ih2 k c b h]
  | lam a ih =>
      intro k c b h
      simp only [subst_lam, lift_lam]
      rw [ih (k + 1) (c + 1) (lift 0 b) (by omega), lift_lift b 0 c (Nat.zero_le _)]

/-- Lifting at a cutoff at or below the substituted index. -/
theorem lift_subst_low (a : Term) : ∀ (k c : Nat) (b : Term), c ≤ k →
    lift c (subst a k b) = subst (lift c a) (k + 1) (lift c b) := by
  induction a with
  | var n => intro k c b h; var_case
  | app a₁ a₂ ih1 ih2 => intro k c b h; simp [ih1 k c b h, ih2 k c b h]
  | lam a ih =>
      intro k c b h
      simp only [subst_lam, lift_lam]
      rw [ih (k + 1) (c + 1) (lift 0 b) (by omega), lift_lift b 0 c (Nat.zero_le _)]

/-- Substituting for a freshly created variable does nothing. -/
@[simp] theorem subst_lift_self (a : Term) : ∀ (i : Nat) (b : Term), subst (lift i a) i b = a := by
  induction a with
  | var n => intro i b; var_case
  | app a₁ a₂ ih1 ih2 => intro i b; simp [ih1, ih2]
  | lam a ih => intro i b; simp [ih]

/-- The substitution (composition) lemma. -/
theorem subst_subst (a : Term) : ∀ (i j : Nat) (b c : Term), i ≤ j →
    subst (subst a i b) j c = subst (subst a (j + 1) (lift i c)) i (subst b j c) := by
  induction a with
  | var n => intro i j b c h; var_case
  | app a₁ a₂ ih1 ih2 => intro i j b c h; simp [ih1 i j b c h, ih2 i j b c h]
  | lam a ih =>
      intro i j b c h
      simp only [subst_lam]
      rw [ih (i + 1) (j + 1) (lift 0 b) (lift 0 c) (by omega),
        lift_lift c 0 i (Nat.zero_le _), lift_subst_low b j 0 c (Nat.zero_le _)]

end Term

open Term

/-- One-step parallel β-reduction: any set of β-redexes present in a term may be
contracted simultaneously. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (var n) (var n)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (app s t) (app s' t')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {s s' t t' : Term} : Par s s' → Par t t' → Par (app (lam s) t) (subst s' 0 t')

theorem Par.refl (t : Term) : Par t t := by
  induction t with
  | var n => exact Par.var n
  | app a b iha ihb => exact Par.app iha ihb
  | lam a ih => exact Par.lam ih

theorem Par.lam_inv {t u : Term} (h : Par (Term.lam t) u) :
    ∃ u', u = Term.lam u' ∧ Par t u' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- Parallel reduction is preserved by lifting. -/
theorem Par.lift {s s' : Term} (h : Par s s') :
    ∀ c : Nat, Par (Term.lift c s) (Term.lift c s') := by
  induction h with
  | var n => intro c; simp only [lift_var]; split <;> exact Par.var _
  | app _ _ ih1 ih2 => intro c; exact Par.app (ih1 c) (ih2 c)
  | lam _ ih => intro c; exact Par.lam (ih (c + 1))
  | @beta s s' t t' _ _ ih1 ih2 =>
      intro c
      have h := Par.beta (ih1 (c + 1)) (ih2 c)
      rw [lift_subst_high s' 0 c t' (Nat.zero_le _)]
      exact h

/-- Parallel reduction is preserved by substitution. -/
theorem Par.subst {a a' : Term} (ha : Par a a') :
    ∀ {b b' : Term}, Par b b' → ∀ k : Nat, Par (Term.subst a k b) (Term.subst a' k b') := by
  induction ha with
  | var n =>
      intro b b' hb k
      simp only [subst_var]
      split
      · exact Par.var _
      · split
        · exact hb
        · exact Par.var _
  | app _ _ ih1 ih2 => intro b b' hb k; exact Par.app (ih1 hb k) (ih2 hb k)
  | lam _ ih => intro b b' hb k; exact Par.lam (ih (hb.lift 0) (k + 1))
  | @beta s s' t t' _ _ ih1 ih2 =>
      intro b b' hb k
      have h := Par.beta (ih1 (hb.lift 0) (k + 1)) (ih2 hb k)
      rw [Term.subst_app, Term.subst_lam, subst_subst s' 0 k t' b' (Nat.zero_le _)]
      exact h

/-- The complete development of a term: all β-redexes currently present are contracted. -/
def dev : Term → Term
  | .var n => .var n
  | .app (.var n) t => .app (.var n) (dev t)
  | .app (.app a b) t => .app (dev (.app a b)) (dev t)
  | .app (.lam s) t => Term.subst (dev s) 0 (dev t)
  | .lam t => .lam (dev t)

/-- Takahashi's triangle property: every one-step parallel reduct of `t` parallel-reduces
to the complete development of `t`. -/
theorem Par.triangle {t u : Term} (h : Par t u) : Par u (dev t) := by
  induction h with
  | var n => exact Par.var n
  | @app s s' t t' hs _ ihs iht =>
      cases s with
      | var n =>
          cases hs
          exact Par.app (Par.var n) iht
      | app a b => exact Par.app ihs iht
      | lam s₀ =>
          obtain ⟨s₁, rfl, _⟩ := hs.lam_inv
          obtain ⟨s₂, hs₂, hpar⟩ := ihs.lam_inv
          have hd : dev (Term.lam s₀) = Term.lam (dev s₀) := rfl
          rw [hd] at hs₂
          cases hs₂
          show Par _ (Term.subst (dev s₀) 0 (dev t))
          exact Par.beta hpar iht
  | lam _ ih => exact Par.lam ih
  | @beta s s' t t' _ _ ih1 ih2 =>
      show Par _ (Term.subst (dev s) 0 (dev t))
      exact ih1.subst ih2 0

/-- Sanity check: contracting the redex `(λx. x) y` is a one-step parallel reduction. -/
example : Par (Term.app (Term.lam (Term.var 0)) (Term.var 3)) (Term.var 3) := by
  have h := Par.beta (Par.var 0) (Par.var 3)
  simpa using h

/-- **Diamond property of one-step parallel β-reduction.**
If a λ-term `t` parallel-reduces in one step both to `u` and to `v`, then `u` and `v`
have a common one-step parallel reduct (namely the complete development of `t`). -/
theorem church_rosser_beta_diamond {t u v : Term} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w :=
  ⟨dev t, hu.triangle, hv.triangle⟩

end CS

