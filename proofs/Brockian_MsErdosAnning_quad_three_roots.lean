import Mathlib

/-!
# The Erdős–Anning theorem

An infinite set of points in the Euclidean plane whose pairwise distances are all integers
must be collinear.

## Proof outline

Assume `S` is infinite with integral pairwise distances and pick `A ≠ B` in `S`.  If some
`C ∈ S` is off the line `AB`, then `A`, `B`, `C` form a non-degenerate triangle.  For every
`P ∈ S` the two differences `dist P A - dist P B` and `dist P A - dist P C` are integers
bounded in absolute value by `dist A B` and `dist A C` respectively, so only finitely many
pairs of values occur (`finite_of_not_collinear`).  The heart of the argument (`key`) shows
that three *distinct* points cannot share the same pair of differences: writing
`⟪P - A, B - A⟫` in terms of the distances (`inner_formula`) shows that all such points lie
on a common line `A + p + x • q` with `x = dist P A`, and `‖p + x • q‖ = x` can hold for at
most two values of `x` unless `p = 0` and `‖q‖ = 1` (`key_p_zero`), in which case `B - A`
and `C - A` are both multiples of `q`, contradicting non-collinearity.  Hence `S` would be
finite, a contradiction.
-/

namespace Brockian.MsErdosAnning

open scoped RealInnerProductSpace

/-! ### Auxiliary algebraic lemmas -/

/-- A real quadratic with three distinct roots is identically zero. -/
lemma quad_three_roots {α β γ a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : α * a ^ 2 + β * a + γ = 0) (hb : α * b ^ 2 + β * b + γ = 0)
    (hc : α * c ^ 2 + β * c + γ = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  -- Subtract pairs of equations to eliminate γ
  have hsub1 : α * (a ^ 2 - b ^ 2) + β * (a - b) = 0 := by linarith
  have hsub2 : α * (a ^ 2 - c ^ 2) + β * (a - c) = 0 := by linarith
  have hsub3 : α * (b ^ 2 - c ^ 2) + β * (b - c) = 0 := by linarith
  -- Factor: (a² - b²) = (a - b)(a + b)
  have hfact1 : (a - b) * (α * (a + b) + β) = 0 := by ring_nf; linarith
  have hfact2 : (a - c) * (α * (a + c) + β) = 0 := by ring_nf; linarith
  have hfact3 : (b - c) * (α * (b + c) + β) = 0 := by ring_nf; linarith
  -- Since a ≠ b, a ≠ c, b ≠ c, we get the linear equations
  have h1 : α * (a + b) + β = 0 := (mul_eq_zero.mp hfact1).resolve_left (sub_ne_zero.mpr hab)
  have h2 : α * (a + c) + β = 0 := (mul_eq_zero.mp hfact2).resolve_left (sub_ne_zero.mpr hac)
  have h3 : α * (b + c) + β = 0 := (mul_eq_zero.mp hfact3).resolve_left (sub_ne_zero.mpr hbc)
  -- From h1 and h2: α * (b - c) = 0, so α = 0
  have hα : α = 0 := by
    have : α * (b - c) = 0 := by linarith
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hbc) this
  -- With α = 0, h1 gives β = 0
  have hβ : β = 0 := by simp [hα] at h1; linarith
  -- With α = 0 and β = 0, ha gives γ = 0
  have hγ : γ = 0 := by simp [hα, hβ] at ha; linarith
  exact ⟨hα, hβ, hγ⟩

/-- A set in which no three elements are pairwise distinct is finite. -/
lemma finite_of_no_three {X : Type*} (T : Set X)
    (h : ∀ P ∈ T, ∀ Q ∈ T, ∀ R ∈ T, P ≠ Q → P ≠ R → Q ≠ R → False) : T.Finite := by
  by_contra hinf
  -- T is infinite, so we can find 3 distinct elements
  have : ∃ a b c : _, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    let f := Set.Infinite.natEmbedding T hinf
    have h0 := (f 0).2
    have h1 := (f 1).2
    have h2 := (f 2).2
    exact ⟨(f 0 : X), (f 1 : X), (f 2 : X), h0, h1, h2, Subtype.coe_injective.ne (f.injective.ne (by norm_num : (0 : ℕ) ≠ 1)), Subtype.coe_injective.ne (f.injective.ne (by norm_num : (0 : ℕ) ≠ 2)), Subtype.coe_injective.ne (f.injective.ne (by norm_num : (1 : ℕ) ≠ 2))⟩
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := this
  exact h a ha b hb c hc hab hac hbc

/-! ### Plane geometry lemmas -/

/-- In the plane, a vector orthogonal to two vectors which are not parallel is zero. -/
lemma dep_of_orth {u w z : EuclideanSpace ℝ (Fin 2)} (hu : u ≠ 0)
    (h1 : ⟪u, w⟫ = 0) (h2 : ⟪u, z⟫ = 0) :
    ∃ s t : ℝ, ¬ (s = 0 ∧ t = 0) ∧ s • w = t • z := by
  by_cases hw : w = 0
  · exact ⟨1, 0, by simp, by simp [hw]⟩
  by_cases hz : z = 0
  · exact ⟨0, 1, by simp, by simp [hz]⟩
  -- Both w ≠ 0 and z ≠ 0
  -- Use components: for u = ⟨u₁, u₂⟩, w = ⟨w₁, w₂⟩, we have u₁ * w₁ + u₂ * w₂ = 0
  set u₁ := u 0 with hu1_def
  set u₂ := u 1 with hu2_def
  set w₁ := w 0 with hw1_def
  set w₂ := w 1 with hw2_def
  set z₁ := z 0 with hz1_def
  set z₂ := z 1 with hz2_def
  have huw : u₁ * w₁ + u₂ * w₂ = 0 := by simp [inner] at h1; linarith
  have huz : u₁ * z₁ + u₂ * z₂ = 0 := by simp [inner] at h2; linarith
  -- Case split on whether z₁ ≠ 0
  by_cases hz₁_nonzero : z₁ ≠ 0
  · -- Use s = z₁, t = w₁
    use z₁, w₁
    constructor
    · intro ⟨hz₁, hw₁⟩; exact hz₁_nonzero hz₁
    · -- Show z₁ • w = w₁ • z
      ext i
      fin_cases i
      · simp; ring
      · -- Need: z₁ * w₂ = w₁ * z₂
        -- From huw: u₁ * w₁ + u₂ * w₂ = 0, so u₁ * w₁ = -u₂ * w₂
        -- From huz: u₁ * z₁ + u₂ * z₂ = 0, so u₁ * z₁ = -u₂ * z₂
        -- Multiply first by z₂: u₁ * w₁ * z₂ = -u₂ * w₂ * z₂
        -- Multiply second by w₂: u₁ * z₁ * w₂ = -u₂ * z₂ * w₂
        -- These are equal, so u₁ * w₁ * z₂ = u₁ * z₁ * w₂
        have key : u₁ * w₁ * z₂ = u₁ * z₁ * w₂ := by
          have eq1 : u₁ * w₁ = -u₂ * w₂ := by linarith
          have eq2 : u₁ * z₁ = -u₂ * z₂ := by linarith
          calc u₁ * w₁ * z₂ = (-u₂ * w₂) * z₂ := by rw [eq1]
            _ = -u₂ * w₂ * z₂ := by ring
            _ = -u₂ * z₂ * w₂ := by ring
            _ = (u₁ * z₁) * w₂ := by rw [eq2]
            _ = u₁ * z₁ * w₂ := by ring
        have hcross : w₁ * z₂ = z₁ * w₂ := by
          by_cases hu₁ : u₁ = 0
          · -- If u₁ = 0, then u₂ ≠ 0, so from huw/huz: w₂ = 0 and z₂ = 0
            have hu₂ : u₂ ≠ 0 := fun hu₂_zero => hu (by
              ext i; fin_cases i <;> [exact hu1_def.symm.trans hu₁; exact hu2_def.symm.trans hu₂_zero])
            have huw' : u₂ * w₂ = 0 := by rw [hu₁, zero_mul, zero_add] at huw; exact huw
            have huz' : u₂ * z₂ = 0 := by rw [hu₁, zero_mul, zero_add] at huz; exact huz
            have hw₂_zero : w₂ = 0 := (mul_eq_zero.mp huw').resolve_left hu₂
            have hz₂_zero : z₂ = 0 := (mul_eq_zero.mp huz').resolve_left hu₂
            simp [hw₂_zero, hz₂_zero]
          · -- If u₁ ≠ 0, cancel u₁ from key
            have key' : u₁ * (w₁ * z₂) = u₁ * (z₁ * w₂) := by linarith
            exact mul_left_cancel₀ hu₁ key'
        simp; linarith
  · -- z₁ = 0, so z₂ ≠ 0 (since z ≠ 0)
    simp only [not_not] at hz₁_nonzero
    have hz₂_nonzero : z₂ ≠ 0 := by
      intro hz₂_zero
      exact hz (by ext i; fin_cases i <;> [exact hz1_def.symm.trans hz₁_nonzero; exact hz2_def.symm.trans hz₂_zero])
    -- Use s = z₂, t = w₂
    use z₂, w₂
    constructor
    · intro ⟨hz₂, hw₂⟩; exact hz₂_nonzero hz₂
    · -- Show z₂ • w = w₂ • z
      -- Since z₁ = 0 and z₂ ≠ 0, from huz: u₂ * z₂ = 0, so u₂ = 0
      -- From huw: u₁ * w₁ = 0, and since u ≠ 0, u₁ ≠ 0, so w₁ = 0
      have hu₂ : u₂ = 0 := by
        have huz' : u₂ * z₂ = 0 := by rw [hz₁_nonzero] at huz; ring_nf at huz; exact huz
        exact (mul_eq_zero.mp huz').resolve_right hz₂_nonzero
      have hu₁ : u₁ ≠ 0 := by
        intro hu₁_zero
        exact hu (by ext i; fin_cases i <;> [exact hu1_def.symm.trans hu₁_zero; exact hu2_def.symm.trans hu₂])
      have hw₁ : w₁ = 0 := by
        have huw' : u₁ * w₁ = 0 := by rw [hu₂, zero_mul, add_zero] at huw; exact huw
        exact (mul_eq_zero.mp huw').resolve_left hu₁
      ext i
      fin_cases i
      · show z₂ * w 0 = w₂ * z 0
        rw [hw1_def.symm, hz1_def.symm, hw₁, hz₁_nonzero]; ring
      · show z₂ * w 1 = w₂ * z 1
        ring

/-- If `B - A` and `C - A` are parallel then `A`, `B`, `C` are collinear. -/
lemma collinear_of_smul_eq {A B C : EuclideanSpace ℝ (Fin 2)} {s t : ℝ}
    (hst : ¬ (s = 0 ∧ t = 0)) (h : s • (B - A) = t • (C - A)) :
    Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  by_cases hs : s = 0
  · -- If s = 0, then t ≠ 0, so C = A
    have ht : t ≠ 0 := fun ht => hst ⟨hs, ht⟩
    have hC : C = A := by
      have : t • (C - A) = 0 := by rw [← h, hs, zero_smul]
      exact sub_eq_zero.mp (smul_eq_zero.mp this |>.resolve_left ht)
    simp [hC, collinear_pair]
  · by_cases ht : t = 0
    · -- If t = 0, then s ≠ 0, so B = A
      have hB : B = A := by
        have : s • (B - A) = 0 := by rw [h, ht, zero_smul]
        exact sub_eq_zero.mp (smul_eq_zero.mp this |>.resolve_left hs)
      simp [hB, collinear_pair]
    · -- Both s ≠ 0 and t ≠ 0
      have hBA : B - A = (t / s) • (C - A) := by
        have h1 : s • (B - A) = s • ((t / s) • (C - A)) := by
          rw [h, smul_smul]
          congr 1
          field_simp
        exact smul_right_injective (M := EuclideanSpace ℝ (Fin 2)) hs h1
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      use A, C - A
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨t / s, by rw [← hBA]; simp⟩
      · exact ⟨1, by simp⟩

/-- If `A`, `B`, `C` are not collinear, a vector orthogonal to `B - A` and `C - A` vanishes. -/
lemma orth_eq_zero {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    {u : EuclideanSpace ℝ (Fin 2)} (h1 : ⟪u, B - A⟫ = 0) (h2 : ⟪u, C - A⟫ = 0) : u = 0 := by
  by_contra hu
  obtain ⟨s, t, hst, h⟩ := dep_of_orth hu h1 h2
  exact hABC (collinear_of_smul_eq hst h)

/-- If `A`, `B`, `C` are not collinear, then prescribed inner products with `B - A` and `C - A`
are realized by some vector. -/
lemma exists_inner_eq {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) (r1 r2 : ℝ) :
    ∃ q : EuclideanSpace ℝ (Fin 2), ⟪q, B - A⟫ = r1 ∧ ⟪q, C - A⟫ = r2 := by
  -- Define the linear map T(q) = (⟪q, B - A⟫, ⟪q, C - A⟫)
  let T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ × ℝ := {
    toFun := fun q => (⟪q, B - A⟫, ⟪q, C - A⟫)
    map_add' := fun x y => by simp [inner_add_left]
    map_smul' := fun c x => by simp [inner_smul_left]
  }
  -- T has trivial kernel by orth_eq_zero
  have hker : LinearMap.ker T = ⊥ := by
    ext q
    simp only [LinearMap.mem_ker, Submodule.mem_bot, Prod.ext_iff]
    constructor
    · intro hq
      exact orth_eq_zero hABC hq.1 hq.2
    · intro hq
      simp [hq]
  -- T is surjective since dim(domain) = dim(codomain) and ker(T) = ⊥
  have hsurj : Function.Surjective T := by
    have hidj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    have hcodim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
    have h := LinearMap.finrank_range_of_inj hidj
    have hrange_dim : Module.finrank ℝ (LinearMap.range T) = Module.finrank ℝ (ℝ × ℝ) := by
      rw [h, hfin, hcodim]
    -- The range has same dimension as codomain, so it's the whole space
    have hrange : LinearMap.range T = ⊤ := Submodule.eq_top_of_finrank_eq hrange_dim
    exact LinearMap.range_eq_top.mp hrange
  obtain ⟨q, hq⟩ := hsurj (r1, r2)
  have hq' : (⟪q, B - A⟫, ⟪q, C - A⟫) = (r1, r2) := hq
  exact ⟨q, congrArg Prod.fst hq', congrArg Prod.snd hq'⟩

/-- The basic identity relating the inner product `⟪P - A, B - A⟫` to the distances from `P`. -/
lemma inner_formula (P A B : EuclideanSpace ℝ (Fin 2)) :
    ⟪P - A, B - A⟫ =
      (dist P A - dist P B) * dist P A + (‖B - A‖ ^ 2 - (dist P A - dist P B) ^ 2) / 2 := by
  have h1 : ⟪P - A, B - A⟫ = (‖P - A‖ ^ 2 + ‖B - A‖ ^ 2 - ‖P - B‖ ^ 2) / 2 := by
    have key := norm_sub_sq_real (P - A) (B - A)
    have : P - A - (B - A) = P - B := by abel
    rw [this] at key
    linarith
  rw [h1, dist_eq_norm, dist_eq_norm]
  ring

/-- Two points with the same distance differences give the same "offset" vector `p`. -/
lemma same_p {A B C P Q q : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hq1 : ⟪q, B - A⟫ = dist P A - dist P B) (hq2 : ⟪q, C - A⟫ = dist P A - dist P C)
    (e1 : dist Q A - dist Q B = dist P A - dist P B)
    (e2 : dist Q A - dist Q C = dist P A - dist P C) :
    (P - A) - (dist P A) • q = (Q - A) - (dist Q A) • q := by
  -- Define r = (P - A) - (dist P A) • q - ((Q - A) - (dist Q A) • q)
  -- We show r is orthogonal to both (B - A) and (C - A)
  -- Since A, B, C are not collinear, r = 0
  set r := (P - A) - (dist P A) • q - ((Q - A) - (dist Q A) • q) with hr_def
  suffices h : r = 0 by rw [hr_def] at h; exact sub_eq_zero.mp h
  -- Show r is orthogonal to (B - A)
  have horthB : ⟪r, B - A⟫ = 0 := by
    simp only [hr_def]
    have hr_simp : (P - A - dist P A • q) - (Q - A - dist Q A • q) = (P - Q) - (dist P A - dist Q A) • q := by module
    rw [hr_simp]
    rw [inner_sub_left, inner_smul_left, hq1]
    have hPQ : P - Q = (P - A) - (Q - A) := by abel
    rw [hPQ, inner_sub_left]
    simp only [inner_formula]
    simp
    have he1' : dist Q A = dist Q B + (dist P A - dist P B) := by linarith
    rw [he1']
    ring
  -- Show r is orthogonal to (C - A)
  have horthC : ⟪r, C - A⟫ = 0 := by
    simp only [hr_def]
    have hr_simp : (P - A - dist P A • q) - (Q - A - dist Q A • q) = (P - Q) - (dist P A - dist Q A) • q := by module
    rw [hr_simp]
    rw [inner_sub_left, inner_smul_left, hq2]
    have hPQ : P - Q = (P - A) - (Q - A) := by abel
    rw [hPQ, inner_sub_left]
    simp only [inner_formula]
    simp
    have he2' : dist Q A = dist Q C + (dist P A - dist P C) := by linarith
    rw [he2']
    ring
  exact orth_eq_zero hABC horthB horthC

/-- If `‖p + x • q‖ = x` for three distinct values of `x`, then `p = 0` and `q` is a unit
vector. -/
lemma key_p_zero {a b c : ℝ} {p q : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hP : ‖p + a • q‖ = a) (hQ : ‖p + b • q‖ = b) (hR : ‖p + c • q‖ = c) :
    p = 0 ∧ ‖q‖ = 1 := by
  -- Squaring gives: ‖p‖² + 2x⟪p, q⟫ + x²‖q‖² = x²
  -- Rearranging: ‖p‖² + 2x⟪p, q⟫ + x²(‖q‖² - 1) = 0
  have ha_sq : ‖p‖^2 + 2 * a * ⟪p, q⟫ + a^2 * (‖q‖^2 - 1) = 0 := by
    have := congrArg (·^2) hP
    simp [norm_add_sq_real, norm_smul, mul_pow, sq_abs, inner_smul_right] at this
    linarith
  have hb_sq : ‖p‖^2 + 2 * b * ⟪p, q⟫ + b^2 * (‖q‖^2 - 1) = 0 := by
    have := congrArg (·^2) hQ
    simp [norm_add_sq_real, norm_smul, mul_pow, sq_abs, inner_smul_right] at this
    linarith
  have hc_sq : ‖p‖^2 + 2 * c * ⟪p, q⟫ + c^2 * (‖q‖^2 - 1) = 0 := by
    have := congrArg (·^2) hR
    simp [norm_add_sq_real, norm_smul, mul_pow, sq_abs, inner_smul_right] at this
    linarith
  -- Apply quad_three_roots with α = ‖q‖² - 1, β = 2⟪p, q⟫, γ = ‖p‖²
  have hcoeffs := quad_three_roots hab hac hbc
    (by linear_combination ha_sq : (‖q‖^2 - 1) * a^2 + 2 * ⟪p, q⟫ * a + ‖p‖^2 = 0)
    (by linear_combination hb_sq : (‖q‖^2 - 1) * b^2 + 2 * ⟪p, q⟫ * b + ‖p‖^2 = 0)
    (by linear_combination hc_sq : (‖q‖^2 - 1) * c^2 + 2 * ⟪p, q⟫ * c + ‖p‖^2 = 0)
  obtain ⟨hq2, _, hp2⟩ := hcoeffs
  exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hp2), by
    have hqpos : 0 ≤ ‖q‖ := norm_nonneg q
    nlinarith [sq_nonneg ‖q‖]⟩

/-- Equality case of Cauchy-Schwarz: if `‖q‖ = 1`, `⟪q, w⟫ = k` and `‖w‖ ^ 2 = k ^ 2`,
then `w = k • q`. -/
lemma eq_smul_of_norm_one {q w : EuclideanSpace ℝ (Fin 2)} {k : ℝ} (hq : ‖q‖ = 1)
    (h : ⟪q, w⟫ = k) (hw : ‖w‖ ^ 2 = k ^ 2) : w = k • q := by
  have hinner_symm : ⟪w, q⟫ = k := by rw [← real_inner_comm]; exact h
  have hnorm_km_sq : ‖k • q‖ ^ 2 = k ^ 2 := by
    rw [norm_smul, hq, Real.norm_eq_abs]
    simp
  have hnorm_sq : ‖w - k • q‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, inner_smul_right, hinner_symm, hw, hnorm_km_sq]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq))

/-! ### The key finiteness step -/

/-- Three distinct points cannot have the same pair of distance differences to two of the
vertices of a non-degenerate triangle. -/
lemma key {A B C P Q R : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (e1Q : dist Q A - dist Q B = dist P A - dist P B)
    (e1R : dist R A - dist R B = dist P A - dist P B)
    (e2Q : dist Q A - dist Q C = dist P A - dist P C)
    (e2R : dist R A - dist R C = dist P A - dist P C) : False := by
  obtain ⟨q, hq1, hq2⟩ := exists_inner_eq hABC (dist P A - dist P B) (dist P A - dist P C)
  have hPQ' := same_p hABC hq1 hq2 e1Q e2Q
  have hPR' := same_p hABC hq1 hq2 e1R e2R
  have hPQ_vec : P - Q = (dist P A - dist Q A) • q := by
    have eq1 : P - A - dist P A • q - (Q - A - dist Q A • q) = 0 := by rw [hPQ']; abel
    have eq2 : (P - Q) - (dist P A - dist Q A) • q = 0 := by convert eq1 using 1; module
    exact sub_eq_zero.mp eq2
  have hpq : dist P A ≠ dist Q A := by
    intro h
    simp [h] at hPQ_vec
    exact hPQ (sub_eq_zero.mp hPQ_vec)
  have hqr : dist Q A ≠ dist R A := by
    intro h
    have hQR_vec : Q - R = (dist Q A - dist R A) • q := by
      have eq1 : Q - A - dist Q A • q = R - A - dist R A • q := by rw [hPQ'.symm, hPR']
      have eq2 : Q - A - dist Q A • q - (R - A - dist R A • q) = 0 := by rw [eq1]; abel
      have eq3 : (Q - R) - (dist Q A - dist R A) • q = 0 := by convert eq2 using 1; module
      exact sub_eq_zero.mp eq3
    simp [h] at hQR_vec
    exact hQR (sub_eq_zero.mp hQR_vec)
  have hpr_vec : P - R = (dist P A - dist R A) • q := by
    have eq1 : P - A - dist P A • q - (R - A - dist R A • q) = 0 := by rw [hPR']; abel
    have eq2 : (P - R) - (dist P A - dist R A) • q = 0 := by convert eq1 using 1; module
    exact sub_eq_zero.mp eq2
  have hpr : dist P A ≠ dist R A := by
    intro h
    simp [h] at hpr_vec
    exact hPR (sub_eq_zero.mp hpr_vec)
  have hQR_vec : Q - R = (dist Q A - dist R A) • q := by
    have eq1 : Q - A - dist Q A • q = R - A - dist R A • q := by rw [hPQ'.symm, hPR']
    have eq2 : Q - A - dist Q A • q - (R - A - dist R A • q) = 0 := by rw [eq1]; abel
    have eq3 : (Q - R) - (dist Q A - dist R A) • q = 0 := by convert eq2 using 1; module
    exact sub_eq_zero.mp eq3
  let c_Q := ⟪Q - A, q⟫
  let s := ‖q‖^2
  have hPQ_sq : dist P A ^ 2 = dist Q A ^ 2 + 2 * (dist P A - dist Q A) * c_Q + (dist P A - dist Q A) ^ 2 * s := by
    have hPQ_eq : P - A = Q - A + (dist P A - dist Q A) • q := by
      have : P - Q = (dist P A - dist Q A) • q := hPQ_vec
      calc P - A = (P - Q) + (Q - A) := by module
        _ = (dist P A - dist Q A) • q + (Q - A) := by rw [this]
        _ = Q - A + (dist P A - dist Q A) • q := by module
    have h1 : dist P A ^ 2 = ‖P - A‖ ^ 2 := by rw [dist_eq_norm]
    have h2 : dist Q A ^ 2 = ‖Q - A‖ ^ 2 := by rw [dist_eq_norm]
    rw [h1, h2, hPQ_eq, norm_add_sq_real, inner_smul_right, norm_smul]
    simp [s]
    rw [mul_pow, sq_abs]
    ring
  have hPR_sq : dist P A ^ 2 = dist R A ^ 2 + 2 * (dist P A - dist R A) * ⟪R - A, q⟫ + (dist P A - dist R A) ^ 2 * s := by
    have hPR_eq : P - A = R - A + (dist P A - dist R A) • q := by
      have : P - R = (dist P A - dist R A) • q := hpr_vec
      calc P - A = (P - R) + (R - A) := by module
        _ = (dist P A - dist R A) • q + (R - A) := by rw [this]
        _ = R - A + (dist P A - dist R A) • q := by module
    have h1 : dist P A ^ 2 = ‖P - A‖ ^ 2 := by rw [dist_eq_norm]
    have h2 : dist R A ^ 2 = ‖R - A‖ ^ 2 := by rw [dist_eq_norm]
    rw [h1, h2, hPR_eq, norm_add_sq_real, inner_smul_right, norm_smul]
    simp [s]
    rw [mul_pow, sq_abs]
    ring
  have hQR_sq : dist Q A ^ 2 = dist R A ^ 2 + 2 * (dist Q A - dist R A) * ⟪R - A, q⟫ + (dist Q A - dist R A) ^ 2 * s := by
    have hQR_eq : Q - A = R - A + (dist Q A - dist R A) • q := by
      have : Q - R = (dist Q A - dist R A) • q := hQR_vec
      calc Q - A = (Q - R) + (R - A) := by module
        _ = (dist Q A - dist R A) • q + (R - A) := by rw [this]
        _ = R - A + (dist Q A - dist R A) • q := by module
    have h1 : dist Q A ^ 2 = ‖Q - A‖ ^ 2 := by rw [dist_eq_norm]
    have h2 : dist R A ^ 2 = ‖R - A‖ ^ 2 := by rw [dist_eq_norm]
    rw [h1, h2, hQR_eq, norm_add_sq_real, inner_smul_right, norm_smul]
    simp [s]
    rw [mul_pow, sq_abs]
    ring
  let a := dist P A
  let b := dist Q A
  let c := dist R A
  let cQ := ⟪Q - A, q⟫
  let cR := ⟪R - A, q⟫
  have hPQcQ : a ^ 2 = b ^ 2 + 2 * (a - b) * cQ + (a - b) ^ 2 * s := hPQ_sq
  have hQRcR : b ^ 2 = c ^ 2 + 2 * (b - c) * cR + (b - c) ^ 2 * s := hQR_sq
  have hPRcR : a ^ 2 = c ^ 2 + 2 * (a - c) * cR + (a - c) ^ 2 * s := hPR_sq
  have hPQcR : a ^ 2 = c ^ 2 + 2 * (a - b) * cQ + 2 * (b - c) * cR + (a - b) ^ 2 * s + (b - c) ^ 2 * s := by
    linarith
  have eq2 : b + c = 2 * cR + (b - c) * s := by
    have factored : b ^ 2 - c ^ 2 = (b - c) * (2 * cR + (b - c) * s) := by ring_nf; linarith
    have key : (b - c) * (b + c) = (b - c) * (2 * cR + (b - c) * s) := by ring_nf; linarith
    exact mul_left_cancel₀ (sub_ne_zero.mpr hqr) key
  have eq3 : a + c = 2 * cR + (a - c) * s := by
    have factored : a ^ 2 - c ^ 2 = (a - c) * (2 * cR + (a - c) * s) := by ring_nf; linarith
    have key : (a - c) * (a + c) = (a - c) * (2 * cR + (a - c) * s) := by ring_nf; linarith
    exact mul_left_cancel₀ (sub_ne_zero.mpr hpr) key
  have hProd1 : (a - b) * (1 - s) = 0 := by
    have sub_eq : a - b = (a - b) * s := by linarith
    linear_combination sub_eq
  have hs_eq : s = 1 := by
    have := mul_eq_zero.mp hProd1
    cases this with
    | inl h => exact absurd h (sub_ne_zero.mpr hpq)
    | inr h => linarith
  have hq_norm : ‖q‖ = 1 := by
    have hs_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
    simp [s] at hs_eq
    cases hs_eq with
    | inl h => exact h
    | inr h => linarith
  have hcQ : c_Q = b := by
    have h := hPQcQ
    simp [s, hs_eq] at h
    have factored : (a - b) * (c_Q - b) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_left (sub_ne_zero.mpr hpq))
  have hcR : cR = c := by
    simp [s, hs_eq] at eq2
    linarith
  have hQA_vec : Q - A = b • q := by
    apply eq_smul_of_norm_one hq_norm
    · rw [real_inner_comm]; exact hcQ
    · simp [dist_eq_norm, b]
  have hRA_vec : R - A = c • q := by
    apply eq_smul_of_norm_one hq_norm
    · rw [real_inner_comm]; exact hcR
    · simp [dist_eq_norm, c]
  have hPA_vec : P - A = a • q := by
    calc P - A = (P - Q) + (Q - A) := by module
      _ = (a - b) • q + b • q := by rw [hPQ_vec, hQA_vec]
      _ = a • q := by rw [sub_smul]; simp
  have hd_sq : (⟪q, B - A⟫) ^ 2 = dist A B ^ 2 := by
    have hPB_eq : P - B = (A - B) + a • q := by
      have : P - B = (P - A) + (A - B) := by module
      rw [this, hPA_vec]
      abel
    have hPB_sq : dist P B ^ 2 = dist A B ^ 2 - 2 * ⟪q, B - A⟫ * a + a ^ 2 := by
      have h1 : dist P B ^ 2 = ‖P - B‖ ^ 2 := by rw [dist_eq_norm]
      rw [h1, hPB_eq, norm_add_sq_real, inner_smul_right, norm_smul]
      simp [hq_norm]
      rw [dist_eq_norm]
      have hBAsub : ⟪q, B - A⟫ = -⟪q, A - B⟫ := by
        have : B - A = -(A - B) := by abel
        rw [this, inner_neg_right]
      rw [hBAsub, real_inner_comm q (A - B)]
      ring
    have hd : ⟪q, B - A⟫ = a - dist P B := hq1
    have hd2 : dist P B ^ 2 = dist A B ^ 2 - 2 * a * (a - dist P B) + a ^ 2 := by
      rw [hd] at hPB_sq
      linear_combination hPB_sq
    calc (⟪q, B - A⟫) ^ 2 = (a - dist P B) ^ 2 := by rw [hd]
      _ = a ^ 2 - 2 * a * dist P B + dist P B ^ 2 := by ring
      _ = dist A B ^ 2 := by linarith [hd2]
  have he_sq : (⟪q, C - A⟫) ^ 2 = dist A C ^ 2 := by
    have hPC_eq : P - C = (A - C) + a • q := by
      have : P - C = (P - A) + (A - C) := by module
      rw [this, hPA_vec]
      abel
    have hPC_sq : dist P C ^ 2 = dist A C ^ 2 - 2 * ⟪q, C - A⟫ * a + a ^ 2 := by
      have h1 : dist P C ^ 2 = ‖P - C‖ ^ 2 := by rw [dist_eq_norm]
      rw [h1, hPC_eq, norm_add_sq_real, inner_smul_right, norm_smul]
      simp [hq_norm]
      rw [dist_eq_norm]
      have hCAsub : ⟪q, C - A⟫ = -⟪q, A - C⟫ := by
        have : C - A = -(A - C) := by abel
        rw [this, inner_neg_right]
      rw [hCAsub, real_inner_comm q (A - C)]
      ring
    have he : ⟪q, C - A⟫ = a - dist P C := hq2
    have he2 : dist P C ^ 2 = dist A C ^ 2 - 2 * a * (a - dist P C) + a ^ 2 := by
      rw [he] at hPC_sq
      linear_combination hPC_sq
    calc (⟪q, C - A⟫) ^ 2 = (a - dist P C) ^ 2 := by rw [he]
      _ = a ^ 2 - 2 * a * dist P C + dist P C ^ 2 := by ring
      _ = dist A C ^ 2 := by linarith [he2]
  have hBA_par : ∃ r : ℝ, B - A = r • q := by
    use ⟪B - A, q⟫
    apply eq_smul_of_norm_one hq_norm (real_inner_comm _ _)
    rw [dist_eq_norm] at hd_sq
    rw [real_inner_comm] at hd_sq
    rw [norm_sub_rev] at hd_sq
    exact hd_sq.symm
  have hCA_par : ∃ t : ℝ, C - A = t • q := by
    use ⟪C - A, q⟫
    apply eq_smul_of_norm_one hq_norm (real_inner_comm _ _)
    rw [dist_eq_norm] at he_sq
    rw [real_inner_comm] at he_sq
    rw [norm_sub_rev] at he_sq
    exact he_sq.symm
  obtain ⟨r, hr⟩ := hBA_par
  obtain ⟨t, ht⟩ := hCA_par
  by_cases ht0 : t = 0
  · simp [ht0] at ht
    have hCA : C = A := sub_eq_zero.mp ht
    simp [hCA] at hABC
    exact hABC (collinear_pair ℝ B A)
  · have hBA_par_C : B - A = (r / t) • (C - A) := by
      rw [hr, ht]
      rw [smul_smul]
      congr 1
      field_simp
    have hcoll : Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      use A, C - A
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨r / t, by rw [← hBA_par_C]; simp⟩
      · exact ⟨1, by simp⟩
    exact hABC hcoll
/-- Any distance difference within `S` is an integer. -/
lemma exists_int_diff {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n) {x A B : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ S) (hA : A ∈ S) (hB : B ∈ S) : ∃ k : ℤ, dist x A - dist x B = (k : ℝ) := by
  obtain ⟨na, hna⟩ := hint x hx A hA
  obtain ⟨nb, hnb⟩ := hint x hx B hB
  exact ⟨na - nb, by simp [hna, hnb]⟩

/-- A point collinear with two distinct points lies on the line through them. -/
lemma mem_line_of_collinear {A B x : EuclideanSpace ℝ (Fin 2)} (hAB : A ≠ B)
    (h : Collinear ℝ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ t : ℝ, x = A + t • (B - A) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, v, hv⟩ := h
  have hA : A ∈ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  have hB : B ∈ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  have hx : x ∈ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  obtain ⟨rA, hA'⟩ := hv A hA
  obtain ⟨rB, hB'⟩ := hv B hB
  obtain ⟨rx, hx'⟩ := hv x hx
  -- B - A = (rB - rA) • v
  have hBA : B - A = (rB - rA) • v := by rw [hA', hB']; ext i; simp [vadd_eq_add]; ring
  -- x - A = (rx - rA) • v
  have hxA : x - A = (rx - rA) • v := by rw [hA', hx']; ext i; simp [vadd_eq_add]; ring
  -- Since A ≠ B, we have rA ≠ rB
  have hr : rA ≠ rB := by
    intro hr_eq
    apply hAB
    rw [hA', hB', hr_eq]
  -- Let t = (rx - rA) / (rB - rA)
  use (rx - rA) / (rB - rA)
  -- Show x = A + t • (B - A)
  have hr' : rB - rA ≠ 0 := sub_ne_zero.mpr hr.symm
  rw [hBA]
  rw [hx', hA']
  rw [smul_smul]
  field_simp
  ext i
  simp [vadd_eq_add]
  ring

/-- A set of points with integral pairwise distances containing a non-degenerate triangle
is finite. -/
lemma finite_of_not_collinear {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n)
    {A B C : EuclideanSpace ℝ (Fin 2)} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) : S.Finite := by
  -- For each point P in S, define signature s(P) = (d1, d2) where
  -- d1 = dist P A - dist P B and d2 = dist P A - dist P C
  -- By exists_int_diff, d1 and d2 are integers.
  -- By triangle inequality: |d1| ≤ dist A B and |d2| ≤ dist A C
  -- So there are finitely many possible signatures.
  -- By key, each signature corresponds to at most 2 points.
  -- Therefore S is finite.
  
  -- First, bound the possible values of d1 and d2 using triangle inequality
  let M1 : ℤ := ⌈dist A B⌉
  let M2 : ℤ := ⌈dist A C⌉
  
  -- The signature function
  let σ : EuclideanSpace ℝ (Fin 2) → ℤ × ℤ := fun P =>
    ((⌊dist P A - dist P B⌋, ⌊dist P A - dist P C⌋))
  
  -- The signature values are bounded by the side lengths
  -- We'll show the range is a subset of a finite product of finite sets
  have hbound : ∀ P ∈ S, 
      -M1 ≤ ⌊dist P A - dist P B⌋ ∧ ⌊dist P A - dist P B⌋ ≤ M1 ∧ 
      -M2 ≤ ⌊dist P A - dist P C⌋ ∧ ⌊dist P A - dist P C⌋ ≤ M2 := by
    intro P hP
    -- Use triangle inequality: |dist P A - dist P B| ≤ dist A B
    -- Triangle inequality
    -- dist_triangle P A B : dist P B ≤ dist P A + dist A B
    have htri1 : dist P B ≤ dist P A + dist A B := dist_triangle P A B
    have htri2 : dist P A ≤ dist P B + dist A B := by simpa [dist_comm A B] using dist_triangle P B A
    have htri3 : dist P C ≤ dist P A + dist A C := dist_triangle P A C
    have htri4 : dist P A ≤ dist P C + dist A C := by simpa [dist_comm A C] using dist_triangle P C A
    -- Derive bounds on differences
    have h1 : dist P A - dist P B ≤ dist A B := by linarith
    have h2 : dist P B - dist P A ≤ dist A B := by linarith
    have h3 : dist P A - dist P C ≤ dist A C := by linarith
    have h4 : dist P C - dist P A ≤ dist A C := by linarith
    -- Now bound the floor values
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- -M1 ≤ ⌊dist P A - dist P B⌋
      have h5 : -(dist A B) ≤ dist P A - dist P B := by linarith
      have h6 : ⌊-(dist A B)⌋ ≤ ⌊dist P A - dist P B⌋ := Int.floor_mono h5
      have h7 : -⌈dist A B⌉ ≤ ⌊-(dist A B)⌋ := by simp [Int.floor_neg]
      linarith
    · -- ⌊dist P A - dist P B⌋ ≤ M1
      calc ⌊dist P A - dist P B⌋ ≤ ⌊dist A B⌋ := Int.floor_mono h1
        _ ≤ ⌈dist A B⌉ := Int.floor_le_ceil _
    · -- -M2 ≤ ⌊dist P A - dist P C⌋
      have h5 : -(dist A C) ≤ dist P A - dist P C := by linarith
      have h6 : ⌊-(dist A C)⌋ ≤ ⌊dist P A - dist P C⌋ := Int.floor_mono h5
      have h7 : -⌈dist A C⌉ ≤ ⌊-(dist A C)⌋ := by simp [Int.floor_neg]
      linarith
    · -- ⌊dist P A - dist P C⌋ ≤ M2
      calc ⌊dist P A - dist P C⌋ ≤ ⌊dist A C⌋ := Int.floor_mono h3
        _ ≤ ⌈dist A C⌉ := Int.floor_le_ceil _
  
  -- So the range of σ on S is finite
  have hrange_finite : (Set.range (σ ∘ Subtype.val : S → ℤ × ℤ)).Finite := by
    -- The range is contained in a finite product of finite sets
    let bounds : Set (ℤ × ℤ) := {p | -M1 ≤ p.1 ∧ p.1 ≤ M1 ∧ -M2 ≤ p.2 ∧ p.2 ≤ M2}
    have hbounds_finite : bounds.Finite := by
      apply Set.Finite.subset (Set.Finite.prod (Set.finite_Icc (-M1) M1) (Set.finite_Icc (-M2) M2))
      intro p hp
      rw [Set.mem_prod]
      simp at hp ⊢
      exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩
    apply Set.Finite.subset hbounds_finite
    intro p hp
    simp only [Set.mem_range] at hp
    obtain ⟨⟨P, hP⟩, hPp⟩ := hp
    rw [← hPp]
    exact hbound P hP
  
  -- Each fiber has at most 2 points by key
  -- Use Set.Finite.of_finite_image_union_preimage or similar
  -- Define the inclusion S → S (as subtype) and compose with σ
  let f : S → ℤ × ℤ := σ ∘ Subtype.val
  have hf_image_finite : (f '' Set.univ).Finite := by
    convert hrange_finite
    ext x
    simp [f]
  -- Each fiber f⁻¹({r}) has at most 2 elements
  have hfiber_card : ∀ r, (f ⁻¹' {r}).Finite := by
    intro r
    -- The fiber over r consists of elements x : S with f x = r
    -- i.e., points P ∈ S with σ P = r
    -- By key, at most 2 such points exist
    by_contra hinf
    -- Extract 3 distinct points from the infinite fiber
    have hInf : Set.Infinite (f ⁻¹' {r}) := by simpa using hinf
    -- Get 3 distinct elements
    obtain ⟨p, hp⟩ := Set.Infinite.nonempty hInf
    have hInf1 : Set.Infinite ((f ⁻¹' {r}) \ {p}) := by
      by_contra hfin
      apply hInf
      exact Set.Finite.subset (Set.Finite.union (not_not.mp hfin) (Set.finite_singleton p))
        (fun x hx => by simp at hx ⊢; tauto)
    obtain ⟨q, hq_set, hq'⟩ := Set.Infinite.nonempty hInf1
    have hInf2 : Set.Infinite ((f ⁻¹' {r}) \ ({p, q} : Set S)) := by
      by_contra hfin
      apply hInf
      exact Set.Finite.subset (Set.Finite.union (not_not.mp hfin) (Set.toFinite {p, q}))
        (fun x hx => by simp at hx ⊢; tauto)
    obtain ⟨s, hs_set, hs'⟩ := Set.Infinite.nonempty hInf2
    -- These are 3 distinct elements with f p = f q = f s = r
    have hp_eq : f p = r := hp
    have hq_eq : f q = r := hq_set
    have hs_eq : f s = r := hs_set
    -- Convert to points in EuclideanSpace
    let P := p.val
    let Q := q.val
    let R := s.val
    have hP : P ∈ S := p.property
    have hQ : Q ∈ S := q.property
    have hR : R ∈ S := s.property
    have hpq : P ≠ Q := by
      intro h
      have heq : p = q := Subtype.ext h
      exact hq' heq.symm
    have hps : P ≠ R := by
      intro h
      have heq : p = s := Subtype.ext h
      simp [heq] at hs'
    have hqs : Q ≠ R := by
      intro h
      have heq : q = s := Subtype.ext h
      simp [heq] at hs'
    -- Extract the signature values
    have hr1 : ⌊dist P A - dist P B⌋ = r.1 := by
      have := congrArg Prod.fst hp_eq
      simp [f, σ] at this
      exact this
    have hr2 : ⌊dist P A - dist P C⌋ = r.2 := by
      have := congrArg Prod.snd hp_eq
      simp [f, σ] at this
      exact this
    have hq1 : ⌊dist Q A - dist Q B⌋ = r.1 := by
      have := congrArg Prod.fst hq_eq
      simp [f, σ] at this
      exact this
    have hq2 : ⌊dist Q A - dist Q C⌋ = r.2 := by
      have := congrArg Prod.snd hq_eq
      simp [f, σ] at this
      exact this
    have hs1 : ⌊dist R A - dist R B⌋ = r.1 := by
      have := congrArg Prod.fst hs_eq
      simp [f, σ] at this
      exact this
    have hs2 : ⌊dist R A - dist R C⌋ = r.2 := by
      have := congrArg Prod.snd hs_eq
      simp [f, σ] at this
      exact this
    -- The distance differences are integers (by exists_int_diff)
    obtain ⟨d1, hd1⟩ := exists_int_diff hint hP hA hB
    obtain ⟨d2, hd2⟩ := exists_int_diff hint hP hA hC
    -- Since the floors equal r.1 and r.2, and the values are integers, we have:
    have hP_d1 : dist P A - dist P B = r.1 := by rw [hd1]; simp_all
    have hP_d2 : dist P A - dist P C = r.2 := by rw [hd2]; simp_all
    have hQ_d1 : dist Q A - dist Q B = r.1 := by
      obtain ⟨d1Q, hd1Q⟩ := exists_int_diff hint hQ hA hB
      rw [hd1Q]; simp_all
    have hQ_d2 : dist Q A - dist Q C = r.2 := by
      obtain ⟨d2Q, hd2Q⟩ := exists_int_diff hint hQ hA hC
      rw [hd2Q]; simp_all
    have hR_d1 : dist R A - dist R B = r.1 := by
      obtain ⟨d1S, hd1S⟩ := exists_int_diff hint hR hA hB
      rw [hd1S]; simp_all
    have hR_d2 : dist R A - dist R C = r.2 := by
      obtain ⟨d2S, hd2S⟩ := exists_int_diff hint hR hA hC
      rw [hd2S]; simp_all
    -- Apply key: we have P, Q, R with same distance differences
    have e1Q : dist Q A - dist Q B = dist P A - dist P B := by rw [hQ_d1, hP_d1]
    have e1S : dist R A - dist R B = dist P A - dist P B := by rw [hR_d1, hP_d1]
    have e2Q : dist Q A - dist Q C = dist P A - dist P C := by rw [hQ_d2, hP_d2]
    have e2S : dist R A - dist R C = dist P A - dist P C := by rw [hR_d2, hP_d2]
    exact key hABC hpq hps hqs e1Q e1S e2Q e2S
  -- By contradiction: if S is infinite, some fiber is infinite
  -- But each fiber has ≤ 2 points by key
  by_contra hinf
  -- The infinite set S maps to a finite set via f, so some fiber is infinite
  -- f '' Set.univ is finite, Set.univ (the subtype) is infinite
  -- By Set.Infinite.exists_infinite_fiber, some fiber is infinite
  have hfiber_infinite : ∃ r, Set.Infinite (f ⁻¹' {r}) := by
    by_contra h
    push_neg at h
    -- Every fiber is finite
    have hfib_all_finite : ∀ r, (f ⁻¹' {r}).Finite := h
    -- The union of all fibers is Set.univ
    have hunion : ⋃ r, f ⁻¹' {r} = Set.univ := by ext x; simp
    -- Set.univ is infinite (since S is infinite)
    have huniv_inf : Set.Infinite (Set.univ : Set S) := by
      by_contra hfin
      push_neg at hfin
      have hS_fin : S.Finite := by
        have : Finite S := Set.finite_univ_iff.mp hfin
        exact Set.finite_coe_iff.mpr this
      exact hinf hS_fin
    -- Infinite set cannot be union of finitely many finite sets
    have hfiber_range_fin : (Set.range f).Finite := by
      simp only [Set.range, Set.image_univ] at hf_image_finite ⊢
      exact hf_image_finite
    have hsub : (Set.univ : Set S) ⊆ ⋃ r ∈ Set.range f, f ⁻¹' {r} := fun x _ => by
      simp only [Set.mem_iUnion]
      use f x
      simp
    have hunion_fin : (⋃ r ∈ Set.range f, f ⁻¹' {r}).Finite := by
      apply Set.Finite.biUnion hfiber_range_fin
      intro r _
      exact hfib_all_finite r
    exact huniv_inf (Set.Finite.subset hunion_fin hsub)
  obtain ⟨r, hr_inf⟩ := hfiber_infinite
  -- A fiber corresponds to points with the same signature (d1, d2)
  -- By key, at most 2 such points exist
  exact hr_inf (hfiber_card r)

/-- If `x` is not on the line through the distinct points `A` and `B`, then `A`, `B`, `x` are
not collinear. -/
lemma not_collinear_of_not_mem_line {A B x : EuclideanSpace ℝ (Fin 2)} (hAB : A ≠ B)
    (h : ¬ ∃ t : ℝ, x = A + t • (B - A)) :
    ¬ Collinear ℝ ({A, B, x} : Set (EuclideanSpace ℝ (Fin 2))) :=
  fun hcol => h (mem_line_of_collinear hAB hcol)

/-- The Erdős–Anning theorem: an infinite set of points in the plane with all pairwise distances
    integers must be collinear. -/
theorem erdos_anning (S : Set (EuclideanSpace ℝ (Fin 2))) (hinf : S.Infinite)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n) :
    ∃ (p v : EuclideanSpace ℝ (Fin 2)), ∀ x ∈ S, ∃ t : ℝ, x = p + t • v := by
  have h_coll : Collinear ℝ S := Classical.not_not.1 fun h_not_coll => by
    -- S is not collinear, so there exist 3 non-collinear points
    -- Since S is infinite, we can find two distinct points A, B in S
    obtain ⟨A, hA⟩ := hinf.to_subtype.nonempty
    have h_S_nontrivial : ∃ B ∈ S, B ≠ A := by
      by_contra h_all_eq_A
      push_neg at h_all_eq_A
      have : S ⊆ {A} := fun x hx => Set.eq_of_mem_singleton (h_all_eq_A x hx)
      exact hinf (Set.Finite.subset (Set.finite_singleton A) this)
    obtain ⟨B, hB, hBA⟩ := h_S_nontrivial
    -- If S is not collinear, there exists a point C not on the line through A and B
    -- The line through A and B is {A + t • (B - A) | t : ℝ}
    have hC : ∃ C ∈ S, ¬∃ t : ℝ, C = A + t • (B - A) := by
      by_contra h_all_on_line
      push_neg at h_all_on_line
      -- If all points are on the line through A and B, then S is collinear
      apply h_not_coll
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      use A, B - A
      intro x hx
      obtain ⟨t, ht⟩ := h_all_on_line x hx
      use t
      simp [ht]
      rw [add_comm]
    obtain ⟨C, hC_mem, hC_not_line⟩ := hC
    -- A, B, C are not collinear because C is not on the line through A and B
    have hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hcol
      exact hC_not_line (mem_line_of_collinear (Ne.symm hBA) hcol)
    exact hinf (finite_of_not_collinear hint hA hB hC_mem hABC)
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h_coll
  obtain ⟨p₀, v, hv⟩ := h_coll
  use p₀, v
  intro x hx
  obtain ⟨t, ht⟩ := hv x hx
  use t
  simp [ht]
  rw [add_comm]

end Brockian.MsErdosAnning

