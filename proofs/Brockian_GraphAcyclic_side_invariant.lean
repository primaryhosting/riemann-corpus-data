import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/
def twinAdm {n : ℕ} (a : ZMod n) : Prop := IsUnit a ∧ IsUnit (a + 2)

/-- The +3 flow graph on ℤ/n: a ~ b when they differ by ±3. -/
def plusThreeGraph (n : ℕ) : SimpleGraph (ZMod n) where
  Adj a b := (b - a = 3 ∨ a - b = 3) ∧ a ≠ b
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

section Height

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- If `g` is an injective "height" function whose values change by exactly one along every edge
of `H`, then, given `a b` with `g b = g a + 1`, a walk of `H` avoiding the edge `s(a, b)` cannot
cross the level `g a`. -/
lemma side_invariant (g : V → ℤ) (hinj : Function.Injective g) {a b : V} (h1 : g b = g a + 1)
    {H : SimpleGraph V} (hstep : ∀ ⦃u v : V⦄, H.Adj u v → g v = g u + 1 ∨ g v = g u - 1)
    {x y : V} (p : H.Walk x y) (hp : s(a, b) ∉ p.edges) : g x ≤ g a ↔ g y ≤ g a := by
  induction p with
  | nil => simp
  | @cons u v w hd tail IH =>
    rw [Walk.edges_cons] at hp
    simp at hp
    have IH' := IH hp.2
    have hp_ne := hp.1
    have huv_step : g u ≤ g a ↔ g v ≤ g a := by
      rcases hstep hd with hv | hv
      · -- `g v = g u + 1`: crossing the level would force the edge to be `s(a, b)`
        constructor
        · intro hu
          by_contra hna
          push_neg at hna
          have hu_eq : u = a := hinj (by linarith : g u = g a)
          have hv_eq : v = b := hinj (by rw [hv, hu_eq, h1])
          exact hp_ne.1 hu_eq.symm hv_eq.symm
        · intro hv_le
          linarith
      · -- `g v = g u - 1`: crossing the level would force the edge to be `s(b, a)`
        constructor
        · intro hu
          linarith
        · intro hv_le
          by_contra hna
          push_neg at hna
          have hu_eq : u = b := hinj (by linarith : g u = g b)
          have hv_eq : v = a := hinj (by linarith : g v = g a)
          exact hp_ne.2 hv_eq.symm hu_eq.symm
    rw [huv_step, IH']

/-- With an injective height function as above, every edge is a bridge. -/
lemma isBridge_of_int_height (g : V → ℤ) (hinj : Function.Injective g)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → g y = g x + 1 ∨ g y = g x - 1)
    {a b : V} (hab : G.Adj a b) (h1 : g b = g a + 1) : G.IsBridge s(a, b) := by
  refine ⟨hab, ?_⟩
  rintro ⟨p⟩
  -- `p` is a walk from `a` to `b` in `G` with the edge `s(a, b)` deleted
  have hp : s(a, b) ∉ p.edges := by
    intro he
    obtain ⟨d, -, hd_edge⟩ := List.mem_map.mp he
    have hd_edge_set : d.edge ∈ (G \ fromEdgeSet {s(a, b)}).edgeSet := d.edge_mem
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, Set.mem_diff] at hd_edge_set
    simp [hd_edge, Sym2.isDiag_iff_proj_eq, hab.ne] at hd_edge_set
  have hstep_sub : ∀ ⦃u v : V⦄, (G \ fromEdgeSet {s(a, b)}).Adj u v →
      g v = g u + 1 ∨ g v = g u - 1 := fun _ _ hadj => hstep hadj.1
  have := side_invariant g hinj h1 hstep_sub p hp
  simp only [le_refl, true_iff] at this
  linarith [this]

/-- A graph admitting an injective `ℤ`-valued height function such that adjacent vertices have
heights differing by exactly one is acyclic. -/
theorem acyclic_of_int_height (g : V → ℤ) (hinj : Function.Injective g)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → g y = g x + 1 ∨ g y = g x - 1) :
    G.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rcases hstep hvw with h | h
  · exact isBridge_of_int_height g hinj hstep hvw h
  · have := isBridge_of_int_height g hinj hstep hvw.symm (by linarith)
    rwa [Sym2.eq_swap] at this

end Height

section Arith

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
/-- `3` is invertible mod `M` when `gcd(3, M) = 1`. -/
lemma three_mul_inv (h3 : Nat.Coprime 3 M) : (3 : ZMod M) * (3 : ZMod M)⁻¹ = 1 := by
  simpa using ZMod.coe_mul_inv_eq_one (n := M) 3 h3

/-- Taking `ZMod.val` turns `+1` into `+1` on the integers, as long as we do not wrap to `0`. -/
lemma val_succ_of_ne_zero {x y : ZMod M} (h : y = x + 1) (hy : y ≠ 0) :
    ((y.val : ℤ)) = (x.val : ℤ) + 1 := by
  have hM : 1 < M := by
    by_contra hle
    push_neg at hle
    interval_cases M
    · exact NeZero.ne (n := 0) rfl
    · rw [h] at hy
      exact hy (by subsingleton)
  haveI : Fact (1 < M) := ⟨hM⟩
  rw [h]
  have h1 : (x + 1).val = (x.val + 1) % M := by
    rw [ZMod.val_add]
    have : ZMod.val 1 = 1 := ZMod.val_one (n := M)
    simp [this]
  have hxv : x.val < M := ZMod.val_lt x
  have hne : (x + 1).val ≠ 0 := by
    rw [h] at hy
    simp [ZMod.val_eq_zero]
    exact hy
  rw [h1] at hne
  have hlt : x.val + 1 < M := by
    by_contra hge
    push_neg at hge
    have : x.val + 1 = M := Nat.le_antisymm (Nat.succ_le_of_lt hxv) hge
    simp [this] at hne
  rw [h1, Nat.mod_eq_of_lt hlt]
  norm_cast

/-- The height of a twin-admissible residue: the position of `a` along the `+3` cycle. -/
noncomputable def height (M : ℕ) (v : {a : ZMod M | twinAdm a}) : ℤ :=
  (((v : ZMod M) * (3 : ZMod M)⁻¹).val : ℤ)

lemma height_injective (h3 : Nat.Coprime 3 M) : Function.Injective (height M) := by
  intro a b hab
  simp [height] at hab
  have h1 : (a * 3⁻¹ : ZMod M).val = (b * 3⁻¹ : ZMod M).val := by
    have : ((a * 3⁻¹ : ZMod M).val : ℤ) = ((b * 3⁻¹ : ZMod M).val : ℤ) := by
      rw [ZMod.cast.eq_def] at hab
      rcases M with _ | M <;> simp_all
    exact Nat.cast_inj.mp this
  have h2 : ((a : ZMod M) * 3⁻¹) = ((b : ZMod M) * 3⁻¹) := by
    apply ZMod.val_injective M
    exact h1
  have h3' : IsUnit (3 : ZMod M) := by
    rw [isUnit_iff_exists_inv]
    use (3 : ZMod M)⁻¹
    exact three_mul_inv h3
  have h3'' : IsUnit ((3 : ZMod M)⁻¹) := by
    rw [isUnit_iff_exists_inv]
    use (3 : ZMod M)
    have := three_mul_inv h3
    rw [mul_comm] at this
    exact this
  have inv_mul : (3 : ZMod M)⁻¹ * 3 = 1 := by
    have h := three_mul_inv h3
    rw [mul_comm] at h
    simpa using h
  have h3''' : (a : ZMod M) = (b : ZMod M) := by
    calc (a : ZMod M) = (a : ZMod M) * 3⁻¹ * 3 := by rw [mul_assoc, inv_mul, mul_one]
      _ = (b : ZMod M) * 3⁻¹ * 3 := by rw [h2]
      _ = (b : ZMod M) := by rw [mul_assoc, inv_mul, mul_one]
  exact Subtype.ext h3'''

lemma height_step (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    ∀ ⦃x y : {a : ZMod M | twinAdm a}⦄,
      (SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)).Adj x y →
      height M y = height M x + 1 ∨ height M y = height M x - 1 := by
  intro x y hadj
  -- Extract the adjacency condition from plusThreeGraph
  simp only [SimpleGraph.induce] at hadj
  simp only [plusThreeGraph] at hadj
  obtain ⟨hdiff, _⟩ := hadj
  -- hdiff : y - x = 3 ∨ x - y = 3
  -- First, establish that 3 * 3⁻¹ = 1 in ZMod M
  have h3inv : (3 : ZMod M) * (3 : ZMod M)⁻¹ = 1 := three_mul_inv h3
  obtain h | h := hdiff
  · -- Case: y = x + 3
    -- Then y * 3⁻¹ = x * 3⁻¹ + 1
    left
    -- From h : y - x = 3, we get y = x + 3
    -- The subtype coercion preserves subtraction
    have hdiff' : (y : ZMod M) - (x : ZMod M) = 3 := by
      simpa using h
    have hy : (y : ZMod M) = (x : ZMod M) + 3 := by
      have := hdiff'; rw [sub_eq_iff_eq_add] at this; rw [add_comm] at this; exact this
    -- So y * 3⁻¹ = x * 3⁻¹ + 1
    have hprod : (y : ZMod M) * (3 : ZMod M)⁻¹ = (x : ZMod M) * (3 : ZMod M)⁻¹ + 1 := by
      rw [hy]; ring_nf
      rw [mul_comm ((3 : ZMod M)⁻¹) 3]; rw [h3inv]; ring
    -- Since y is twin-admissible, y is a unit, so y ≠ 0
    haveI : NeZero M := ‹_›
    haveI : Fact (1 < M) := ⟨hM⟩
    haveI : Nontrivial (ZMod M) := ZMod.nontrivial M
    have hy_unit : IsUnit (y : ZMod M) := y.2.1
    have hy_ne_zero : (y : ZMod M) ≠ 0 := hy_unit.ne_zero
    -- If (x * 3⁻¹).val = M - 1, then x * 3⁻¹ + 1 = 0, so y * 3⁻¹ = 0, so y = 0
    -- This contradicts y ≠ 0. So (x * 3⁻¹).val < M - 1
    have hval_lt : ((x : ZMod M) * (3 : ZMod M)⁻¹).val < M - 1 := by
      by_contra h_contra
      push_neg at h_contra
      -- Since val is in [0, M-1], we have (x * 3⁻¹).val = M - 1
      have hval_eq : ((x : ZMod M) * (3 : ZMod M)⁻¹).val = M - 1 := by
        have h1 : ((x : ZMod M) * (3 : ZMod M)⁻¹).val < M := ZMod.val_lt _
        omega
      -- In ZMod M, x * 3⁻¹ = M - 1 = -1
      have hx3inv_eq_neg1 : (x : ZMod M) * (3 : ZMod M)⁻¹ = -1 := by
        have h1 : ((M - 1 : ℕ) : ZMod M) = -1 := by
          have h2 : ((M - 1 : ℕ) : ZMod M) + 1 = 0 := by simp [Nat.cast_sub (by omega : 1 ≤ M)]
          exact eq_neg_of_add_eq_zero_left h2
        rw [← h1, ← hval_eq]
        rw [ZMod.natCast_val, ZMod.cast_id]
      -- So y * 3⁻¹ = -1 + 1 = 0
      have hy3inv_eq_zero : (y : ZMod M) * (3 : ZMod M)⁻¹ = 0 := by
        rw [hprod, hx3inv_eq_neg1]; ring
      -- Since 3⁻¹ is a unit, y = 0
      have hy_eq_zero : (y : ZMod M) = 0 := by
        have h3_ne_zero : (3 : ZMod M) ≠ 0 := by
          intro h3eq0
          rw [h3eq0] at h3inv
          simp at h3inv
        have h3inv_ne_zero : (3 : ZMod M)⁻¹ ≠ 0 := by
          intro h3inv_eq0
          rw [h3inv_eq0] at h3inv
          simp at h3inv
        by_cases hy : (y : ZMod M) = 0
        · exact hy
        · exfalso
          have h1 : (y : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 0 := by rw [hy3inv_eq_zero]; ring
          rw [mul_assoc] at h1
          rw [mul_comm (3 : ZMod M)⁻¹ 3, h3inv] at h1
          simp at h1
          exact hy h1
      exact hy_ne_zero hy_eq_zero
    -- Now use hval_lt to show the val equality
    have hval_eq' : ((y : ZMod M) * (3 : ZMod M)⁻¹).val = ((x : ZMod M) * (3 : ZMod M)⁻¹).val + 1 := by
      rw [hprod]
      have hv : ((x : ZMod M) * (3 : ZMod M)⁻¹).val < M := ZMod.val_lt _
      have hv' : ((x : ZMod M) * (3 : ZMod M)⁻¹).val + 1 < M := by omega
      have hne : (y : ZMod M) * (3 : ZMod M)⁻¹ ≠ 0 := by
        intro heq
        apply hy_ne_zero
        -- if y * 3⁻¹ = 0 and 3⁻¹ ≠ 0, then y = 0
        have h3inv_ne : (3 : ZMod M)⁻¹ ≠ 0 := by
          intro h
          rw [h] at h3inv
          simp at h3inv
        -- Multiply both sides by 3: y * 3⁻¹ * 3 = 0 * 3 = 0
        have : (y : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 0 := by rw [heq]; ring
        rw [mul_assoc, mul_comm (3 : ZMod M)⁻¹ 3, h3inv, mul_one] at this
        exact this
      have hval_eq' := val_succ_of_ne_zero hprod hne
      norm_cast at hval_eq'
      rw [hprod] at hval_eq'
      exact hval_eq'
    simp [height, hval_eq']
  · -- Case: x = y + 3
    -- Then x * 3⁻¹ = y * 3⁻¹ + 1, so y * 3⁻¹ = x * 3⁻¹ - 1
    right
    haveI : NeZero M := ‹_›
    haveI : Fact (1 < M) := ⟨hM⟩
    haveI : Nontrivial (ZMod M) := ZMod.nontrivial M
    -- From h : x - y = 3, we get x = y + 3
    have hdiff' : (x : ZMod M) - (y : ZMod M) = 3 := by simpa using h
    have hx : (x : ZMod M) = (y : ZMod M) + 3 := by
      have := hdiff'; rw [sub_eq_iff_eq_add] at this; rw [add_comm] at this; exact this
    -- So x * 3⁻¹ = y * 3⁻¹ + 1
    have hprod : (x : ZMod M) * (3 : ZMod M)⁻¹ = (y : ZMod M) * (3 : ZMod M)⁻¹ + 1 := by
      rw [hx]; ring_nf
      rw [mul_comm ((3 : ZMod M)⁻¹) 3]; rw [h3inv]; ring
    -- x is a unit, so x ≠ 0, so x * 3⁻¹ ≠ 0
    have hx_unit : IsUnit (x : ZMod M) := x.2.1
    have hx_ne_zero : (x : ZMod M) ≠ 0 := hx_unit.ne_zero
    -- So (x * 3⁻¹).val ≥ 1
    have hx3inv_ne : (x : ZMod M) * (3 : ZMod M)⁻¹ ≠ 0 := by
      intro heq
      have h3inv_ne : (3 : ZMod M)⁻¹ ≠ 0 := by
        intro h
        rw [h] at h3inv
        simp at h3inv
      have : (x : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 0 := by rw [heq]; ring
      rw [mul_assoc, mul_comm (3 : ZMod M)⁻¹ 3, h3inv, mul_one] at this
      exact hx_ne_zero this
    have hx3inv_val_pos : ((x : ZMod M) * (3 : ZMod M)⁻¹).val ≥ 1 := by
      by_contra h_neg
      have h0 : ((x : ZMod M) * (3 : ZMod M)⁻¹).val = 0 := by omega
      simp [ZMod.val_eq_zero] at h0
      exact hx3inv_ne h0
    -- Now show (y * 3⁻¹).val = (x * 3⁻¹).val - 1
    have hval_eq' : ((y : ZMod M) * (3 : ZMod M)⁻¹).val = ((x : ZMod M) * (3 : ZMod M)⁻¹).val - 1 := by
      have heq : (y : ZMod M) * (3 : ZMod M)⁻¹ = (x : ZMod M) * (3 : ZMod M)⁻¹ - 1 := by
        rw [hprod]; ring
      rw [heq]
      -- We'll show (x * 3⁻¹ - 1).val = (x * 3⁻¹).val - 1
      -- First show x * 3⁻¹ - 1 ≠ 0
      have hne : (x : ZMod M) * (3 : ZMod M)⁻¹ - 1 ≠ 0 := by
        intro hsub
        have hx3eq1 : (x : ZMod M) * (3 : ZMod M)⁻¹ = 1 := by linear_combination hsub
        -- From x * 3⁻¹ = 1, we get x = 3
        have hx_eq_3 : (x : ZMod M) = 3 := by
          have : (x : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 1 * 3 := by rw [hx3eq1]
          rw [mul_assoc, mul_comm (3 : ZMod M)⁻¹ 3, h3inv, mul_one, one_mul] at this
          exact this
        -- Since x = y + 3 and x = 3, we get y = 0
        have hy_eq_0 : (y : ZMod M) = 0 := by simpa [hx_eq_3] using hx
        -- But y is twin-admissible, so y is a unit, so y ≠ 0
        exact y.2.1.ne_zero hy_eq_0
      -- Now use that (a - 1).val = a.val - 1 when a ≠ 0 and a - 1 ≠ 0
      set a := (x : ZMod M) * (3 : ZMod M)⁻¹ with ha_def
      have ha_ne : a ≠ 0 := hx3inv_ne
      have ha_eq_b1 : a = (a - 1) + 1 := by ring
      have hab : (a.val : ℤ) = ((a - 1).val : ℤ) + 1 :=
        val_succ_of_ne_zero ha_eq_b1 ha_ne
      omega
    show (((y : ZMod M) * (3 : ZMod M)⁻¹).val : ℤ) = (((x : ZMod M) * (3 : ZMod M)⁻¹).val : ℤ) - 1
    rw [hval_eq', Int.ofNat_sub hx3inv_val_pos]; rfl

end Arith

/-- Gate sub-brick 2 (the hard SimpleGraph step): for a modulus M coprime to 3, the induced
subgraph of the +3 flow on the twin-admissible residues is ACYCLIC. Intuition: when gcd(3,M)=1
the +3 map is a single M-cycle over all of ℤ/M; the residue 0 is never twin-admissible (0 is not
a unit for M>1), so the admissible vertex set is a PROPER subset — deleting ≥1 vertex from a cycle
leaves a disjoint union of paths, which has no cycle. (Arithmetic facts available to reproduce:
`a + 3*(k:ZMod M) = a → M ∣ k` for a unit 3, and 0 is not a unit in a nontrivial ZMod M.) -/
theorem twin_admissible_induced_acyclic (M : ℕ) [NeZero M]
    (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    (SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)).IsAcyclic :=
  acyclic_of_int_height (height M) (height_injective h3) (height_step h3 hM)

end Brockian.GraphAcyclic

