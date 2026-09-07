import Brockian.WeylPlancherelScaffold
import Brockian.WeylHarmonicOscillator
import Brockian.FreeLaplacianPlancherel

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Brockian.Weyl.MaximalMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def maximalMulDomain (g : α → ℂ) :
    Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (g * (f : α → ℂ)) 2 μ}
  zero_mem' := by
    refine (MemLp.zero' : MemLp (0 : α → ℂ) 2 μ).ae_eq ?_
    filter_upwards [Lp.coeFn_zero (α := α) (E := ℂ) (p := 2) (μ := μ)] with x hx
    simp only [Pi.mul_apply]
    rw [hx]
    simp
  add_mem' := by
    intro f h hf hh
    refine (hf.add hh).ae_eq ?_
    filter_upwards [Lp.coeFn_add f h] with x hx
    simp only [Pi.add_apply, Pi.mul_apply] at hx ⊢
    rw [hx]
    ring
  smul_mem' := by
    intro c f hf
    refine (hf.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    ring

noncomputable def maximalMulValue (g : α → ℂ)
    (f : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ :=
  (show MemLp (g * ((f : Lp ℂ 2 μ) : α → ℂ)) 2 μ from f.2).toLp
    (g * ((f : Lp ℂ 2 μ) : α → ℂ))

theorem coeFn_maximalMulValue (g : α → ℂ)
    (f : maximalMulDomain (μ := μ) g) :
    (maximalMulValue g f : α → ℂ) =ᵐ[μ]
      g * ((f : Lp ℂ 2 μ) : α → ℂ) :=
  MemLp.coeFn_toLp _

noncomputable def maximalMul (g : α → ℂ) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalMulDomain (μ := μ) g
  toFun :=
    { toFun := maximalMulValue g
      map_add' := by
        intro f h
        apply Lp.ext
        have ein : (((f + h : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
            ((f : Lp ℂ 2 μ) : α → ℂ) + ((h : Lp ℂ 2 μ) : α → ℂ) := by
          simpa using Lp.coeFn_add (f : Lp ℂ 2 μ) (h : Lp ℂ 2 μ)
        filter_upwards [coeFn_maximalMulValue g (f + h), coeFn_maximalMulValue g f,
          coeFn_maximalMulValue g h,
          Lp.coeFn_add (maximalMulValue g f) (maximalMulValue g h), ein]
            with x e0 e1 e2 esum einx
        simp only [Pi.add_apply, Pi.mul_apply] at e0 e1 e2 esum einx ⊢
        rw [e0, einx, esum, e1, e2]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        have ein : (((c • f : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
            c • ((f : Lp ℂ 2 μ) : α → ℂ) := by
          simpa using Lp.coeFn_smul c (f : Lp ℂ 2 μ)
        filter_upwards [coeFn_maximalMulValue g (c • f), coeFn_maximalMulValue g f,
          Lp.coeFn_smul c (maximalMulValue g f), ein] with x e0 e1 esr einx
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, RingHom.id_apply]
          at e0 e1 esr einx ⊢
        rw [e0, einx, esr, e1]
        ring }

@[simp] theorem maximalMul_domain (g : α → ℂ) :
    (maximalMul (μ := μ) g).domain = maximalMulDomain (μ := μ) g := rfl

theorem coeFn_maximalMul (g : α → ℂ)
    (f : (maximalMul (μ := μ) g).domain) :
    (maximalMul (μ := μ) g f : α → ℂ) =ᵐ[μ]
      g * ((f : Lp ℂ 2 μ) : α → ℂ) :=
  coeFn_maximalMulValue g f

open Brockian.SpectralGate1
open Brockian.Weyl.Cayley

noncomputable def shiftPreimage (r : α → ℂ) (hr : MemLp r ∞ μ)
    (h : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  mulLpFun r hr h

theorem coeFn_shiftPreimage (r : α → ℂ) (hr : MemLp r ∞ μ)
    (h : Lp ℂ 2 μ) :
    (shiftPreimage r hr h : α → ℂ) =ᵐ[μ] r * (h : α → ℂ) := by
  simpa only [shiftPreimage, Pi.smul_apply, smul_eq_mul] using coeFn_mulLpFun r hr h

theorem shiftPreimage_mem_domain (g r : α → ℂ) (z : ℂ)
    (hr : MemLp r ∞ μ) (hinv : ∀ x, (g x - z) * r x = 1)
    (h : Lp ℂ 2 μ) :
    shiftPreimage r hr h ∈ maximalMulDomain (μ := μ) g := by
  let v := shiftPreimage r hr h
  have hmem : MemLp ((h : α → ℂ) + z • (v : α → ℂ)) 2 μ :=
    (Lp.memLp h).add ((Lp.memLp v).const_smul z)
  refine hmem.ae_eq ?_
  filter_upwards [coeFn_shiftPreimage r hr h] with x hv
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hv ⊢
  rw [hv]
  calc
    h x + z * (r x * h x) = ((g x - z) * r x) * h x + z * (r x * h x) := by
      rw [hinv x, one_mul]
    _ = g x * (r x * h x) := by ring

theorem exists_maximalMul_shift_preimage (g r : α → ℂ) (z : ℂ)
    (hr : MemLp r ∞ μ) (hinv : ∀ x, (g x - z) * r x = 1)
    (h : Lp ℂ 2 μ) :
    ∃ v : (maximalMul (μ := μ) g).domain,
      maximalMul (μ := μ) g v - z • (v : Lp ℂ 2 μ) = h := by
  let v : Lp ℂ 2 μ := shiftPreimage r hr h
  have hvdom : v ∈ maximalMulDomain (μ := μ) g :=
    shiftPreimage_mem_domain g r z hr hinv h
  let vd : (maximalMul (μ := μ) g).domain := ⟨v, hvdom⟩
  refine ⟨vd, ?_⟩
  apply Lp.ext
  filter_upwards [coeFn_maximalMul g vd, coeFn_shiftPreimage r hr h,
    Lp.coeFn_sub (maximalMul (μ := μ) g vd) (z • v), Lp.coeFn_smul z v]
      with x hm hv hsub hsmul
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hm hv hsub hsmul ⊢
  rw [hsub, hm, hsmul, hv]
  calc
    g x * (r x * h x) - z * (r x * h x) = ((g x - z) * r x) * h x := by ring
    _ = h x := by rw [hinv x, one_mul]

theorem rangeSMulSub_maximalMul_eq_top (g r : α → ℂ) (z : ℂ)
    (hr : MemLp r ∞ μ) (hinv : ∀ x, (g x - z) * r x = 1) :
    rangeSMulSub (maximalMul (μ := μ) g) z = ⊤ := by
  ext h
  simp only [Submodule.mem_top, iff_true]
  exact mem_rangeSMulSub.mpr (exists_maximalMul_shift_preimage g r z hr hinv h)

namespace Quadratic

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

def quadratic : ℝ → ℂ := fun x => Complex.ofReal (x ^ 2)

noncomputable def quadraticResolventMultiplier (z : ℂ) : ℝ → ℂ :=
  fun x => (quadratic x - z)⁻¹

theorem quadratic_sub_ne_zero {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    quadratic x - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [quadratic, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
  exact hz (neg_eq_zero.mp hi)

theorem continuous_quadraticResolventMultiplier {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (quadraticResolventMultiplier z) := by
  apply Continuous.inv₀
  · unfold quadratic
    fun_prop
  · exact quadratic_sub_ne_zero hz

theorem norm_quadraticResolventMultiplier_le {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    ‖quadraticResolventMultiplier z x‖ ≤ |z.im|⁻¹ := by
  rw [quadraticResolventMultiplier, norm_inv]
  have hqim : (quadratic x).im = 0 := by
    change (Complex.ofReal (x ^ 2)).im = 0
    exact Complex.ofReal_im _
  have hnorm : |z.im| ≤ ‖quadratic x - z‖ := by
    calc
      |z.im| = |(quadratic x - z).im| := by
        rw [Complex.sub_im, hqim, zero_sub, abs_neg]
      _ ≤ ‖quadratic x - z‖ := Complex.abs_im_le_norm _
  exact (inv_le_inv₀ (norm_pos_iff.mpr (quadratic_sub_ne_zero hz x))
    (abs_pos.mpr hz)).2 hnorm

theorem quadraticResolventMultiplier_memLp_top {z : ℂ} (hz : z.im ≠ 0) :
    MemLp (quadraticResolventMultiplier z) ∞ (volume : Measure ℝ) := by
  apply memLp_top_of_bound (continuous_quadraticResolventMultiplier hz).aestronglyMeasurable
    |z.im|⁻¹
  exact Filter.Eventually.of_forall (norm_quadraticResolventMultiplier_le hz)

theorem quadratic_resolvent_inverse {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    (quadratic x - z) * quadraticResolventMultiplier z x = 1 := by
  exact mul_inv_cancel₀ (quadratic_sub_ne_zero hz x)

theorem quadraticMaximal_rangeSMulSub_eq_top {z : ℂ} (hz : z.im ≠ 0) :
    rangeSMulSub (maximalMul (μ := (volume : Measure ℝ)) quadratic) z = ⊤ :=
  rangeSMulSub_maximalMul_eq_top quadratic (quadraticResolventMultiplier z) z
    (quadraticResolventMultiplier_memLp_top hz) (quadratic_resolvent_inverse hz)

theorem schwartzToL2_mem_maximalMulDomain (f : SchwartzMap ℝ ℂ) :
    schwartzToL2 f ∈ maximalMulDomain (μ := (volume : Measure ℝ)) quadratic := by
  change MemLp (quadratic * (schwartzToL2 f : ℝ → ℂ)) 2 volume
  have hq : MemLp (quadraticMulSchwartz f : ℝ → ℂ) 2 volume :=
    (quadraticMulSchwartz f).memLp 2 volume
  refine hq.ae_eq ?_
  filter_upwards [coeFn_schwartzToL2 f] with x hx
  simp only [Pi.mul_apply, quadraticMulSchwartz_apply, quadratic]
  rw [hx]
  norm_num

theorem quadraticMaximal_dense :
    Dense ((maximalMul (μ := (volume : Measure ℝ)) quadratic).domain : Set L2R) := by
  apply harmonicOscillatorPMap_dense.mono
  intro u hu
  rw [harmonicOscillatorPMap_domain] at hu
  obtain ⟨f, rfl⟩ := hu
  exact schwartzToL2_mem_maximalMulDomain f

theorem quadraticMaximal_isSymmetric :
    IsSymmetric (maximalMul (μ := (volume : Measure ℝ)) quadratic) := by
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coeFn_maximalMul quadratic f, coeFn_maximalMul quadratic h]
    with x ef eh
  simp only [ef, eh, Pi.mul_apply, quadratic]
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem quadraticMaximal_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (maximalMul (μ := (volume : Measure ℝ)) quadratic) := by
  rw [Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff quadraticMaximal_dense]
  constructor
  · rw [rangeAddI]
    have htop := quadraticMaximal_rangeSMulSub_eq_top (z := -Complex.I) (by norm_num)
    rw [htop]
    exact dense_univ
  · rw [rangeSubI]
    have htop := quadraticMaximal_rangeSMulSub_eq_top (z := Complex.I) (by norm_num)
    rw [htop]
    exact dense_univ

end Quadratic

namespace Plancherel

open Brockian.Weyl.Operator
open Brockian.Weyl.FreeLaplacian2
open Brockian.FreeLaplacianPlancherel

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

noncomputable def conjugateDomainEmbedding (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) : T.domain →ₗ[ℂ] K :=
  U.toLinearMap.comp T.domain.subtype

theorem conjugateDomainEmbedding_injective (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) : Function.Injective (conjugateDomainEmbedding U T) := by
  intro x y hxy
  apply Subtype.ext
  exact U.injective hxy

noncomputable def conjugateDomainEquiv (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) :
    T.domain ≃ₗ[ℂ] LinearMap.range (conjugateDomainEmbedding U T) :=
  LinearEquiv.ofInjective (conjugateDomainEmbedding U T)
    (conjugateDomainEmbedding_injective U T)

noncomputable def conjugatePMap (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) : K →ₗ.[ℂ] K where
  domain := LinearMap.range (conjugateDomainEmbedding U T)
  toFun := (U.toLinearMap.comp T.toFun).comp
    (conjugateDomainEquiv U T).symm.toLinearMap

@[simp] theorem conjugatePMap_domain (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) :
    (conjugatePMap U T).domain = T.domain.map U.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem conjugatePMap_apply (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (x : T.domain) :
    conjugatePMap U T (conjugateDomainEquiv U T x) = U (T x) := by
  simp [conjugatePMap, conjugateDomainEquiv]

theorem conjugatePMap_essentiallySelfAdjoint (U : H ≃ₗᵢ[ℂ] K)
    {T : H →ₗ.[ℂ] H} [CompleteSpace H] [CompleteSpace K]
    (hd : Dense (T.domain : Set H)) (hT : EssentiallySelfAdjoint T) :
    EssentiallySelfAdjoint (conjugatePMap U T) := by
  apply (essentiallySelfAdjoint_transfer U hd (conjugatePMap_domain U T) ?_).mpr hT
  intro y x hy
  have hy' : y = conjugateDomainEquiv U T x := Subtype.ext hy
  rw [hy', conjugatePMap_apply]

/-- The free Laplacian defined spectrally by Fourier conjugation of multiplication by `ξ²`.
The identification with `-f''` on the Schwartz core is a separate theorem. -/
noncomputable def fourierDefinedFreeLaplacian :
    Quadratic.L2R →ₗ.[ℂ] Quadratic.L2R :=
  conjugatePMap fourierL2
    (maximalMul (μ := (volume : Measure ℝ)) Quadratic.quadratic)

theorem fourierDefinedFreeLaplacian_essentiallySelfAdjoint :
    EssentiallySelfAdjoint fourierDefinedFreeLaplacian :=
  conjugatePMap_essentiallySelfAdjoint fourierL2
    Quadratic.quadraticMaximal_dense Quadratic.quadraticMaximal_essentiallySelfAdjoint

end Plancherel

end Brockian.Weyl.MaximalMultiplication
