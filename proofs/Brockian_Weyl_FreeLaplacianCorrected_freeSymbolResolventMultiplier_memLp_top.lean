import Brockian.WeylMaximalMultiplication
import Brockian.WeylSchrodingerGate1Final

open MeasureTheory
open scoped InnerProductSpace

namespace Brockian.Weyl.FreeLaplacianCorrected

open Brockian.Weyl.Operator
open Brockian.Weyl.Cayley
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Final
open Brockian.Weyl.MaximalMultiplication
open Brockian.Weyl.MaximalMultiplication.Plancherel

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The physical Fourier symbol for `-d^2/dx^2` under Mathlib's
`exp(-2*pi*i*x*xi)` convention. -/
noncomputable def freeSymbol (xi : Real) : Complex :=
  Complex.ofReal (4 * Real.pi ^ 2 * xi ^ 2)

noncomputable def freeSymbolResolventMultiplier (z : Complex) : Real -> Complex :=
  fun xi => (freeSymbol xi - z)⁻¹

theorem freeSymbol_sub_ne_zero {z : Complex} (hz : z.im ≠ 0) (xi : Real) :
    freeSymbol xi - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [freeSymbol, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
  exact hz (neg_eq_zero.mp hi)

theorem continuous_freeSymbolResolventMultiplier {z : Complex} (hz : z.im ≠ 0) :
    Continuous (freeSymbolResolventMultiplier z) := by
  apply Continuous.inv₀
  · unfold freeSymbol
    fun_prop
  · exact freeSymbol_sub_ne_zero hz

theorem norm_freeSymbolResolventMultiplier_le {z : Complex} (hz : z.im ≠ 0)
    (xi : Real) :
    ‖freeSymbolResolventMultiplier z xi‖ ≤ |z.im|⁻¹ := by
  rw [freeSymbolResolventMultiplier, norm_inv]
  have hsim : (freeSymbol xi).im = 0 := Complex.ofReal_im _
  have hnorm : |z.im| ≤ ‖freeSymbol xi - z‖ := by
    calc
      |z.im| = |(freeSymbol xi - z).im| := by
        rw [Complex.sub_im, hsim, zero_sub, abs_neg]
      _ ≤ ‖freeSymbol xi - z‖ := Complex.abs_im_le_norm _
  exact (inv_le_inv₀ (norm_pos_iff.mpr (freeSymbol_sub_ne_zero hz xi))
    (abs_pos.mpr hz)).2 hnorm

theorem freeSymbolResolventMultiplier_memLp_top {z : Complex} (hz : z.im ≠ 0) :
    MemLp (freeSymbolResolventMultiplier z) ∞ (volume : Measure Real) := by
  apply memLp_top_of_bound
    (continuous_freeSymbolResolventMultiplier hz).aestronglyMeasurable |z.im|⁻¹
  exact Filter.Eventually.of_forall (norm_freeSymbolResolventMultiplier_le hz)

theorem freeSymbol_resolvent_inverse {z : Complex} (hz : z.im ≠ 0) (xi : Real) :
    (freeSymbol xi - z) * freeSymbolResolventMultiplier z xi = 1 := by
  exact mul_inv_cancel₀ (freeSymbol_sub_ne_zero hz xi)

/-- Maximal multiplication by the correctly normalized free symbol. -/
noncomputable def freeSymbolMaximal : L2R →ₗ.[Complex] L2R :=
  maximalMul (μ := (volume : Measure Real)) freeSymbol

theorem freeSymbolMaximal_rangeSMulSub_eq_top {z : Complex} (hz : z.im ≠ 0) :
    rangeSMulSub freeSymbolMaximal z = ⊤ :=
  rangeSMulSub_maximalMul_eq_top freeSymbol (freeSymbolResolventMultiplier z) z
    (freeSymbolResolventMultiplier_memLp_top hz) (freeSymbol_resolvent_inverse hz)

noncomputable def freeSymbolMulSchwartz :
    SchwartzMap Real Complex →L[Complex] SchwartzMap Real Complex :=
  SchwartzMap.smulLeftCLM Complex
    (fun xi : Real => (4 * Real.pi ^ 2 * xi ^ 2 : Complex))

@[simp] theorem freeSymbolMulSchwartz_apply (f : SchwartzMap Real Complex) (xi : Real) :
    freeSymbolMulSchwartz f xi = freeSymbol xi * f xi := by
  rw [freeSymbolMulSchwartz]
  simpa [freeSymbol, Complex.ofReal_mul, Complex.ofReal_pow, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply
      (show (fun xi : Real => (4 * Real.pi ^ 2 * xi ^ 2 : Complex)).HasTemperateGrowth by
        fun_prop) f xi

theorem schwartzToL2_mem_freeSymbolMaximal_domain (f : SchwartzMap Real Complex) :
    schwartzToL2 f ∈ freeSymbolMaximal.domain := by
  change MemLp (freeSymbol * (schwartzToL2 f : Real -> Complex)) 2 volume
  have hm : MemLp (freeSymbolMulSchwartz f : Real -> Complex) 2 volume :=
    (freeSymbolMulSchwartz f).memLp 2 volume
  refine hm.ae_eq ?_
  filter_upwards [coeFn_schwartzToL2 f] with xi hxi
  simp only [Pi.mul_apply, freeSymbolMulSchwartz_apply]
  rw [hxi]

theorem freeSymbolMaximal_dense :
    Dense (freeSymbolMaximal.domain : Set L2R) := by
  apply freeSchrodingerPMap_dense.mono
  intro u hu
  rw [freeSchrodingerPMap_domain] at hu
  obtain ⟨f, rfl⟩ := hu
  exact schwartzToL2_mem_freeSymbolMaximal_domain f

theorem freeSymbolMaximal_isSymmetric : IsSymmetric freeSymbolMaximal := by
  change IsSymmetric (maximalMul (μ := (volume : Measure Real)) freeSymbol)
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coeFn_maximalMul freeSymbol f, coeFn_maximalMul freeSymbol g]
      with xi hf hg
  simp only [hf, hg, Pi.mul_apply, freeSymbol]
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem freeSymbolMaximal_essentiallySelfAdjoint :
    EssentiallySelfAdjoint freeSymbolMaximal := by
  rw [Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff freeSymbolMaximal_dense]
  constructor
  · rw [rangeAddI]
    rw [freeSymbolMaximal_rangeSMulSub_eq_top (z := -Complex.I) (by norm_num)]
    exact dense_univ
  · rw [rangeSubI]
    rw [freeSymbolMaximal_rangeSMulSub_eq_top (z := Complex.I) (by norm_num)]
    exact dense_univ

/-- The normalized spectral free Laplacian `F^{-1} M_{4*pi^2*xi^2} F`. -/
noncomputable def spectralFreeLaplacian : L2R →ₗ.[Complex] L2R :=
  conjugatePMap Brockian.FreeLaplacianPlancherel.fourierL2.symm freeSymbolMaximal

theorem spectralFreeLaplacian_essentiallySelfAdjoint :
    EssentiallySelfAdjoint spectralFreeLaplacian :=
  conjugatePMap_essentiallySelfAdjoint
    Brockian.FreeLaplacianPlancherel.fourierL2.symm
    freeSymbolMaximal_dense freeSymbolMaximal_essentiallySelfAdjoint

end Brockian.Weyl.FreeLaplacianCorrected
