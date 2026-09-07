/-
  Closed non-real shifted ranges for closed symmetric LinearPMaps.

  The distinction between an essentially self-adjoint core and its closure matters:
  the core shifts are generally only dense, while the closure shifts are closed.  This
  file proves the closed-operator theorem needed to upgrade the latter to surjectivity.
-/
import Brockian.WeylSelfAdjointExtension

namespace Brockian.Weyl.ClosedRangeClosure

open scoped InnerProductSpace Topology
open Set
open Filter
open Brockian.Weyl.Operator Brockian.Weyl.Cayley

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extending a partial operator can only enlarge any scalar-shifted range. -/
theorem rangeSMulSub_mono {T S : H →ₗ.[ℂ] H} (hTS : T ≤ S) (z : ℂ) :
    rangeSMulSub T z ≤ rangeSMulSub S z := by
  intro u hu
  obtain ⟨v, rfl⟩ := mem_rangeSMulSub.mp hu
  obtain ⟨w, hvw, hTw⟩ := LinearPMap.exists_of_le hTS v
  apply mem_rangeSMulSub.mpr
  refine ⟨w, ?_⟩
  rw [← hTw, ← hvw]

/-- A dense shifted range remains dense after extending the operator. -/
theorem dense_rangeSMulSub_of_le {T S : H →ₗ.[ℂ] H} (hTS : T ≤ S) (z : ℂ)
    (hT : Dense (rangeSMulSub T z : Set H)) :
    Dense (rangeSMulSub S z : Set H) :=
  hT.mono (SetLike.coe_subset_coe.mpr (rangeSMulSub_mono hTS z))

/-- A closed symmetric operator has closed range after every non-real scalar shift.

The proof is the standard graph argument.  The symmetric lower bound makes the
preimages of a convergent range sequence Cauchy.  Closedness of the operator graph
then puts the limit preimage back in the domain. -/
theorem isClosed_rangeSMulSub_of_isClosed_of_isSymmetric
    {T : H →ₗ.[ℂ] H} (hclosed : T.IsClosed) (hT : IsSymmetric T)
    {z : ℂ} (hz : z.im ≠ 0) :
    IsClosed (rangeSMulSub T z : Set H) := by
  apply IsSeqClosed.isClosed
  intro y y₀ hy hy_lim
  choose v hv using fun n ↦ (mem_rangeSMulSub.mp (hy n))
  let x : ℕ → H := fun n ↦ (v n : H)
  have him : 0 < |z.im| := abs_pos.mpr hz
  have hx_cauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hy_lim.cauchySeq)
      (|z.im| * ε) (mul_pos him hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hshift :
        T (v m - v n) - z • ((v m - v n : T.domain) : H) = y m - y n := by
      calc
        T (v m - v n) - z • ((v m - v n : T.domain) : H)
            = (T (v m) - z • (v m : H)) - (T (v n) - z • (v n : H)) := by
                change T.toFun (v m - v n) - z • ((v m : H) - (v n : H)) = _
                rw [T.toFun.map_sub, smul_sub]
                exact sub_sub_sub_comm _ _ _ _
        _ = y m - y n := by rw [hv m, hv n]
    have hbound := hT.norm_sub_smul_ge (v m - v n) z
    rw [hshift] at hbound
    rw [dist_eq_norm]
    change ‖((v m : H) - (v n : H))‖ < ε
    have hmul : |z.im| * ‖((v m : H) - (v n : H))‖ < |z.im| * ε :=
      lt_of_le_of_lt hbound (by simpa [dist_eq_norm] using hN m hm n hn)
    by_contra hnot
    have hle : ε ≤ ‖((v m : H) - (v n : H))‖ := le_of_not_gt hnot
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hle him.le)) hmul
  obtain ⟨x₀, hx_lim⟩ := cauchySeq_tendsto_of_complete hx_cauchy
  have hTv (n : ℕ) : T (v n) = y n + z • x n := by
    dsimp [x]
    have := hv n
    apply sub_eq_iff_eq_add.mp
    exact this
  have hzx_lim : Tendsto (fun n ↦ z • x n) atTop (nhds (z • x₀)) :=
    tendsto_const_nhds.smul hx_lim
  have hTv_lim : Tendsto (fun n ↦ T (v n)) atTop (nhds (y₀ + z • x₀)) := by
    convert hy_lim.add hzx_lim using 1
    ext n
    exact hTv n
  have hgraph_mem : ∀ n, (x n, T (v n)) ∈ T.graph := by
    intro n
    simpa [x] using T.mem_graph (v n)
  have hgraph_lim :
      Tendsto (fun n ↦ (x n, T (v n))) atTop (nhds (x₀, y₀ + z • x₀)) :=
    hx_lim.prodMk_nhds hTv_lim
  have hlimit_graph : (x₀, y₀ + z • x₀) ∈ T.graph :=
    hclosed.isSeqClosed hgraph_mem hgraph_lim
  rw [LinearPMap.mem_graph_iff] at hlimit_graph
  obtain ⟨w, hwx, hTw⟩ := hlimit_graph
  apply mem_rangeSMulSub.mpr
  refine ⟨w, ?_⟩
  calc
    T w - z • (w : H) = (y₀ + z • x₀) - z • x₀ := by rw [hTw, hwx]
    _ = y₀ := by abel

/-- The two unit shifts of a closed symmetric operator have closed ranges. -/
theorem isClosed_rangeAddI_and_rangeSubI
    {T : H →ₗ.[ℂ] H} (hclosed : T.IsClosed) (hT : IsSymmetric T) :
    IsClosed (rangeAddI T : Set H) ∧ IsClosed (rangeSubI T : Set H) := by
  constructor
  · show IsClosed (rangeSMulSub T (-Complex.I) : Set H)
    exact isClosed_rangeSMulSub_of_isClosed_of_isSymmetric hclosed hT
      (by rw [Complex.neg_im, Complex.I_im]; exact neg_ne_zero.mpr one_ne_zero)
  · show IsClosed (rangeSMulSub T Complex.I : Set H)
    exact isClosed_rangeSMulSub_of_isClosed_of_isSymmetric hclosed hT
      (by rw [Complex.I_im]; exact one_ne_zero)

end Brockian.Weyl.ClosedRangeClosure
