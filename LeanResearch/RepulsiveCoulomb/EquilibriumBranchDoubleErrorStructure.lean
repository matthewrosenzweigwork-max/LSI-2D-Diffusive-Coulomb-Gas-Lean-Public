module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleTranslation
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDoubleErrorMoments

@[expose] public section

/-! Joint measurability and exact symmetry of the finite double-error proxy.
The value on the spatial diagonal is proved zero; the equality with g-P^2g
is still asserted only off that diagonal. These are the kernel hypotheses
needed for an actual centered finite-product correlation estimate. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
namespace RepulsiveCoulomb

theorem equilibriumDoubleCircularError_diagonal {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    equilibriumDoubleCircularError ε x x = 0 := by
  have hsingle : equilibriumCircularError ε (x - x) = 0 := by
    simp only [sub_self, equilibriumCircularError, smul_zero, equilibriumLogPositive,
      equilibriumLogKernel, norm_zero, Real.log_zero, neg_zero, max_self]
  have hs : ∀ᵐ z ∂equilibriumCircleMeasure x ε, z ∈ sphere x ε :=
    mem_ae_iff.mpr (equilibriumCircleMeasure_supported x hε.le)
  have he : (fun z : ℂ => equilibriumCircularError ε (z - x)) =ᵐ[equilibriumCircleMeasure x ε] 0 := by
    filter_upwards [hs] with z hz
    have hn : ‖z - x‖ = ε := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz
    exact equilibriumCircularError_eq_zero_of_le_norm hε hn.ge
  unfold equilibriumDoubleCircularError equilibriumAveragedCircularError
  rw [hsingle, integral_congr_ae he]
  simp only [Pi.zero_apply, integral_zero, zero_add]

/-- A measurable finite representative with an explicitly separated diagonal. -/
theorem equilibriumDoubleCircularError_eq_piecewise {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumDoubleCircularError ε x y = if x = y then 0 else
      equilibriumLogKernel (x - y) - equilibriumDoubleCircularKernel ε x y := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl, equilibriumDoubleCircularError_diagonal hε]
  · rw [if_neg hxy, equilibriumDoubleCircularError_eq_sub hε hxy]

theorem equilibriumDoubleCircularError_joint_measurable {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun p : ℂ × ℂ => equilibriumDoubleCircularError ε p.1 p.2) := by
  simp only [equilibriumDoubleCircularError_eq_piecewise hε]
  exact measurable_const.ite (isClosed_eq continuous_fst continuous_snd).measurableSet
    ((equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).sub
      (equilibriumDoubleCircularKernel_joint_measurable hε))

theorem equilibriumDoubleCircularError_symm {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumDoubleCircularError ε x y = equilibriumDoubleCircularError ε y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · rw [equilibriumDoubleCircularError_eq_sub hε hxy,
      equilibriumDoubleCircularError_eq_sub hε (fun hyx => hxy hyx.symm),
      equilibriumDoubleCircularKernel_symm hε x y]
    simp only [equilibriumLogKernel, norm_sub_rev]

end RepulsiveCoulomb
