import LeanResearch.RepulsiveCoulomb.UnitAnnularCutoff

/-! Actual scale-explicit annular cutoffs with compact support strictly inside
{R/2 < norm z < 4R}, equal to one on {R <= norm z <= 2R}. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def annularCutoff (R : ℝ) (z : ℂ) : ℝ := unitAnnularCutoff (R⁻¹ • z)

theorem annularCutoff_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (annularCutoff R) := by
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => R⁻¹ • z) := by fun_prop
  exact unitAnnularCutoff_contDiff.comp hT

theorem annularCutoff_mem_Icc (R : ℝ) (z : ℂ) : annularCutoff R z ∈ Icc (0 : ℝ) 1 :=
  unitAnnularCutoff_mem_Icc _

theorem norm_annular_scale {R : ℝ} (hR : 0 < R) (z : ℂ) : ‖R⁻¹ • z‖ = ‖z‖ / R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), div_eq_mul_inv, mul_comm]

theorem annularCutoff_one {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : R ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * R) : annularCutoff R z = 1 := by
  apply unitAnnularCutoff_one
  rw [norm_annular_scale hR z]
  exact ⟨(le_div_iff₀ hR).mpr (by simpa using hz.1), (div_le_iff₀ hR).mpr hz.2⟩

theorem annularCutoff_tsupport_bounds {R : ℝ} (hR : 0 < R) :
    tsupport (annularCutoff R) ⊆ {z : ℂ | 3 * R / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * R} := by
  apply closure_minimal
  · intro z hz
    change unitAnnularCutoff (R⁻¹ • z) ≠ 0 at hz
    have hb := unitAnnularCutoff_tsupport (subset_closure hz)
    change (3 / 4 : ℝ) ≤ ‖R⁻¹ • z‖ ∧ ‖R⁻¹ • z‖ ≤ 3 at hb
    rw [norm_annular_scale hR z] at hb
    constructor
    · have h := (le_div_iff₀ hR).mp hb.1
      linarith
    · exact (div_le_iff₀ hR).mp hb.2
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

theorem annularCutoff_tsupport_strict {R : ℝ} (hR : 0 < R) :
    tsupport (annularCutoff R) ⊆ {z : ℂ | R / 2 < ‖z‖ ∧ ‖z‖ < 4 * R} := by
  intro z hz
  obtain ⟨hlo, hup⟩ := annularCutoff_tsupport_bounds hR hz
  constructor <;> linarith

theorem annularCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (annularCutoff R) := by
  change IsCompact (tsupport (annularCutoff R))
  apply (isCompact_closedBall (0 : ℂ) (3 * R)).of_isClosed_subset (isClosed_tsupport (annularCutoff R))
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using (annularCutoff_tsupport_bounds hR hz).2

theorem exists_annularCutoff_gradient_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (R : ℝ), 0 < R → ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R := by
  obtain ⟨C, hC, hbound⟩ := unitAnnularCutoff_fderiv_bounded
  refine ⟨C, hC, ?_⟩
  intro R hR z
  let T : ℂ → ℂ := fun x => R⁻¹ • x
  have hT : HasFDerivAt T (R⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_smul R⁻¹
  have h := (unitAnnularCutoff_contDiff.differentiable (by simp) (T z)).hasFDerivAt.comp z hT
  rw [TauCeti.norm_gradient_eq_norm_fderiv]
  change ‖fderiv ℝ (unitAnnularCutoff ∘ T) z‖ ≤ C / R
  rw [h.fderiv]
  calc
    _ ≤ ‖fderiv ℝ unitAnnularCutoff (T z)‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ‖R⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ContinuousLinearMap.norm_id]
      simp [div_eq_mul_inv]

end RepulsiveCoulomb
