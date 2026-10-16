import LeanResearch.RepulsiveCoulomb.CoulombRelativeRawIntegral

/-! Normalized relative conditional and actual center/frozen marginal. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def coulombRelativeMarginalDensity (N : ℕ) (β : ℝ) (p : ℂ × CoulombConfig N) : ℝ≥0∞ :=
  (coulombPartition (N + 2) β)⁻¹ * ENNReal.ofReal (coulombRelativeFrozenWeight N β p) *
    pointPartition β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2)

def coulombRelativeMarginal (N : ℕ) (β : ℝ) : Measure (ℂ × CoulombConfig N) :=
  volume.withDensity (coulombRelativeMarginalDensity N β)

theorem coulombRelativeMarginalDensity_measurable {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) :
    Measurable (coulombRelativeMarginalDensity N β) := by
  have he : (fun p : ℂ × CoulombConfig N =>
      pointPartition β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2)) =
      (fun q : CoulombConfig (N + N + 1) => pointPartition β (coulombRelativeExponents N β) (fun j => q j)) ∘
        coulombRelativeRootConfig (N := N) := by
    funext p
    apply congrArg (pointPartition β (coulombRelativeExponents N β))
    rfl
  have hp : Measurable (fun p : ℂ × CoulombConfig N =>
      pointPartition β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2)) := by
    rw [he]
    exact (pointPartition_measurable_config β (coulombRelativeExponents_nonneg N hβ)).comp
      (coulombRelativeRootConfig_continuous N).measurable
  exact (measurable_const.mul (coulombRelativeFrozenWeight_continuous N hβ).measurable.ennreal_ofReal).mul hp

set_option maxHeartbeats 800000 in
theorem coulomb_relative_tower {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 2) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂coulombMeasure (N + 2) β) =
      ∫⁻ p : ℂ × CoulombConfig N,
        (∫⁻ u : ℂ, F (coulombRelativeInsert p.1 u p.2) ∂coulombRelativeKernel N β hβ p)
          ∂coulombRelativeMarginal N β := by
  simp_rw [coulombRelativeKernel_apply]
  let a := coulombRelativeExponents N β
  have ha : ∀ j, 0 ≤ a j := coulombRelativeExponents_nonneg N hβ.le
  have hjoint : Measurable (fun p : (ℂ × CoulombConfig N) × ℂ =>
      F (coulombRelativeInsert p.1.1 p.2 p.1.2)) :=
    hF.comp (coulombRelativeInsert_joint_measurable N)
  have hcond := hjoint.lintegral_kernel_prod_right' (κ := coulombRelativeKernel N β hβ)
  simp only [coulombRelativeKernel_apply] at hcond
  rw [coulombMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume (coulombWeight_continuous hβ.le).measurable.ennreal_ofReal hF]
  change (coulombPartition (N + 2) β)⁻¹ *
      (∫⁻ z, ENNReal.ofReal (coulombWeight β z) * F z) = _
  rw [coulomb_raw_relative_lintegral hβ.le hF, coulombRelativeMarginal,
    lintegral_withDensity_eq_lintegral_mul volume (coulombRelativeMarginalDensity_measurable hβ.le) hcond]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (coulombPartition_pos (N := N + 2) hβ).ne')]
  apply lintegral_congr
  intro p
  have hslice : Measurable (fun u : ℂ => F (coulombRelativeInsert p.1 u p.2)) :=
    hjoint.comp measurable_prodMk_left
  change (coulombPartition (N + 2) β)⁻¹ * (ENNReal.ofReal (coulombRelativeFrozenWeight N β p) *
      ∫⁻ u : ℂ, ENNReal.ofReal (pointWeight β a (coulombRelativeRoots p.1 p.2) u) *
        F (coulombRelativeInsert p.1 u p.2)) =
    coulombRelativeMarginalDensity N β p *
      (∫⁻ u : ℂ, F (coulombRelativeInsert p.1 u p.2) ∂pointMeasure β a (coulombRelativeRoots p.1 p.2))
  rw [pointMeasure_lintegral β a (coulombRelativeRoots p.1 p.2) hslice]
  have hc := ENNReal.mul_inv_cancel (pointPartition_pos β a (coulombRelativeRoots p.1 p.2)).ne'
    (pointPartition_lt_top hβ ha (coulombRelativeRoots p.1 p.2)).ne
  unfold coulombRelativeMarginalDensity
  change _ = ((coulombPartition (N + 2) β)⁻¹ * ENNReal.ofReal (coulombRelativeFrozenWeight N β p) *
    pointPartition β a (coulombRelativeRoots p.1 p.2)) * _
  calc
    _ = ((coulombPartition (N + 2) β)⁻¹ * ENNReal.ofReal (coulombRelativeFrozenWeight N β p)) *
        (pointPartition β a (coulombRelativeRoots p.1 p.2) *
          (pointPartition β a (coulombRelativeRoots p.1 p.2))⁻¹) *
        (∫⁻ u : ℂ, ENNReal.ofReal (pointWeight β a (coulombRelativeRoots p.1 p.2) u) *
          F (coulombRelativeInsert p.1 u p.2)) := by
      rw [hc, mul_one]
      ac_rfl
    _ = _ := by ac_rfl

theorem coulombRelativeMarginal_isProbability {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (coulombRelativeMarginal N β) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have h := coulomb_relative_tower (N := N) hβ (F := fun _ => 1) measurable_const
  have hfiber (p : ℂ × CoulombConfig N) :
      (∫⁻ _u : ℂ, (1 : ℝ≥0∞) ∂coulombRelativeKernel N β hβ p) = 1 := by
    simp only [lintegral_one, measure_univ]
  simp_rw [hfiber] at h
  constructor
  simpa only [lintegral_one, measure_univ] using h.symm

end RepulsiveCoulomb

