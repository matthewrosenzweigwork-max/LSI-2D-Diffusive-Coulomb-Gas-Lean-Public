module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.LogSmoothConvolution
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCrossInteraction
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchInteraction

@[expose] public section

/-! Weak Poisson for the literal potential of
a supplied bounded measurable P2 probability density. It uses the NEW planar
fundamental solution and actual absolute two-variable integrability before
Fubini. No minimizer, radiality, EL, smooth density or PDE certificate is input. -/
noncomputable section
open MeasureTheory Real Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- The NEW fundamental solution translated to any source point. -/
theorem translated_log_fundamental_solution {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (y : ℂ) :
    Integrable (fun x => equilibriumLogKernel (x-y) * Laplacian.laplacian φ x) ∧
      (∫ x : ℂ, equilibriumLogKernel (x-y) * Laplacian.laplacian φ x) =
        (-2 * Real.pi) * φ y := by
  have ht : ContDiff ℝ 2 (fun z : ℂ => φ (y-z)) :=
    hφ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport (fun z : ℂ => φ (y-z)) :=
    hφc.comp_homeomorph (Homeomorph.subLeft y)
  obtain ⟨hti, hte⟩ := log_fundamental_solution ht htc
  have hrow : Integrable (fun x => equilibriumLogKernel (x-y) * Laplacian.laplacian φ x) := by
    apply (hti.comp_sub_left y).congr
    filter_upwards with x
    rw [laplacian_comp_sub_left hφ, sub_sub_self]
    simp only [equilibriumLogKernel, norm_sub_rev]
  have he : (∫ z : ℂ, (-Real.log ‖z‖) * Laplacian.laplacian φ (y-z)) =
      ∫ x : ℂ, equilibriumLogKernel (x-y) * Laplacian.laplacian φ x := by
    calc
      (∫ z : ℂ, (-Real.log ‖z‖) * Laplacian.laplacian φ (y-z)) =
          ∫ z : ℂ, equilibriumLogKernel ((y-z)-y) * Laplacian.laplacian φ (y-z) := by
        apply integral_congr_ae
        filter_upwards with z
        have hz : (y-z)-y = -z := by abel
        simp only [hz, equilibriumLogKernel, norm_neg]
      _ = _ := integral_sub_left_eq_self
        (fun x : ℂ => equilibriumLogKernel (x-y) * Laplacian.laplacian φ x) volume y
  refine ⟨hrow, ?_⟩
  have hte' : (∫ z : ℂ, (-Real.log ‖z‖) * Laplacian.laplacian φ (y-z)) =
      (-2 * Real.pi) * φ y := by
    simpa only [laplacian_comp_sub_left hφ, sub_zero] using hte
  exact he.symm.trans hte'

theorem boundedDensityPotential_kernel_integrable {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρ2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x)) (x : ℂ) :
    Integrable (fun y => equilibriumLogKernel (x-y) * ρ y) :=
  equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi
    (equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2) x

/-- Local integrability of the literal potential, separately from all test
identities, excludes spurious distributional statements about totalized integrals. -/
theorem boundedDensityPotential_locallyIntegrable {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x)) :
    LocallyIntegrable (equilibriumDensityPotential ρ) volume := by
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  let C := M * Real.pi/2 + (∫ y : ℂ, equilibriumLogMoment y * ρ y)
  have hc : Continuous (fun x : ℂ => C+equilibriumLogMoment x) :=
    continuous_const.add equilibriumLogMoment_continuous
  apply locallyIntegrable_iff.mpr
  intro K hK
  apply (hc.continuousOn.integrableOn_compact hK).mono'
    (equilibriumDensityPotential_measurable hρm).aestronglyMeasurable.restrict
  filter_upwards with x
  rw [Real.norm_eq_abs]
  have h := equilibriumDensityPotential_abs_bound hρm hρ0 hρM hρi hρmass hρL x
  dsimp only [C]
  linarith

/-- Actual two-variable absolute integrability for a signed compact test
factor, obtained from the nonnegative outer density |psi|. -/
theorem boundedDensity_kernel_compact_test_integrable {ρ ψ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p : ℂ × ℂ => ψ p.1 *
      (equilibriumLogKernel (p.1-p.2) * ρ p.2)) (volume.prod volume) := by
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have houteri : Integrable (fun x => |ψ x|) :=
    hψ.abs.integrable_of_hasCompactSupport hψc.abs
  have houterL : Integrable (fun x : ℂ => equilibriumLogMoment x * |ψ x|) :=
    (equilibriumLogMoment_continuous.mul hψ.abs).integrable_of_hasCompactSupport hψc.abs.mul_left
  have hcross := equilibriumCrossInteraction_integrable hψ.abs.measurable
    (fun x => abs_nonneg (ψ x)) houteri houterL
    hρm hρ0 hρM hρi hρmass hρL
  apply hcross.norm.mono' (by
    have hg := equilibriumLogKernel_measurable
    fun_prop)
  filter_upwards with p
  simp only [norm_mul, Real.norm_eq_abs, abs_abs, le_refl]

/-- Weak Poisson with the correct physical coefficient and genuine
integrability of both test pairings. -/
theorem boundedDensityPotential_weak_poisson {ρ φ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x))
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) ∧
      Integrable (fun x => ρ x * φ x) ∧
      (∫ x : ℂ, equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) =
        (-2 * Real.pi) * (∫ x : ℂ, ρ x * φ x) := by
  let ψ := Laplacian.laplacian φ
  have hψ : Continuous ψ := continuous_laplacian_of_contDiff_two hφ
  have hψc : HasCompactSupport ψ := hasCompactSupport_laplacian hφ hφc
  let G : ℂ × ℂ → ℝ := fun p => ψ p.1 * (equilibriumLogKernel (p.1-p.2) * ρ p.2)
  have hG : Integrable G (volume.prod volume) :=
    boundedDensity_kernel_compact_test_integrable hρm hρ0 hρM hρi hρmass hρ2 hψ hψc
  have hleft (x : ℂ) : (∫ y : ℂ, G (x,y)) = equilibriumDensityPotential ρ x * ψ x := by
    dsimp only [G]
    rw [integral_const_mul]
    unfold equilibriumDensityPotential
    ring
  have hlefti : Integrable (fun x => equilibriumDensityPotential ρ x * ψ x) :=
    hG.integral_prod_left.congr (Eventually.of_forall hleft)
  have hrighti : Integrable (fun x => ρ x * φ x) := by
    apply (hφ.continuous.integrable_of_hasCompactSupport hφc).bdd_mul
      hρm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
      exact hρM x
  have hright (y : ℂ) : (∫ x : ℂ, G (x,y)) = (-2 * Real.pi) * (ρ y * φ y) := by
    calc
      (∫ x : ℂ, G (x,y)) =
          ρ y * (∫ x : ℂ, equilibriumLogKernel (x-y) * ψ x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [G]
        ring
      _ = ρ y * ((-2 * Real.pi) * φ y) := by
        rw [(translated_log_fundamental_solution hφ hφc y).2]
      _ = _ := by ring
  refine ⟨hlefti, hrighti, ?_⟩
  calc
    (∫ x : ℂ, equilibriumDensityPotential ρ x * ψ x) =
        ∫ x : ℂ, ∫ y : ℂ, G (x,y) :=
      integral_congr_ae (Eventually.of_forall fun x => (hleft x).symm)
    _ = ∫ y : ℂ, ∫ x : ℂ, G (x,y) := integral_integral_swap hG
    _ = ∫ y : ℂ, (-2 * Real.pi) * (ρ y * φ y) :=
      integral_congr_ae (Eventually.of_forall hright)
    _ = (-2 * Real.pi) * (∫ x : ℂ, ρ x * φ x) := integral_const_mul _ _

end RepulsiveCoulomb.PaperRoute
