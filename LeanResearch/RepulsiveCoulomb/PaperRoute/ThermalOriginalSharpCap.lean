import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalSmoothEL
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalLaplacianSharpCap

/-! The sharp physical density cap for the same smooth EL representative
of a NEW canonical minimizer. The actual weak-Poisson identity and NEW
smoothness feed pointwise Poisson and the Laplacian-at-maximum argument. -/
noncomputable section
open MeasureTheory Real Set Metric TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

theorem thermalCanonical_minimizer_exists_capped_smooth_EL_density {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
      (∀ x, ρ x ≤ Real.pi⁻¹) ∧
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ) ∧
      Measurable ρ ∧ (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
      Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
      Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) ∧
      equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
      (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
      0 < K ∧ (∀ x, ρ x ≤ K * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) ∧
      (∀ x, Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) μ) ∧
      (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) ∧
      (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) ∧
      ContDiff ℝ 1 ρ ∧
      ContDiff ℝ 1 (equilibriumDensityPotential ρ) ∧
      TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) (equilibriumDensityPotential ρ)
        (fderiv ℝ (equilibriumDensityPotential ρ)) ∧
      TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
        (fderiv ℝ (equilibriumDensityPotential ρ)) (thermalWeakHessian ρ) ∧
      (∀ (p : ℝ≥0∞) (S : Set ℂ), IsCompact S →
        MemLp (equilibriumDensityPotential ρ) p (volume.restrict S) ∧
        MemLp (fderiv ℝ (equilibriumDensityPotential ρ)) p (volume.restrict S) ∧
        MemLp (thermalWeakHessian ρ) p (volume.restrict S)) ∧
      (∀ R θ : ℝ≥0, θ ≤ 1 →
        HolderOnWith (thermalNewtonLipschitzConstant M * (2 * R : ℝ≥0)^(1-(θ : ℝ))) θ
          (fderiv ℝ (equilibriumDensityPotential ρ)) (closedBall (0 : ℂ) (R : ℝ))) ∧
      (∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        Integrable (fun x => equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) ∧
        Integrable (fun x => ρ x * φ x) ∧
        (∫ x : ℂ, equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) =
          (-2 * Real.pi) * (∫ x : ℂ, ρ x * φ x)) := by
  obtain ⟨ρ, C, M, K, hρsmooth, hUsmooth, hm, hpos, hM, hbound, hi, hmass, h2, hH, hlaw,
    hEL, hK, htail, hG, hUrad, hrad, hρC1, hUC1, hweakU, hweakDU, hLp, hHolder, hPoisson⟩ :=
    thermalCanonical_minimizer_exists_smooth_EL_density hβ μ hmin
  have hcap := thermal_sharp_cap_of_smooth_bounded_EL hβ hρsmooth hpos hbound
    hi hmass h2 hUsmooth hEL
  exact ⟨ρ, C, M, K, hcap, hρsmooth, hUsmooth, hm, hpos, hM, hbound, hi, hmass, h2, hH, hlaw,
    hEL, hK, htail, hG, hUrad, hrad, hρC1, hUC1, hweakU, hweakDU, hLp, hHolder, hPoisson⟩

/-- Original β>0 yields the sharp capped representative through NEW
attainment, uniqueness/radiality, weak Poisson, smoothness and the genuine
second-order maximum test. Higher-derivative tails remain separate. -/
theorem thermal_exists_capped_smooth_EL_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      equilibriumNonnegativeObjective β μ ≠ ⊤ ∧
      (∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) ∧
      ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
        (∀ x, ρ x ≤ Real.pi⁻¹) ∧
        ContDiff ℝ (⊤ : ℕ∞) ρ ∧
        ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ) ∧
        Measurable ρ ∧ (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
        Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
        Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
        Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) ∧
        equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
        (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
        0 < K ∧ (∀ x, ρ x ≤ K * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) ∧
        (∀ x, Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) μ) ∧
        (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) ∧
        (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) ∧
        ContDiff ℝ 1 ρ ∧
        ContDiff ℝ 1 (equilibriumDensityPotential ρ) ∧
        TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) (equilibriumDensityPotential ρ)
          (fderiv ℝ (equilibriumDensityPotential ρ)) ∧
        TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
          (fderiv ℝ (equilibriumDensityPotential ρ)) (thermalWeakHessian ρ) ∧
        (∀ (p : ℝ≥0∞) (S : Set ℂ), IsCompact S →
          MemLp (equilibriumDensityPotential ρ) p (volume.restrict S) ∧
          MemLp (fderiv ℝ (equilibriumDensityPotential ρ)) p (volume.restrict S) ∧
          MemLp (thermalWeakHessian ρ) p (volume.restrict S)) ∧
        (∀ R θ : ℝ≥0, θ ≤ 1 →
          HolderOnWith (thermalNewtonLipschitzConstant M * (2 * R : ℝ≥0)^(1-(θ : ℝ))) θ
            (fderiv ℝ (equilibriumDensityPotential ρ)) (closedBall (0 : ℂ) (R : ℝ))) ∧
        (∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
          Integrable (fun x => equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) ∧
          Integrable (fun x => ρ x * φ x) ∧
          (∫ x : ℂ, equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) =
            (-2 * Real.pi) * (∫ x : ℂ, ρ x * φ x)) := by
  obtain ⟨μ, _, _, hfinite, hmin⟩ := thermalCanonical_exists_global_minimizer hβ
  exact ⟨μ, hfinite, hmin, thermalCanonical_minimizer_exists_capped_smooth_EL_density hβ μ hmin⟩

end RepulsiveCoulomb.PaperRoute
