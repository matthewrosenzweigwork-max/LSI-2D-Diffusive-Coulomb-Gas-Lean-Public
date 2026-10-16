module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalWeakRegularity
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialELBootstrap

@[expose] public section

/-! Smoothness of the actual positive radial EL representative from a NEW
canonical minimizer, retaining the genuine weak-Poisson/local-second-order
regularity output for the same density. The C1 potential supplied by that
new output is the explicit input to the new radial score bootstrap. -/
noncomputable section
open MeasureTheory Real Set Metric TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

theorem thermalCanonical_minimizer_exists_smooth_EL_density {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
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
  obtain ⟨ρ, C, M, K, hm, hpos, hM, hbound, hi, hmass, h2, hH, hlaw,
    hEL, hK, htail, hG, hUrad, hrad, hρC1, hUC1, hweakU, hweakDU, hLp, hHolder, hPoisson⟩ :=
    thermalCanonical_minimizer_exists_weak_regular_EL_density hβ μ hmin
  obtain ⟨hρsmooth, hUsmooth⟩ := thermal_radial_EL_smooth_of_potential_contDiff_one
    hβ hm hpos hbound hi hmass h2 hrad hEL hUC1
  exact ⟨ρ, C, M, K, hρsmooth, hUsmooth, hm, hpos, hM, hbound, hi, hmass, h2, hH, hlaw,
    hEL, hK, htail, hG, hUrad, hrad, hρC1, hUC1, hweakU, hweakDU, hLp, hHolder, hPoisson⟩

/-- Original-input smooth density and potential, with all preceding genuine
weak-regularity and probability-law conclusions preserved. The sharp cap and
all higher-derivative tails are separate subsequent results. -/
theorem thermal_exists_smooth_EL_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      equilibriumNonnegativeObjective β μ ≠ ⊤ ∧
      (∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) ∧
      ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
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
  exact ⟨μ, hfinite, hmin, thermalCanonical_minimizer_exists_smooth_EL_density hβ μ hmin⟩

end RepulsiveCoulomb.PaperRoute
