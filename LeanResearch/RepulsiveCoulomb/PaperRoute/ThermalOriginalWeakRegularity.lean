import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalBoundedRadialEL
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalBoundedPoisson
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialWeakRegularity

/-! Actual weak Poisson and local second-order regularity for the same bounded
positive EL representative selected from a NEW canonical minimizer. The weak
Hessian and every local Lp/Hölder condition are literal mathematical objects.
The initial C1 regularity of the density genuinely consumes the NEW C1
potential output through the exponential EL formula. -/
noncomputable section
open MeasureTheory Real Set Metric TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- The exponential EL formula transfers a supplied actual C1 potential
result to the positive representative; no old smooth-density producer is used. -/
theorem thermal_EL_contDiff_one_of_potential {β C : ℝ} {ρ : ℂ → ℝ}
    (hρpos : ∀ x, 0 < ρ x)
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (hU : ContDiff ℝ 1 (equilibriumDensityPotential ρ)) : ContDiff ℝ 1 ρ := by
  have h : ContDiff ℝ 1 (fun x : ℂ =>
      Real.exp (-β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)) :=
    ((contDiff_const.mul (((contDiff_norm_sq (𝕜 := ℝ)).div_const 2).add hU)).add contDiff_const).exp
  have he : ρ = fun x : ℂ =>
      Real.exp (-β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) := by
    funext x
    rw [← hEL x, Real.exp_log (hρpos x)]
  rwa [← he] at h

/-- All regularity belongs to the actual chosen representative of this
original canonical minimizer. No Sobolev, Poisson, or reference certificate
is assumed. All Lp assertions are local; no mass-one global energy is claimed. -/
theorem thermalCanonical_minimizer_exists_weak_regular_EL_density {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
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
  obtain ⟨ρ, C, M, K, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρlaw,
    hEL, hK, htail, hpoint, hUrad, hρrad⟩ :=
    thermalCanonical_minimizer_exists_bounded_radial_EL_density hβ μ hmin
  have hρ0 (x : ℂ) : 0 ≤ ρ x := (hρpos x).le
  obtain ⟨hUC1, hweakU, hweakDU, hLp, hHolder⟩ :=
    thermal_radial_weak_regularity hρm hρ0 hρM hρi hρmass hρ2 hUrad
  refine ⟨ρ, C, M, K, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρlaw,
    hEL, hK, htail, hpoint, hUrad, hρrad,
    thermal_EL_contDiff_one_of_potential hρpos hEL hUC1,
    hUC1, hweakU, hweakDU, hLp, hHolder, ?_⟩
  intro φ hφ hφc
  exact boundedDensityPotential_weak_poisson hρm hρ0 hρM hρi hρmass hρ2 hφ hφc

/-- The original input β>0 produces a canonical minimizer with an actual
positive radial C1 EL density, weak Poisson, two weak derivatives of its
potential, and all the compact Lp and local Hölder estimates above. -/
theorem thermal_exists_weak_regular_EL_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      equilibriumNonnegativeObjective β μ ≠ ⊤ ∧
      (∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) ∧
      ∃ (ρ : ℂ → ℝ) (C M K : ℝ),
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
  exact ⟨μ, hfinite, hmin, thermalCanonical_minimizer_exists_weak_regular_EL_density hβ μ hmin⟩

end RepulsiveCoulomb.PaperRoute
