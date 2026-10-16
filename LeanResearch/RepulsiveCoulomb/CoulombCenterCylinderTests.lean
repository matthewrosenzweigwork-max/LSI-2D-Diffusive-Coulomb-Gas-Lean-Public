import LeanResearch.RepulsiveCoulomb.CoulombCenterCylinderGeometry
import LeanResearch.RepulsiveCoulomb.CoulombCenterTensorCore
import LeanResearch.RepulsiveCoulomb.CoulombBoundedSmoothDomain

/-! Genuine factor-cylinder tests inside the original full physical form.
The lifts are constructed by bounded-smooth approximation, with exact entropy
and energy identities. Thus upper bounds come from actual domain elements. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open PeriodicAttractiveLogGas
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombCenter_test_c1_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Ω : Opens E)
    (ψ : TestFunction Ω ℝ ⊤) :
    ∃ B : ℝ, 0 < B ∧ ∀ z, |ψ z| ≤ B ∧ ‖gradient (ψ : E → ℝ) z‖ ≤ B := by
  let f : E → ℝ := fun z => |ψ z| + ‖gradient (ψ : E → ℝ) z‖
  have hc : Continuous f := ψ.continuous.abs.add (TauCeti.continuous_gradient_testFunction ψ).norm
  have hs : HasCompactSupport f := by
    convert! ψ.hasCompactSupport.norm.add (TauCeti.hasCompactSupport_gradient_testFunction ψ).norm using 1 <;>
      simp only [f, Real.norm_eq_abs, Pi.add_apply]
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro z
  have hf0 : 0 ≤ f z := by dsimp [f]; positivity
  have hb : f z ≤ |B| + 1 := by
    by_cases hz : z ∈ tsupport f
    · have h := hB z hz
      rw [Real.norm_eq_abs, abs_of_nonneg hf0] at h
      linarith [le_abs_self B]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      positivity
  dsimp only [f] at hb
  constructor <;> linarith [abs_nonneg (ψ z), norm_nonneg (gradient (ψ : E → ℝ) z)]

theorem coulombCenterGaussianCore_lift (m : ℕ) (e : CoulombCenterRotation (m + 1))
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    ∃ u : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => ψ (coulombCenterProjection e z)) ∧
      coulombFormGradientL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => e.symm (coulombCoordinateInjection (m + 2) 0
          (gradient (ψ : ℂ → ℝ) (coulombCenterProjection e z)))) ∧
      coulombFormEnergy (m + 2) hβ u =
        ∫ c, ‖gradient (ψ : ℂ → ℝ) c‖ ^ 2 ∂coulombCenterGaussian β := by
  let f : CoulombConfig (m + 2) → ℝ := fun z => ψ (coulombCenterProjection e z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := ψ.contDiff.comp (coulombCenterProjection e).contDiff
  obtain ⟨B, hBpos, hB⟩ := coulombCenter_test_c1_bound (⊤ : Opens ℂ) ψ
  have hb : ∀ z, |f z| ≤ B := fun z => (hB (coulombCenterProjection e z)).1
  have hgb : ∀ z, ‖gradient f z‖ ≤ B := by
    intro z
    rw [coulombCenter_center_cylinder_gradient_norm e z (ψ.contDiff.differentiable (by simp) _)]
    exact (hB (coulombCenterProjection e z)).2
  let u := coulombBoundedSmoothForm m hβ f hf B hb hgb
  refine ⟨u, coulombBoundedSmoothForm_value m hβ f hf B hb hgb, ?_, ?_⟩
  · filter_upwards [coulombBoundedSmoothForm_gradient m hβ f hf B hb hgb] with z hz
    rw [hz]
    exact coulombCenter_center_cylinder_gradient e z (ψ.contDiff.differentiable (by simp) _)
  · rw [coulombBoundedSmoothForm_energy]
    have hg (z : CoulombConfig (m + 2)) : ‖gradient f z‖ =
        ‖gradient (ψ : ℂ → ℝ) (coulombCenterProjection e z)‖ :=
      coulombCenter_center_cylinder_gradient_norm e z (ψ.contDiff.differentiable (by simp) _)
    simp_rw [hg]
    exact coulombCenter_projection_integral (coulombCenterProjection_measurePreserving e he hβ)
      ((TauCeti.continuous_gradient_testFunction ψ).norm.pow 2).measurable

theorem coulombCenterRelativeCore_lift (m : ℕ) (e : CoulombCenterRotation (m + 1))
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    ∃ u : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => ψ (coulombCenterRelativeProjection e z)) ∧
      coulombFormGradientL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => e.symm (coulombCenterRelativeInjection (m + 1)
          (gradient (ψ : CoulombConfig (m + 1) → ℝ) (coulombCenterRelativeProjection e z)))) ∧
      coulombFormEnergy (m + 2) hβ u =
        ∫ r, ‖gradient (ψ : CoulombConfig (m + 1) → ℝ) r‖ ^ 2
          ∂coulombCenterRelativeMeasure e β := by
  let f : CoulombConfig (m + 2) → ℝ := fun z => ψ (coulombCenterRelativeProjection e z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := ψ.contDiff.comp (coulombCenterRelativeProjection e).contDiff
  obtain ⟨B, hBpos, hB⟩ := coulombCenter_test_c1_bound (coulombCenterRelativeDomain e) ψ
  have hb : ∀ z, |f z| ≤ B := fun z => (hB (coulombCenterRelativeProjection e z)).1
  have hgb : ∀ z, ‖gradient f z‖ ≤ B := by
    intro z
    rw [coulombCenter_relative_cylinder_gradient_norm e z (ψ.contDiff.differentiable (by simp) _)]
    exact (hB (coulombCenterRelativeProjection e z)).2
  let u := coulombBoundedSmoothForm m hβ f hf B hb hgb
  refine ⟨u, coulombBoundedSmoothForm_value m hβ f hf B hb hgb, ?_, ?_⟩
  · filter_upwards [coulombBoundedSmoothForm_gradient m hβ f hf B hb hgb] with z hz
    rw [hz]
    exact coulombCenter_relative_cylinder_gradient e z (ψ.contDiff.differentiable (by simp) _)
  · rw [coulombBoundedSmoothForm_energy]
    have hg (z : CoulombConfig (m + 2)) : ‖gradient f z‖ =
        ‖gradient (ψ : CoulombConfig (m + 1) → ℝ) (coulombCenterRelativeProjection e z)‖ :=
      coulombCenter_relative_cylinder_gradient_norm e z (ψ.contDiff.differentiable (by simp) _)
    simp_rw [hg]
    exact coulombCenter_projection_integral
      (coulombCenterRelativeProjection_measurePreserving e he hβ)
      ((TauCeti.continuous_gradient_testFunction ψ).norm.pow 2).measurable

/-- Testing the original full form on actual cylinders gives both factor LSIs. -/
theorem coulombCenter_factor_cores_of_admissible (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : poleBranchAdmissibleLSIRate (m + 2) hβ ρ) :
    CoulombCenterGaussianCoreLSI β (2 / ρ) ∧ CoulombCenterRelativeCoreLSI e β (2 / ρ) := by
  letI := coulombMeasure_isProbability (N := m + 2) hβ
  letI := coulombCenterGaussian_isProbability hβ
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  constructor
  · intro ψ
    obtain ⟨u, hv, hg, heq⟩ := coulombCenterGaussianCore_lift m e he hβ ψ
    have h := hρ.2 u
    rw [entropy_congr_ae (hv.mono (fun _ hz => congrArg (fun t : ℝ => t ^ 2) hz)), heq] at h
    rw [coulombCenter_projection_entropy (coulombCenterProjection_measurePreserving e he hβ)
      (ψ.continuous.measurable.pow_const 2)] at h
    exact h
  · intro ψ
    obtain ⟨u, hv, hg, heq⟩ := coulombCenterRelativeCore_lift m e he hβ ψ
    have h := hρ.2 u
    rw [entropy_congr_ae (hv.mono (fun _ hz => congrArg (fun t : ℝ => t ^ 2) hz)), heq] at h
    rw [coulombCenter_projection_entropy (coulombCenterRelativeProjection_measurePreserving e he hβ)
      (ψ.continuous.measurable.pow_const 2)] at h
    exact h

/-- Exact equivalence of the original full-domain rate and its two factors. -/
theorem coulombCenter_admissible_iff_factor_cores (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) :
    poleBranchAdmissibleLSIRate (m + 2) hβ ρ ↔
      CoulombCenterGaussianCoreLSI β (2 / ρ) ∧ CoulombCenterRelativeCoreLSI e β (2 / ρ) :=
  ⟨coulombCenter_factor_cores_of_admissible m e he hβ,
    fun h => coulombCenter_admissible_of_factor_cores e he hβ hρ h.1 h.2⟩

end RepulsiveCoulomb
