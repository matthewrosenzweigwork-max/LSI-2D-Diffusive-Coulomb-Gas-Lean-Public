import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeCore

/-! Actual factor projections and isometric gradients of smooth cylinders.
These statements supply both upper-bound tests for optimal tensorization. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open PeriodicAttractiveLogGas
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterProjection (e : CoulombCenterRotation n) :
    CoulombConfig (n + 1) →L[ℝ] ℂ :=
  (coulombCoordinate 0).comp e.toContinuousLinearEquiv.toContinuousLinearMap

def coulombCenterRelativeProjection (e : CoulombCenterRotation n) :
    CoulombConfig (n + 1) →L[ℝ] CoulombConfig n :=
  (coulombCenterRelativeInjection n).toContinuousLinearMap.adjoint.comp
    e.toContinuousLinearEquiv.toContinuousLinearMap

theorem coulombCenterProjection_apply (e : CoulombCenterRotation n)
    (z : CoulombConfig (n + 1)) : coulombCenterProjection e z = e z 0 := rfl

theorem coulombCenterRelativeProjection_apply (e : CoulombCenterRotation n)
    (z : CoulombConfig (n + 1)) : coulombCenterRelativeProjection e z = coulombTail (e z) := by
  apply ext_inner_left ℝ
  intro v
  change inner ℝ v ((coulombCenterRelativeInjection n).toContinuousLinearMap.adjoint (e z)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (coulombCenterRelativeInjection n v) (e z) = inner ℝ v (coulombTail (e z))
  have h := coulombCenter_relative_inner (e z) v
  simpa only [real_inner_comm] using h

theorem coulombCenterProjection_eq_chart (e : CoulombCenterRotation n)
    (z : CoulombConfig (n + 1)) : coulombCenterProjection e z = (coulombCenterChart e z).1 := rfl

theorem coulombCenterRelativeProjection_eq_chart (e : CoulombCenterRotation n)
    (z : CoulombConfig (n + 1)) :
    coulombCenterRelativeProjection e z = (coulombCenterChart e z).2 := by
  rw [coulombCenterRelativeProjection_apply]
  ext j
  rfl

theorem coulombCenterProjection_measurePreserving (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    MeasurePreserving (coulombCenterProjection e) (coulombMeasure (n + 1) β)
      (coulombCenterGaussian β) := by
  refine ⟨(coulombCenterProjection e).measurable, ?_⟩
  have h : (coulombCenterProjection e : CoulombConfig (n + 1) → ℂ) =
      fun z => (coulombCenterChart e z).1 := funext (coulombCenterProjection_eq_chart e)
  rw [h]
  exact coulombCenter_gaussian_marginal e he hβ

theorem coulombCenterRelativeProjection_measurePreserving (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    MeasurePreserving (coulombCenterRelativeProjection e) (coulombMeasure (n + 1) β)
      (coulombCenterRelativeMeasure e β) := by
  refine ⟨(coulombCenterRelativeProjection e).measurable, ?_⟩
  have h : (coulombCenterRelativeProjection e : CoulombConfig (n + 1) → CoulombConfig n) =
      fun z => (coulombCenterChart e z).2 := funext (coulombCenterRelativeProjection_eq_chart e)
  rw [h]
  exact coulombCenter_relative_marginal e he hβ

/-- Change of variables for a noninjective measure-preserving projection. -/
theorem coulombCenter_projection_integral
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {p : A → B}
    (hp : MeasurePreserving p μ ν) {f : B → ℝ} (hf : Measurable f) :
    (∫ x, f (p x) ∂μ) = ∫ y, f y ∂ν := by
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm

/-- Extended entropy respects a genuine factor projection, including infinity. -/
theorem coulombCenter_projection_entropy
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {p : A → B} (hp : MeasurePreserving p μ ν) {f : B → ℝ} (hf : Measurable f) :
    entropy μ (fun x => f (p x)) = entropy ν f := by
  have hF : Measurable (fun y => ENNReal.ofReal (entropyDensity (f y))) :=
    (continuous_entropyDensity.measurable.comp hf).ennreal_ofReal
  unfold entropy
  dsimp only
  rw [hp.lintegral_comp hF,
    coulombCenter_projection_integral hp hf, probReal_univ, probReal_univ]

theorem coulombCenter_center_cylinder_gradient (e : CoulombCenterRotation n)
    {f : ℂ → ℝ} (z : CoulombConfig (n + 1))
    (hf : DifferentiableAt ℝ f (coulombCenterProjection e z)) :
    gradient (fun w => f (coulombCenterProjection e w)) z =
      e.symm (coulombCoordinateInjection (n + 1) 0 (gradient f (coulombCenterProjection e z))) := by
  have h := hf.hasFDerivAt.comp z (coulombCenterProjection e).hasFDerivAt
  apply (toDual ℝ (CoulombConfig (n + 1))).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ coulombCenterProjection e) z = _
  rw [h.fderiv]
  ext v
  change fderiv ℝ f (coulombCenterProjection e z) (coulombCenterProjection e v) =
    inner ℝ (e.symm (coulombCoordinateInjection (n + 1) 0
      (gradient f (coulombCenterProjection e z)))) v
  rw [← inner_gradient_left]
  change inner ℝ (gradient f (coulombCenterProjection e z)) (e v 0) =
    inner ℝ (e.symm (coulombCoordinateInjection (n + 1) 0
      (gradient f (coulombCenterProjection e z)))) v
  have hi := e.inner_map_map
    (e.symm (coulombCoordinateInjection (n + 1) 0 (gradient f (coulombCenterProjection e z)))) v
  rw [e.apply_symm_apply] at hi
  rw [← hi]
  have hc := coulomb_inner_coordinate_injection 0 (e v) (gradient f (coulombCenterProjection e z))
  simpa only [real_inner_comm] using hc.symm

theorem coulombCenter_relative_cylinder_gradient (e : CoulombCenterRotation n)
    {f : CoulombConfig n → ℝ} (z : CoulombConfig (n + 1))
    (hf : DifferentiableAt ℝ f (coulombCenterRelativeProjection e z)) :
    gradient (fun w => f (coulombCenterRelativeProjection e w)) z =
      e.symm (coulombCenterRelativeInjection n (gradient f (coulombCenterRelativeProjection e z))) := by
  have h := hf.hasFDerivAt.comp z (coulombCenterRelativeProjection e).hasFDerivAt
  apply (toDual ℝ (CoulombConfig (n + 1))).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ coulombCenterRelativeProjection e) z = _
  rw [h.fderiv]
  ext v
  change fderiv ℝ f (coulombCenterRelativeProjection e z) (coulombCenterRelativeProjection e v) =
    inner ℝ (e.symm (coulombCenterRelativeInjection n
      (gradient f (coulombCenterRelativeProjection e z)))) v
  rw [← inner_gradient_left]
  change inner ℝ (gradient f (coulombCenterRelativeProjection e z))
      (coulombCenterRelativeProjection e v) =
    inner ℝ (e.symm (coulombCenterRelativeInjection n
      (gradient f (coulombCenterRelativeProjection e z)))) v
  rw [coulombCenterRelativeProjection_apply e v]
  have hi := e.inner_map_map
    (e.symm (coulombCenterRelativeInjection n (gradient f (coulombCenterRelativeProjection e z)))) v
  rw [e.apply_symm_apply] at hi
  rw [← hi]
  have hr := coulombCenter_relative_inner (e v) (gradient f (coulombCenterRelativeProjection e z))
  simpa only [real_inner_comm] using hr.symm

theorem coulombCenter_center_cylinder_gradient_norm (e : CoulombCenterRotation n)
    {f : ℂ → ℝ} (z : CoulombConfig (n + 1))
    (hf : DifferentiableAt ℝ f (coulombCenterProjection e z)) :
    ‖gradient (fun w => f (coulombCenterProjection e w)) z‖ =
      ‖gradient f (coulombCenterProjection e z)‖ := by
  rw [coulombCenter_center_cylinder_gradient e z hf, e.symm.norm_map,
    coulombCoordinateInjection_norm]

theorem coulombCenter_relative_cylinder_gradient_norm (e : CoulombCenterRotation n)
    {f : CoulombConfig n → ℝ} (z : CoulombConfig (n + 1))
    (hf : DifferentiableAt ℝ f (coulombCenterRelativeProjection e z)) :
    ‖gradient (fun w => f (coulombCenterRelativeProjection e w)) z‖ =
      ‖gradient f (coulombCenterRelativeProjection e z)‖ := by
  rw [coulombCenter_relative_cylinder_gradient e z hf, e.symm.norm_map,
    (coulombCenterRelativeInjection n).norm_map]

end RepulsiveCoulomb
