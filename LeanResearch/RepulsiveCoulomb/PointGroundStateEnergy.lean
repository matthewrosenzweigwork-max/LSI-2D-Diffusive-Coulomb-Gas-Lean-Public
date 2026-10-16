module

public import LeanResearch.RepulsiveCoulomb.PointScoreCrossTerm

@[expose] public section

/-! Actual normalized ground-state energy identity, with all terms integrable
on the original puncture-avoiding smooth core. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem testFunction_physical_energy_integrable (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    Integrable (fun x : ℂ => ‖gradient (φ : ℂ → ℝ) x‖ ^ 2) μ := by
  have hc := TauCeti.continuous_gradient_testFunction φ
  have hs := TauCeti.hasCompactSupport_gradient_testFunction φ
  change Continuous (fun x : ℂ => gradient (φ : ℂ → ℝ) x) at hc
  change HasCompactSupport (fun x : ℂ => gradient (φ : ℂ → ℝ) x) at hs
  have hs2 : HasCompactSupport (fun x : ℂ => ‖gradient (φ : ℂ → ℝ) x‖ ^ 2) :=
    hs.comp_left (g := fun v : ℂ => ‖v‖ ^ 2) (by simp)
  exact (hc.norm.pow 2).integrable_of_hasCompactSupport hs2

theorem pointMeasure_integral_density_of_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (_hf : Integrable f (pointMeasure γ a y)) :
    (∫ x, f x ∂pointMeasure γ a y) = ∫ x : ℂ, pointDensity γ a y x * f x := by
  rw [pointMeasure_eq_withDensity hγ ha y,
    integral_withDensity_eq_integral_toReal_smul
      (pointDensity_continuous γ ha y).measurable.ennreal_ofReal (by simp)]
  congr 1
  funext z
  simp only [ENNReal.toReal_ofReal (pointDensity_nonneg hγ ha y z), smul_eq_mul]

theorem pointGroundState_energy_density {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    pointDensity γ a y z * ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 =
      ‖gradient (pointGroundStateCore hγ ha y φ : ℂ → ℝ) z‖ ^ 2 +
      (1 / 4 : ℝ) * (‖pointScore γ a y z‖ ^ 2 * (pointGroundStateCore hγ ha y φ z) ^ 2) +
      pointGroundStateCore hγ ha y φ z *
        inner ℝ (gradient (pointGroundStateCore hγ ha y φ : ℂ → ℝ) z) (pointScore γ a y z) := by
  have h := congrArg (fun v : ℂ => ‖v‖ ^ 2) (pointGroundStateCore_gradient_identity hγ ha y φ z)
  rw [norm_add_sq_real] at h
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (pointDensity_nonneg hγ ha y z), inner_smul_right, smul_eq_mul, div_pow] at h
  nlinarith only [h]

theorem pointGroundState_energy_identity {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) =
      (∫ x : ℂ, ‖gradient (pointGroundStateCore hγ ha y φ : ℂ → ℝ) x‖ ^ 2) +
      (1 / 4 : ℝ) * (∫ x : ℂ, ‖pointScore γ a y x‖ ^ 2 * (pointGroundStateCore hγ ha y φ x) ^ 2) -
      γ * (∫ x : ℂ, (pointGroundStateCore hγ ha y φ x) ^ 2) := by
  let _ := pointMeasure_isProbability hγ ha y
  let ψ := pointGroundStateCore hγ ha y φ
  have hw := testFunction_physical_energy_integrable (pointDomain a y) φ (pointMeasure γ a y)
  have hE := testFunction_physical_energy_integrable (pointDomain a y) ψ volume
  have hS := pointCore_score_energy_integrable γ ha y ψ
  have hX := pointCore_score_cross_integrable γ ha y ψ
  have hpoint := pointGroundState_energy_density hγ ha y φ
  calc
    _ = ∫ x : ℂ, pointDensity γ a y x * ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 :=
      pointMeasure_integral_density_of_integrable hγ ha y _ hw
    _ = ∫ x : ℂ, (‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 +
        (1 / 4 : ℝ) * (‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2)) +
        ψ x * inner ℝ (gradient (ψ : ℂ → ℝ) x) (pointScore γ a y x) :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_add (by convert! hE.add (hS.const_mul (1 / 4 : ℝ)) using 1) hX,
        integral_add hE (hS.const_mul (1 / 4 : ℝ)), integral_const_mul,
        pointCore_score_cross_integral γ ha y ψ]
      ring

end RepulsiveCoulomb
