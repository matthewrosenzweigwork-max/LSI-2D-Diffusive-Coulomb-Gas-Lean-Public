module

public import LeanResearch.RepulsiveCoulomb.PointDilationBranchCore
public import LeanResearch.RepulsiveCoulomb.PlanarWeightedGaussian

@[expose] public section

/-! Exact variance, extended-entropy and physical-energy transport between the
original Gaussian parameter and the unit parameter. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointDilationBranch_entropy_transport
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {e : A → B}
    (he : MeasurePreserving e μ ν) (he' : MeasurableEmbedding e) (f : B → ℝ) :
    entropy μ (fun x => f (e x)) = entropy ν f := by
  unfold entropy
  rw [he.lintegral_comp_emb he' (fun x => ENNReal.ofReal (entropyDensity (f x))),
    he.integral_comp he' f, probReal_univ, probReal_univ]

theorem pointDilationBranch_core_variance {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    variance (pointDilationBranchCore a y (Real.sqrt γ) (Real.sqrt_pos.mpr hγ) φ : ℂ → ℝ)
      (pointMeasure 1 a (fun j => Real.sqrt γ • y j)) =
        variance (φ : ℂ → ℝ) (pointMeasure γ a y) :=
  (pointDilationBranch_from_unit hγ a y).variance_fun_comp φ.continuous.measurable.aemeasurable

theorem pointDilationBranch_core_entropy {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    entropy (pointMeasure 1 a (fun j => Real.sqrt γ • y j))
      (fun x => pointDilationBranchCore a y (Real.sqrt γ) (Real.sqrt_pos.mpr hγ) φ x ^ 2) =
        entropy (pointMeasure γ a y) (fun x => φ x ^ 2) := by
  letI := pointMeasure_isProbability (by norm_num : (0 : ℝ) < 1) ha (fun j => Real.sqrt γ • y j)
  letI := pointMeasure_isProbability hγ ha y
  exact pointDilationBranch_entropy_transport (pointDilationBranch_from_unit hγ a y)
    (pointDilationBranchLinear (Real.sqrt γ)⁻¹ (inv_pos.mpr (Real.sqrt_pos.mpr hγ))).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x => φ x ^ 2)

theorem pointDilationBranch_core_energy {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, ‖gradient (pointDilationBranchCore a y (Real.sqrt γ) (Real.sqrt_pos.mpr hγ) φ : ℂ → ℝ) x‖ ^ 2
      ∂pointMeasure 1 a (fun j => Real.sqrt γ • y j)) =
      γ⁻¹ * ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y := by
  simp_rw [pointDilationBranchCore_gradient_norm, mul_pow]
  rw [integral_const_mul, inv_pow, Real.sq_sqrt hγ.le]
  congr 1
  exact (pointDilationBranch_from_unit hγ a y).integral_comp
    (pointDilationBranchLinear (Real.sqrt γ)⁻¹ (inv_pos.mpr (Real.sqrt_pos.mpr hγ))).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x => ‖gradient (φ : ℂ → ℝ) x‖ ^ 2)

end RepulsiveCoulomb
