import LeanResearch.RepulsiveCoulomb.CoulombCenterMeasure
import LeanResearch.RepulsiveCoulomb.PointDilationBranchTransport

/-! Exact Gaussian normalization, true coordinate marginals, and extended
entropy change of variables. Neither finite entropy nor an LSI is assumed. -/
noncomputable section
open Set MeasureTheory
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

theorem coulombCenterGaussianWeight_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (coulombCenterGaussianWeight β) := by
  have h := integrable_planar_gaussian (show 0 < β / 2 by positivity)
  convert h using 1
  funext c
  unfold coulombCenterGaussianWeight
  congr 1
  ring

theorem coulombCenterGaussian_integral {β : ℝ} (hβ : 0 < β) :
    (∫ c : ℂ, coulombCenterGaussianWeight β c) = 2 * Real.pi / β := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := ℂ) (show 0 < β / 2 by positivity)
  have he : (fun c : ℂ => coulombCenterGaussianWeight β c) =
      (fun c : ℂ => Real.exp (-(β / 2) * ‖c‖ ^ 2)) := by
    funext c
    unfold coulombCenterGaussianWeight
    congr 1
    ring
  rw [he, h]
  norm_num
  ring

theorem coulombCenterGaussianPartition_formula {β : ℝ} (hβ : 0 < β) :
    coulombCenterGaussianPartition β = ENNReal.ofReal (2 * Real.pi / β) := by
  rw [coulombCenterGaussianPartition,
    ← ofReal_integral_eq_lintegral_ofReal (coulombCenterGaussianWeight_integrable hβ)
      (Filter.Eventually.of_forall (fun c => (Real.exp_pos _).le)),
    coulombCenterGaussian_integral hβ]

/-- The center law has the manuscript's literal β/(2π) normalization. -/
theorem coulombCenterGaussian_density {β : ℝ} (hβ : 0 < β) :
    coulombCenterGaussian β =
      volume.withDensity (fun c : ℂ =>
        ENNReal.ofReal ((β / (2 * Real.pi)) * Real.exp (-β * ‖c‖ ^ 2 / 2))) := by
  rw [coulombCenterGaussian, coulombCenterGaussianPartition_formula hβ,
    ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi / β)]
  have hi : (2 * Real.pi / β)⁻¹ = β / (2 * Real.pi) := by
    rw [inv_div]
  rw [hi, ← withDensity_smul _ (coulombCenterGaussianWeight_measurable β).ennreal_ofReal]
  congr 1
  funext c
  simp only [Pi.smul_apply, smul_eq_mul, coulombCenterGaussianWeight,
    ENNReal.ofReal_mul (by positivity : 0 ≤ β / (2 * Real.pi))]

theorem coulombCenter_gibbsMeasurePreserving (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    MeasurePreserving (coulombCenterChart e) (coulombMeasure (n + 1) β)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) :=
  ⟨(coulombCenterChart e).measurable, coulombCenter_joint_law e he hβ⟩

/-- The relative measure is the actual marginal law, not just a chosen density. -/
theorem coulombCenter_relative_marginal (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    Measure.map (fun z => (coulombCenterChart e z).2) (coulombMeasure (n + 1) β) =
      coulombCenterRelativeMeasure e β := by
  letI := coulombCenterGaussian_isProbability hβ
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  change Measure.map (Prod.snd ∘ coulombCenterChart e) (coulombMeasure (n + 1) β) = _
  rw [← Measure.map_map measurable_snd (coulombCenterChart e).measurable,
    coulombCenter_joint_law e he hβ, Measure.map_snd_prod, measure_univ, one_smul]

/-- The center coordinate is exactly the normalized planar Gaussian. -/
theorem coulombCenter_gaussian_marginal (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    Measure.map (fun z => (coulombCenterChart e z).1) (coulombMeasure (n + 1) β) =
      coulombCenterGaussian β := by
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  letI := coulombCenterGaussian_isProbability hβ
  change Measure.map (Prod.fst ∘ coulombCenterChart e) (coulombMeasure (n + 1) β) = _
  rw [← Measure.map_map measurable_fst (coulombCenterChart e).measurable,
    coulombCenter_joint_law e he hβ, Measure.map_fst_prod, measure_univ, one_smul]

/-- Extended entropy is unchanged, including the +∞ case. -/
theorem coulombCenter_entropy_transport (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (f : ℂ × CoulombConfig n → ℝ) :
    entropy (coulombMeasure (n + 1) β) (fun z => f (coulombCenterChart e z)) =
      entropy ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) f := by
  letI := coulombMeasure_isProbability (N := n + 1) hβ
  letI := coulombCenterGaussian_isProbability hβ
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  exact pointDilationBranch_entropy_transport
    (coulombCenter_gibbsMeasurePreserving e he hβ)
    (coulombCenterChart e).measurableEmbedding f

end RepulsiveCoulomb
