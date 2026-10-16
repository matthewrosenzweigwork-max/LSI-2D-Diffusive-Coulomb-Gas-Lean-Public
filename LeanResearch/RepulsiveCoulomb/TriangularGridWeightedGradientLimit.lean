module

public import LeanResearch.RepulsiveCoulomb.TriangularGridC1Convergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

/-! Actual dominated convergence of the physical weighted-gradient integral for
the constructed compact-C1 mesh samples. -/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem rawPoint_weighted_constant_lintegral_finite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (C : ℝ) (x : ℂ) (R : ℝ) :
    (∫⁻ z in ball x R, ENNReal.ofReal C * ENNReal.ofReal (rawPointWeight a y z)) ≠ ⊤ := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm : (∫⁻ z in ball x R, ENNReal.ofReal (rawPointWeight a y z)) = rawPointMeasure a y (ball x R) :=
    (withDensity_apply _ isOpen_ball.measurableSet).symm
  rw [hm]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (rawPointMeasure_ball_lt_top ha y x R).ne

theorem sampledGridApproximation_weighted_gradient_tendsto {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (hlim : Tendsto h atTop (𝓝 0)) (x : ℂ) (R : ℝ) :
    Tendsto (fun n => ∫⁻ z in ball x R,
      ENNReal.ofReal ‖gradient (sampledGridApproximation f hc (h n) (hh n)) z‖ *
        ENNReal.ofReal (rawPointWeight a y z)) atTop
      (𝓝 (∫⁻ z in ball x R, ENNReal.ofReal ‖gradient f z‖ * ENNReal.ofReal (rawPointWeight a y z))) := by
  obtain ⟨C,hC0,hC⟩ := sampledGridApproximation_gradient_ae_bound hf hc h hh
  have hw : Measurable (fun z => ENNReal.ofReal (rawPointWeight a y z)) :=
    ENNReal.measurable_ofReal.comp (rawPointWeight_continuous ha y).measurable
  apply tendsto_lintegral_of_dominated_convergence'
    (fun z => ENNReal.ofReal C * ENNReal.ofReal (rawPointWeight a y z))
  · intro n
    exact ((ENNReal.measurable_ofReal.comp (complex_gradient_measurable _).norm).mul hw).aemeasurable
  · intro n
    have hb : ∀ᵐ z ∂(volume.restrict (ball x R)), ∀ n,
        ‖gradient (sampledGridApproximation f hc (h n) (hh n)) z‖ ≤ C := ae_restrict_of_ae hC
    filter_upwards [hb] with z hz
    have hn := hz n
    gcongr
  · exact rawPoint_weighted_constant_lintegral_finite ha y C x R
  · have hg : ∀ᵐ z ∂(volume.restrict (ball x R)),
        Tendsto (fun n => gradient (sampledGridApproximation f hc (h n) (hh n)) z) atTop (𝓝 (gradient f z)) :=
      ae_restrict_of_ae (sampledGridApproximation_gradient_ae_tendsto hf hc h hh hlim)
    filter_upwards [hg] with z hz
    have hp := hz.norm.mul_const (rawPointWeight a y z)
    have he := ENNReal.tendsto_ofReal hp
    simpa only [ENNReal.ofReal_mul (norm_nonneg _)] using he

end RepulsiveCoulomb
