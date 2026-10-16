import LeanResearch.RepulsiveCoulomb.TriangularGridWeightedGradientLimit
import LeanResearch.RepulsiveCoulomb.DoubleOscillationFatou
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual compact-C1 double oscillation, obtained from the constructed mesh
approximations by Fatou and weighted physical-gradient dominated convergence. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace RepulsiveCoulomb

theorem rawPoint_compactC1_double_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x : ℂ) {R : ℝ} (hR : 0 < R) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
    let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
    (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1 - f q.2| ∂ν.prod ν) ≤
      2 * ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)) *
        ∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient f z‖ * ENNReal.ofReal (rawPointWeight a y z) := by
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hh : ∀ n, 0 < h n := by intro n; dsimp [h]; positivity
  have hlim : Tendsto h atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
  let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
  let K := (2 : ℝ≥0∞) * ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q))
  let F : ℕ → ℂ → ℝ := fun n => sampledGridApproximation f hc (h n) (hh n)
  let D : ℕ → ℂ × ℂ → ℝ≥0∞ := fun n q => ENNReal.ofReal |F n q.1 - F n q.2|
  let E : ℕ → ℝ≥0∞ := fun n => ∫⁻ z in ball x (2*R),
    ENNReal.ofReal ‖gradient (F n) z‖ * ENNReal.ofReal (rawPointWeight a y z)
  change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1-f q.2| ∂ν.prod ν) ≤ K * _
  apply lintegral_le_of_ae_tendsto_of_eventually_bound (ν.prod ν) (F := D) (b := fun n => K * E n)
  · intro n
    have hfn := (sampledGridApproximation_continuous f hc (h n) (hh n)).measurable
    exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((hfn.comp measurable_fst).sub (hfn.comp measurable_snd)))).aemeasurable
  · apply Filter.Eventually.of_forall
    intro q
    have hv := (sampledGridApproximation_value_tendsto hf hc h hh hlim q.1).sub
      (sampledGridApproximation_value_tendsto hf hc h hh hlim q.2)
    simpa only [Real.norm_eq_abs] using ENNReal.tendsto_ofReal hv.norm
  · have h16 : Tendsto (fun n => 16 * h n) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (16 : ℝ)) atTop (𝓝 16)).mul hlim
    have hmesh : ∀ᶠ n in atTop, 16*h n ≤ R :=
      (h16.eventually (gt_mem_nhds hR)).mono (fun _ hn => hn.le)
    filter_upwards [hmesh] with n hn
    exact scaledTriangularGrid_double_oscillation ha hQ y (compactGridSamples f hc (h n) (hh n))
      (hh n) x hn
  · have hE := sampledGridApproximation_weighted_gradient_tendsto ha y hf hc h hh hlim x (2*R)
    have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    exact ENNReal.Tendsto.const_mul hE (Or.inr hK)

end RepulsiveCoulomb
