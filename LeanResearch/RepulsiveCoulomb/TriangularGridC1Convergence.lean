module

public import LeanResearch.RepulsiveCoulomb.TriangularGridC1DerivativeError

@[expose] public section

/-! Actual value and almost-everywhere physical-gradient convergence for any
positive mesh sequence tending to zero, with a mesh-uniform gradient majorant. -/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

theorem sampledGridApproximation_value_tendsto {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (hlim : Tendsto h atTop (𝓝 0)) (z : ℂ) :
    Tendsto (fun n => sampledGridApproximation f hc (h n) (hh n) z) atTop (𝓝 (f z)) := by
  obtain ⟨C,_,hC⟩ := compactC1_grid_value_error hf hc
  have hprod : Tendsto (fun n => C * h n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g := fun n => C * h n) (fun n => norm_nonneg _) (fun n => ?_) hprod
  simpa only [Real.norm_eq_abs] using hC (h n) (hh n) z

theorem sampledGridApproximation_gradient_modulus {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ) (hh : 0 < h), h < δ →
      ∀ (z : ℂ) (i : GridTriangle), h⁻¹ • z ∈ gridOpenTriangle i →
        ‖gradient (sampledGridApproximation f hc h hh) z - gradient f z‖ < ε := by
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
    (compactC1_fderiv_uniformContinuous hf hc) (ε/4) (by positivity)
  refine ⟨δ/3,by positivity,?_⟩
  intro h hh hsmall z i hz
  have hdf : ∀ w ∈ closedBall z (2*h), ‖fderiv ℝ f w - fderiv ℝ f z‖ ≤ ε/4 := by
    intro w hw
    have hdist : dist w z ≤ 2*h := hw
    have hd : dist w z < δ := by linarith
    have he := hmod hd
    simpa only [dist_eq_norm] using he.le
  have he := sampledGridApproximation_gradient_error hf hc h hh hz hdf
  linarith

theorem sampledGridApproximation_gradient_ae_tendsto {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (hlim : Tendsto h atTop (𝓝 0)) :
    ∀ᵐ z : ℂ ∂volume, Tendsto (fun n => gradient (sampledGridApproximation f hc (h n) (hh n)) z)
      atTop (𝓝 (gradient f z)) := by
  filter_upwards [grid_sequence_ae_open_triangles h hh] with z hz
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := sampledGridApproximation_gradient_modulus hf hc hε
  have hhδ : ∀ᶠ n in atTop, h n < δ := hlim.eventually (gt_mem_nhds hδ)
  filter_upwards [hhδ] with n hn
  obtain ⟨i,hi⟩ := hz n
  simpa only [dist_eq_norm] using hmod (h n) (hh n) hn z i hi

theorem sampledGridApproximation_gradient_uniform_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (hh : 0 < h) (z : ℂ) (i : GridTriangle),
      h⁻¹ • z ∈ gridOpenTriangle i → ‖gradient (sampledGridApproximation f hc h hh) z‖ ≤ C := by
  have hdf : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨M,hM⟩ := hdf.exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ f 0)).trans (hM 0)
  refine ⟨5*M,by positivity,?_⟩
  intro h hh z i hz
  have hd : ∀ w ∈ closedBall z (2*h), ‖fderiv ℝ f w - fderiv ℝ f z‖ ≤ 2*M := by
    intro w _
    exact (norm_sub_le _ _).trans (by linarith [hM w,hM z])
  have he := sampledGridApproximation_gradient_error hf hc h hh hz hd
  have hb : ‖gradient f z‖ ≤ M := by
    change ‖(InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f z)‖ ≤ M
    rw [(InnerProductSpace.toDual ℝ ℂ).symm.norm_map]
    exact hM z
  calc
    _ = ‖(gradient (sampledGridApproximation f hc h hh) z - gradient f z) + gradient f z‖ := by rw [sub_add_cancel]
    _ ≤ ‖gradient (sampledGridApproximation f hc h hh) z - gradient f z‖ + ‖gradient f z‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem sampledGridApproximation_gradient_ae_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z : ℂ ∂volume, ∀ n,
      ‖gradient (sampledGridApproximation f hc (h n) (hh n)) z‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := sampledGridApproximation_gradient_uniform_bound hf hc
  refine ⟨C,hC0,?_⟩
  filter_upwards [grid_sequence_ae_open_triangles h hh] with z hz
  intro n
  obtain ⟨i,hi⟩ := hz n
  exact hC (h n) (hh n) z i hi

end RepulsiveCoulomb
