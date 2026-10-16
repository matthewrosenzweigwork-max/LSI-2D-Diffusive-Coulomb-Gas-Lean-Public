import LeanResearch.RepulsiveCoulomb.PointConformalCompleteness
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! Holomorphic developing primitives away from actual punctures. This uses the
attributed Mathlib harmonic-conjugate theorem and disk-primitive theorem directly.
The derivative has modulus exactly rho, with no distortion constant. Local metric
isometry and the singular cone-chart construction remain separate obligations. -/
noncomputable section
open MeasureTheory Set Metric Filter InnerProductSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem exists_pointDomain_ball {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {x : ℂ} (hx : x ∉ pointPunctures a y) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (pointPunctures a y)ᶜ :=
  Metric.isOpen_iff.mp (pointPunctures_finite a y).isClosed.isOpen_compl x hx

theorem exists_pointConformal_primitive_on_ball {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) {r : ℝ}
    (hball : ball x r ⊆ (pointPunctures a y)ᶜ) :
    ∃ F : ℂ → ℂ, F x = 0 ∧ AnalyticOnNhd ℂ F (ball x r) ∧
      ∀ z ∈ ball x r, ‖deriv F z‖ = pointConformalDensity a y z ∧ deriv F z ≠ 0 := by
  have hh : HarmonicOnNhd (pointConformalLog a y) (ball x r) :=
    (pointConformalLog_harmonicOnNhd ha y).mono hball
  obtain ⟨H, hH, hre⟩ := hh.exists_analyticOnNhd_ball_re_eq
  have hg : DifferentiableOn ℂ (fun z ↦ Complex.exp (H z)) (ball x r) := by
    intro z hz
    exact ((hH z hz).differentiableAt.cexp).differentiableWithinAt
  obtain ⟨F, hFx, hF⟩ := hg.isExactOn_ball.with_val_at x 0
  have hFd : DifferentiableOn ℂ F (ball x r) :=
    fun z hz ↦ (hF z hz).differentiableAt.differentiableWithinAt
  refine ⟨F, hFx, hFd.analyticOnNhd isOpen_ball, ?_⟩
  intro z hz
  rw [(hF z hz).deriv]
  refine ⟨?_, Complex.exp_ne_zero _⟩
  have hrez : (H z).re = pointConformalLog a y z := hre hz
  rw [Complex.norm_exp, hrez]
  exact exp_pointConformalLog ha y (hball hz)

theorem exists_pointConformal_flat_primitive {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x : ℂ} (hx : x ∉ pointPunctures a y) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, F x = 0 ∧
      ball x r ⊆ (pointPunctures a y)ᶜ ∧ AnalyticOnNhd ℂ F (ball x r) ∧
      ∀ z ∈ ball x r, ‖deriv F z‖ = pointConformalDensity a y z ∧ deriv F z ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := exists_pointDomain_ball a y hx
  obtain ⟨F, h0, hF, hd⟩ := exists_pointConformal_primitive_on_ball ha y x hball
  exact ⟨r, hr, F, h0, hball, hF, hd⟩

/-- An actual local homeomorphism with complex derivative of modulus rho. -/
theorem exists_pointConformal_holomorphic_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x : ℂ} (hx : x ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, x ∈ e.source ∧ e x = 0 ∧
      e.source ⊆ (pointPunctures a y)ᶜ ∧
      ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
        ‖deriv e z‖ = pointConformalDensity a y z ∧ deriv e z ≠ 0 := by
  obtain ⟨r, hr, F, h0, hball, hF, hd⟩ := exists_pointConformal_flat_primitive ha y hx
  have hc : ContDiffAt ℂ 1 F x := (hF x (mem_ball_self hr)).contDiffAt
  have hs := (hc.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv (hd x (mem_ball_self hr)).2
  let e0 := hs.toOpenPartialHomeomorph F
  let e := e0.restrOpen (ball x r) isOpen_ball
  have hsub : e.source ⊆ ball x r := fun _ hz ↦ hz.2
  refine ⟨e, ?_, h0, hsub.trans hball, ?_⟩
  · exact ⟨hs.mem_toOpenPartialHomeomorph_source, mem_ball_self hr⟩
  · intro z hz
    change AnalyticAt ℂ F z ∧ ‖deriv F z‖ = pointConformalDensity a y z ∧ deriv F z ≠ 0
    exact ⟨hF z (hsub hz), hd z (hsub hz)⟩

/-- Exact preservation of lengths for smooth paths staying in a developing chart. -/
theorem pointConformal_chart_path_length {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {U : Set ℂ} {F : ℂ → ℂ}
    (hF : ∀ z ∈ U, AnalyticAt ℂ F z ∧ ‖deriv F z‖ = pointConformalDensity a y z)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc s t))
    (hmap : MapsTo γ (Icc s t) U) :
    pointConformalPathELength a y γ s t = ∫⁻ u in Icc s t, ‖deriv (F ∘ γ) u‖ₑ := by
  unfold pointConformalPathELength
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  have hmem : γ u ∈ U := hmap ⟨hu.1.le, hu.2.le⟩
  have hf := (hF (γ u) hmem).1.differentiableAt
  have hg : DifferentiableAt ℝ γ u :=
    ((hγ u ⟨hu.1.le, hu.2.le⟩).contDiffAt (Icc_mem_nhds hu.1 hu.2)).differentiableAt one_ne_zero
  rw [fderiv_comp_deriv u (hf.restrictScalars ℝ) hg,
    hf.fderiv_restrictScalars (𝕜 := ℝ)]
  have hn : ‖((fderiv ℂ F (γ u)).restrictScalars ℝ) (deriv γ u)‖ =
      pointConformalDensity a y (γ u) * ‖deriv γ u‖ := by
    change ‖fderiv ℂ F (γ u) (deriv γ u)‖ = _
    rw [fderiv_eq_smul_deriv, norm_smul,
      (hF (γ u) hmem).2, mul_comm]
  rw [← ofReal_norm, hn, ENNReal.ofReal_mul (pointConformalDensity_nonneg a y _)]

end RepulsiveCoulomb
