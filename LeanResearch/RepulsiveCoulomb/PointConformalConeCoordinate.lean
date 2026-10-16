import LeanResearch.RepulsiveCoulomb.HolomorphicConeCoordinate

/-! Actual cone-density coordinates for the literal finite point configuration.
The coordinate is a local homeomorphism and preserves the weighted lengths of
smooth curves exactly. Identification with the intrinsic Euclidean cone metric
and the global polyhedral-surface structure remain separate obligations. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_cone_coordinate {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
        ‖e z‖ ^ (coalescedPointExponent a y p / 2) * ‖deriv e z‖ = pointConformalDensity a y z := by
  obtain ⟨r, hr, g, hg, hg0, hfac⟩ := exists_pointConformal_holomorphic_puncture_factor ha y p
  obtain ⟨e, hep, he0, hsub, he⟩ := exists_holomorphic_cone_coordinate (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) p hr hg
    (hg0 p (mem_ball_self hr))
  refine ⟨e, hep, he0, ?_⟩
  intro z hz
  exact ⟨(he z hz).1, (he z hz).2.trans (hfac z (hsub hz)).symm⟩

theorem pointConformal_cone_path_length {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {U : Set ℂ} {F : ℂ → ℂ} {α : ℝ}
    (hF : ∀ z ∈ U, AnalyticAt ℂ F z ∧ ‖F z‖ ^ α * ‖deriv F z‖ = pointConformalDensity a y z)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc s t))
    (hmap : MapsTo γ (Icc s t) U) :
    pointConformalPathELength a y γ s t = ∫⁻ u in Icc s t,
      ENNReal.ofReal (‖F (γ u)‖ ^ α) * ‖deriv (F ∘ γ) u‖ₑ := by
  unfold pointConformalPathELength
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  have hmem := hmap ⟨hu.1.le, hu.2.le⟩
  have hf := (hF (γ u) hmem).1.differentiableAt
  have hg : DifferentiableAt ℝ γ u :=
    ((hγ u ⟨hu.1.le, hu.2.le⟩).contDiffAt (Icc_mem_nhds hu.1 hu.2)).differentiableAt one_ne_zero
  rw [fderiv_comp_deriv u (hf.restrictScalars ℝ) hg, hf.fderiv_restrictScalars (𝕜 := ℝ)]
  have hn : ‖((fderiv ℂ F (γ u)).restrictScalars ℝ) (deriv γ u)‖ =
      ‖deriv F (γ u)‖ * ‖deriv γ u‖ := by
    change ‖fderiv ℂ F (γ u) (deriv γ u)‖ = _
    rw [fderiv_eq_smul_deriv, norm_smul, mul_comm]
  rw [← ofReal_norm, hn, ENNReal.ofReal_mul (norm_nonneg _)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), (hF (γ u) hmem).2]

def pointConeAngle {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) : ℝ :=
  2 * Real.pi * (1 + coalescedPointExponent a y p / 2)

theorem pointConeAngle_eq {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    pointConeAngle a y p = 2 * Real.pi + Real.pi * coalescedPointExponent a y p := by
  unfold pointConeAngle
  ring

theorem pointConeAngle_ge_two_pi {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    2 * Real.pi ≤ pointConeAngle a y p := by
  rw [pointConeAngle_eq]
  nlinarith [coalescedPointExponent_nonneg a y p, Real.pi_pos]

end RepulsiveCoulomb
