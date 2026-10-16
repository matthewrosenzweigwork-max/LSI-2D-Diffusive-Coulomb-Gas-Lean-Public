module

public import LeanResearch.RepulsiveCoulomb.PointConformalBiholomorphicCharts

@[expose] public section

/-! Exact transport and localization of smooth paths for the constructed metrics.
All densities and physical derivatives are explicit. -/
noncomputable section
open MeasureTheory Set Metric Filter Manifold
open scoped ENNReal Topology Manifold
namespace RepulsiveCoulomb

theorem pointConformalPathELength_congr {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {γ η : ℝ → ℂ} {s t : ℝ} (h : EqOn γ η (Icc s t)) :
    pointConformalPathELength a y γ s t = pointConformalPathELength a y η s t := by
  let := pointConformalTangentENorm a y
  rw [pointConformalPathELength_eq_manifold, pointConformalPathELength_eq_manifold]
  exact Manifold.pathELength_congr h

theorem pointConformalPathELength_mono {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) {s t u v : ℝ} (hu : u ≤ s) (hv : t ≤ v) :
    pointConformalPathELength a y γ s t ≤ pointConformalPathELength a y γ u v :=
  lintegral_mono_set (Icc_subset_Icc hu hv)

theorem pointConformalPath_transport {m n : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (b : Fin n → ℝ) (w : Fin n → ℂ) {U : Set ℂ} {F : ℂ → ℂ}
    (hF : ∀ z ∈ U, AnalyticAt ℂ F z ∧
      pointConformalDensity b w (F z) * ‖deriv F z‖ = pointConformalDensity a y z)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc s t))
    (hmap : MapsTo γ (Icc s t) U) :
    pointConformalPathELength a y γ s t = pointConformalPathELength b w (F ∘ γ) s t := by
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
  rw [hn, ENNReal.ofReal_mul (norm_nonneg _), ← mul_assoc,
    ← ENNReal.ofReal_mul (pointConformalDensity_nonneg b w _)]
  change _ = ENNReal.ofReal (pointConformalDensity b w (F (γ u)) * ‖deriv F (γ u)‖) * _
  rw [(hF (γ u) hmem).2]

theorem analyticOnNhd_comp_smooth_path {U : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) {γ : ℝ → ℂ} {s t : ℝ}
    (hγ : ContDiffOn ℝ 1 γ (Icc s t)) (hmap : MapsTo γ (Icc s t) U) :
    ContDiffOn ℝ 1 (F ∘ γ) (Icc s t) := by
  have hf : ContDiffOn ℝ 1 F U := by
    intro z hz
    exact ((hF z hz).contDiffAt (n := 1)).restrict_scalars ℝ |>.contDiffWithinAt
  exact hf.comp hγ hmap

theorem pointConformalPath_transport_inverse {m n : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (b : Fin n → ℝ) (w : Fin n → ℂ) (e : OpenPartialHomeomorph ℂ ℂ)
    (hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity b w (e z) * ‖deriv e z‖ = pointConformalDensity a y z)
    (hInv : AnalyticOnNhd ℂ e.symm e.target)
    {η : ℝ → ℂ} {s t : ℝ} (hη : ContDiffOn ℝ 1 η (Icc s t))
    (hmap : MapsTo η (Icc s t) e.target) :
    pointConformalPathELength a y (e.symm ∘ η) s t = pointConformalPathELength b w η s t := by
  have hγ := analyticOnNhd_comp_smooth_path hInv hη hmap
  have hm : MapsTo (e.symm ∘ η) (Icc s t) e.source := fun u hu ↦ e.map_target (hmap hu)
  rw [pointConformalPath_transport a y b w hF hγ hm]
  apply pointConformalPathELength_congr
  intro u hu
  exact e.right_inv (hmap hu)

theorem pointConformal_path_localization {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {γ : ℝ → ℂ} (hγ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1)) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hstart : pointSmoothConformalEDist a y c (γ 0) ≤ ENNReal.ofReal (R / 4))
    (hlen : pointConformalPathELength a y γ 0 1 ≤ ENNReal.ofReal (R / 2)) :
    ∀ t ∈ Icc (0 : ℝ) 1, pointSmoothConformalEDist a y c (γ t) < ENNReal.ofReal R := by
  intro t ht
  have hs : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
  have hd := pointSmoothConformalEDist_le_path a y (hγ.mono hs) ht.1
  have hm := pointConformalPathELength_mono a y γ (s := 0) (t := t) (u := 0) (v := 1) le_rfl ht.2
  calc
    _ ≤ pointSmoothConformalEDist a y c (γ 0) + pointSmoothConformalEDist a y (γ 0) (γ t) :=
      pointSmoothConformalEDist_triangle a y _ _ _
    _ ≤ ENNReal.ofReal (R / 4) + ENNReal.ofReal (R / 2) := add_le_add hstart (hd.trans (hm.trans hlen))
    _ < ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_ofReal_iff hR]
      linarith

end RepulsiveCoulomb
