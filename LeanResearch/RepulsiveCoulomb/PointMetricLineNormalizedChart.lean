import LeanResearch.RepulsiveCoulomb.PointMetricLineRadialChart
import Mathlib.Topology.Algebra.GroupWithZero

/-! Normalize an actual complete line's full cone chart by an actual unit
rotation. The whole line boundary in the chart disk is identified with the
literal two disk rays, and both directed side-link angles remain at least pi. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem classicalCone_rotation_dist {α : ℝ} (hα : 0 ≤ α) {c : ℂ} (hc : ‖c‖ = 1)
    (x z : ℂ) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist (c * x) (c * z) =
      @dist ℂ (classicalConeMetricSpace α hα).toDist x z := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  rcases hα.eq_or_lt with he | hp
  · subst α
    rw [classicalCone_zero_dist, classicalCone_zero_dist, ← mul_sub, norm_mul, hc, one_mul]
  · rw [classicalCone_distance_formula hp, classicalCone_distance_formula hp,
      norm_mul, norm_mul, hc, one_mul, one_mul, mul_div_mul_left _ _ hc0]

theorem pointClassicalConeDist_rotation {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p : ℂ) {c : ℂ} (hc : ‖c‖ = 1) (x z : ℂ) :
    pointClassicalConeDist a y p (c * x) (c * z) = pointClassicalConeDist a y p x z :=
  classicalCone_rotation_dist
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) hc x z

/-- A closed unit radial trace, restricted to the open radius-R disk, is
exactly the corresponding literal half-open disk ray. -/
theorem unitRadialTrace_iff_diskRay {R : ℝ} (hR : 0 < R) (θ : ℝ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    z ∈ range (fun t : unitInterval ↦ pointRadialSectorPoint (R * t.1) θ) ↔
      z ∈ pointDiskRay R θ := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨R * t.1, ⟨mul_nonneg hR.le t.2.1, ?_⟩, rfl⟩
    simpa only [mem_ball, dist_zero_right,
      pointRadialSectorPoint_norm (mul_nonneg hR.le t.2.1)] using hz
  · rintro ⟨r, hr, rfl⟩
    let t : unitInterval := ⟨r / R, div_nonneg hr.1 hR.le, (div_le_one hR).mpr hr.2.le⟩
    refine ⟨t, ?_⟩
    change pointRadialSectorPoint (R * (r / R)) θ = pointRadialSectorPoint r θ
    rw [mul_div_cancel₀ _ hR.ne']

/-- The normalized chart is actually constructed, with a full all-pairs cone
metric disk and the exact inverse-chart membership test for the whole line. -/
theorem exists_pointMetricLine_normalized_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, ∃ R θ : ℝ,
      0 < R ∧ 0 < θ ∧ θ < 2 * Real.pi ∧ ℓ 0 ∈ F.source ∧ F (ℓ 0) = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R} ⊆ F.source ∧
      Set.BijOn F {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R}
        {w : ℂ | ‖w‖ ≤ R} ∧
      (∀ u, (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v (ℓ 0)).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal =
            pointClassicalConeDist a y (ℓ 0) (F u) (F v)) ∧
      ball (0 : ℂ) R ⊆ F.target ∧
      (∀ z ∈ ball (0 : ℂ) R,
        F.symm z ∈ range ℓ ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ) ∧
      Real.pi ≤ (coalescedPointExponent a y (ℓ 0) / 2 + 1) * θ ∧
      Real.pi ≤ (coalescedPointExponent a y (ℓ 0) / 2 + 1) * (2 * Real.pi - θ) := by
  obtain ⟨e, R, hR, he0, hsource, hbij, hmetric, hnpos, hnneg, hne, hradial,
    hcarrier, hshort, hlong⟩ := exists_pointMetricLine_radial_chart ha y ℓ hd
  obtain ⟨c, hc, θ, hθ0, hθ2, hcu, hcv, hratio⟩ :=
    exists_pointRadialSector_normalization (hnpos.trans hnneg.symm) hne
  rw [hnpos] at hcu hcv
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  let F := e.trans (Homeomorph.mulLeft₀ c hc0).toOpenPartialHomeomorph
  have hF (x : ℂ) : F x = c * e x := rfl
  have hFsource : F.source = e.source := by simp [F]
  have hrot : Set.BijOn (fun z : ℂ ↦ c * z) {w : ℂ | ‖w‖ ≤ R} {w : ℂ | ‖w‖ ≤ R} := by
    refine ⟨?_, fun _ _ _ _ h ↦ mul_left_cancel₀ hc0 h, ?_⟩
    · intro w hw
      change ‖c * w‖ ≤ R
      rw [norm_mul, hc, one_mul]
      exact hw
    · intro w hw
      refine ⟨c⁻¹ * w, ?_, ?_⟩
      · change ‖c⁻¹ * w‖ ≤ R
        rw [norm_mul, norm_inv, hc, inv_one, one_mul]
        exact hw
      · change c * (c⁻¹ * w) = w
        rw [mul_inv_cancel_left₀ hc0]
  have hFbij : Set.BijOn F
      {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R} {w : ℂ | ‖w‖ ≤ R} :=
    hrot.comp hbij
  have hFsrc : {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R} ⊆ F.source := by
    rw [hFsource]
    exact hsource
  have hzero : (pointSmoothConformalEDist a y (ℓ 0) (ℓ 0)).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  have hF0 : F (ℓ 0) = 0 := by rw [hF, he0, mul_zero]
  have hFmetric : ∀ u, (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R →
      ∀ v, (pointSmoothConformalEDist a y v (ℓ 0)).toReal ≤ R →
        (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y (ℓ 0) (F u) (F v) := by
    intro u hu v hv
    rw [hF, hF, pointClassicalConeDist_rotation a y (ℓ 0) hc]
    exact hmetric u hu v hv
  have htarget : ball (0 : ℂ) R ⊆ F.target := by
    intro w hw
    have hwR : ‖w‖ ≤ R := (show ‖w‖ < R by simpa only [mem_ball, dist_zero_right] using hw).le
    obtain ⟨x, hx, hxw⟩ := hFbij.surjOn hwR
    exact hxw ▸ F.mapsTo (hFsrc hx)
  have hrotate_radial (v : ℂ) (φ : ℝ) (hv : c * v = pointRadialSectorPoint R φ)
      (t : unitInterval) : c * (t.1 • v) = pointRadialSectorPoint (R * t.1) φ := by
    calc
      c * (t.1 • v) = t.1 • (c * v) := by simp only [Complex.real_smul]; ring
      _ = t.1 • pointRadialSectorPoint R φ := by rw [hv]
      _ = pointRadialSectorPoint (R * t.1) φ := by
        simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
        ring
  have hFcarrier : F '' (range ℓ ∩
      {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R}) =
      range (fun t : unitInterval ↦ pointRadialSectorPoint (R * t.1) 0) ∪
        range (fun t : unitInterval ↦ pointRadialSectorPoint (R * t.1) θ) := by
    change ((fun z : ℂ ↦ c * z) ∘ e) '' _ = _
    rw [image_comp, hcarrier, image_union]
    congr 1
    · rw [← range_comp]
      exact congrArg range (funext (hrotate_radial (e (ℓ R)) 0 hcu))
    · rw [← range_comp]
      exact congrArg range (funext (hrotate_radial (e (ℓ (-R))) θ hcv))
  have hboundary : ∀ z ∈ ball (0 : ℂ) R,
      F.symm z ∈ range ℓ ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ := by
    intro z hz
    have hzR : ‖z‖ ≤ R := (show ‖z‖ < R by simpa only [mem_ball, dist_zero_right] using hz).le
    obtain ⟨x, hx, hxz⟩ := hFbij.surjOn hzR
    have hinv : F.symm z = x := by rw [← hxz, F.left_inv (hFsrc hx)]
    have hiff : F.symm z ∈ range ℓ ↔ z ∈ F '' (range ℓ ∩
        {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R}) := by
      rw [hinv]
      constructor
      · intro hxl
        exact ⟨x, ⟨hxl, hx⟩, hxz⟩
      · rintro ⟨w, hw, hwz⟩
        have he : w = x := hFbij.injOn hw.2 hx (hwz.trans hxz.symm)
        exact he ▸ hw.1
    rw [hFcarrier] at hiff
    exact hiff.trans (or_congr (unitRadialTrace_iff_diskRay hR 0 hz)
      (unitRadialTrace_iff_diskRay hR θ hz))
  have hangles := cone_directed_sector_angles_eq_short_long hθ0 hθ2 hratio
    (α := coalescedPointExponent a y (ℓ 0) / 2)
  have hsideangles : Real.pi ≤ (coalescedPointExponent a y (ℓ 0) / 2 + 1) * θ ∧
      Real.pi ≤ (coalescedPointExponent a y (ℓ 0) / 2 + 1) * (2 * Real.pi - θ) := by
    rcases hangles with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨h₁.symm ▸ hshort, h₂.symm ▸ hlong⟩
    · exact ⟨h₁.symm ▸ hlong, h₂.symm ▸ hshort⟩
  exact ⟨F, R, θ, hR, hθ0, hθ2, hFsrc hzero, hF0, hFsrc, hFbij, hFmetric,
    htarget, hboundary, hsideangles⟩

end RepulsiveCoulomb
