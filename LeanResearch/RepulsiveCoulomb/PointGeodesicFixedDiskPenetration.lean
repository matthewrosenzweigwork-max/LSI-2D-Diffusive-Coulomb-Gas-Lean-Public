import LeanResearch.RepulsiveCoulomb.PointGeodesicActualSubsegmentAperture
import LeanResearch.RepulsiveCoulomb.IntervalAngleIncrementBridge
import Mathlib.Tactic

/-! Uncompiled additive successor. Actual full-segment angle aperture and
fixed-disk penetration. The full radial lift is constructed, local lift increments
are matched exactly, and original endpoints are reached by closedness. No
caller-supplied lift, phase, branching family, or visibility certificate occurs. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointConformal_geodesic_actual_full_segment_aperture
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, A < ‖γ t‖)
    (hend : ‖γ 0‖ = ‖γ 1‖) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) ∧
      |φ 1 - φ 0| ≤
        (Real.pi + 2 * (pointExteriorMoment a y / A)) / (1 + pointExteriorHalfMass a) := by
  obtain ⟨φ, hφ, hφlift⟩ := exists_global_interval_argument_lift hc
    (fun t ht => norm_pos_iff.mp (hA.trans (havoid t ht)))
  obtain ⟨m, hm, hlocal⟩ := pointConformal_geodesic_actual_subsegment_aperture
    ha y γ hc L hL hgeo hA hyA hB hD havoid hend
  refine ⟨φ, hφ, hφlift, ?_⟩
  apply endpoint_angle_bound_of_interior_straddling_bounds hφ hm
  intro s hs u hu
  obtain ⟨ψ, hψ, hψlift, hbound⟩ := hlocal s u hs.1 hs.2 hu.1 hu.2
  have hsu : s < u := hs.2.trans hu.1
  have hφsub : ∀ t ∈ Icc s u,
      Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ) := by
    intro t ht
    exact hφlift t ⟨(hs.1.trans_le ht.1).le, (ht.2.trans_lt hu.2).le⟩
  rw [interval_argument_increment_eq hsu.le hφ hψ hφsub hψlift]
  exact hbound

theorem pointConformal_geodesic_opposite_fixed_disk_penetration
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hgap : 2 * (pointExteriorMoment a y / A) < Real.pi * pointExteriorHalfMass a)
    (hopposite : γ 1 = -γ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ A := by
  by_contra hnot
  have havoid : ∀ t ∈ Icc (0 : ℝ) 1, A < ‖γ t‖ := by
    intro t ht
    exact lt_of_not_ge (fun hbound => hnot ⟨t, ht, hbound⟩)
  have hend : ‖γ 0‖ = ‖γ 1‖ := by rw [hopposite, norm_neg]
  obtain ⟨φ, hφ, hφlift, hbound⟩ := pointConformal_geodesic_actual_full_segment_aperture
    ha y γ hc L hL hgeo hA hyA hB hD havoid hend
  have hzero : γ 0 ≠ 0 := norm_pos_iff.mp (hA.trans (havoid 0 (by norm_num)))
  have hzero_lift := hφlift 0 (by norm_num)
  have hone_lift : Complex.exp ((φ 1 : ℂ) * Complex.I) =
      (-γ 0) / (‖-γ 0‖ : ℂ) := by
    simpa only [hopposite] using hφlift 1 (by norm_num)
  have hlower := pi_le_abs_opposite_argument_increment hzero hzero_lift hone_lift
  have hp : 0 < 1 + pointExteriorHalfMass a := by linarith
  have hupper : (Real.pi + 2 * (pointExteriorMoment a y / A)) /
      (1 + pointExteriorHalfMass a) < Real.pi := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  linarith

end RepulsiveCoulomb
