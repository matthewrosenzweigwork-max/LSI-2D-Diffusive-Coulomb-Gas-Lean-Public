import LeanResearch.RepulsiveCoulomb.PointSectorReturnOppositeBoundaryGerm

/-! Isolated, uncompiled. The actual clean metric ray determines its radial
chart germ and one of the two full old endpoint coordinates. Neither its radial
formula nor a selected endpoint is an input. Positive ambient exponents remain. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_clean_metric_ray_retained_endpoint_germ
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hP : IsClosed P)
    (ρ : ℝ → ℂ) (hρ0 : ρ 0 = p)
    (hρd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρfront : ∀ t ∈ Ici (0 : ℝ), ρ t ∈ frontier P) :
    ∃ T ξ : ℝ, 0 < T ∧ T < C.radius ∧ ξ ∈ Icc C.lo C.hi ∧
      (ξ = C.lo ∨ ξ = C.hi) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ρ t ∈ C.chart.source ∧
        C.chart (ρ t) = pointRadialSectorPoint t ξ ∧
        ρ t = C.chart.symm (pointRadialSectorPoint t ξ) := by
  let T := C.radius / 2
  have hT : 0 < T := half_pos C.radius_pos
  have hTR : T < C.radius := by dsimp [T]; linarith [C.radius_pos]
  have hdist (t : ℝ) (ht : 0 ≤ t) :
      (pointSmoothConformalEDist a y (ρ t) p).toReal = t := by
    have hd := hρd t ht 0 (show (0 : ℝ) ≤ 0 from le_rfl)
    simpa only [hρ0, Real.dist_eq, sub_zero, abs_of_nonneg ht] using hd
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ρ t ∈ C.chart.source := by
    apply C.source
    change (pointSmoothConformalEDist a y (ρ t) p).toReal ≤ C.radius
    rw [hdist t ht.1]
    exact ht.2.trans hTR.le
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖C.chart (ρ t)‖ = t := by
    have hd : (pointSmoothConformalEDist a y (ρ t) p).toReal ≤ C.radius := by
      rw [hdist t ht.1]
      exact ht.2.trans hTR.le
    exact (C.retainedWidth_chart_norm hd).trans (hdist t ht.1)
  have hTb : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hTmetric : (pointSmoothConformalEDist a y (ρ T) p).toReal ≤ C.radius := by
    rw [hdist T hT.le]
    exact hTR.le
  obtain ⟨r, hr, ξ, hξ, he⟩ := (C.retained (ρ T) hTmetric).mp
    (hP.frontier_subset (hρfront T hT.le))
  have hrT : r = T := by
    have hn := congrArg norm he
    rw [pointRadialSectorPoint_norm hr.1, hnorm T hTb] at hn
    exact hn.symm
  have heT : C.chart (ρ T) = pointRadialSectorPoint T ξ := by rwa [hrT] at he
  have hξends := C.frontier_radial_coordinate_endpoint (hρfront T hT.le)
    (by rw [hdist T hT.le]; exact hTR) hT hξ heT
  let γ : unitInterval → ℂ := fun u => C.chart (ρ (T * u.1))
  have htime (u : unitInterval) : T * u.1 ∈ Icc (0 : ℝ) T :=
    ⟨mul_nonneg hT.le u.2.1, by simpa only [mul_one] using mul_le_mul_of_nonneg_left u.2.2 hT.le⟩
  have hradial (u : unitInterval) : γ u = u.1 • C.chart (ρ T) := by
    apply classicalCone_geodesic_from_apex_nonneg
      (α := coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) γ (C.chart (ρ T))
      (by simp only [γ, mul_zero, hρ0, C.center]) (by simp only [γ, mul_one])
    intro u v
    change pointClassicalConeDist a y p (C.chart (ρ (T * u.1))) (C.chart (ρ (T * v.1))) = _
    rw [← C.metric (ρ (T * u.1)) (by rw [hdist _ (htime u).1]; exact (htime u).2.trans hTR.le)
      (ρ (T * v.1)) (by rw [hdist _ (htime v).1]; exact (htime v).2.trans hTR.le),
      hρd _ (htime u).1 _ (htime v).1, hnorm T hTb, Real.dist_eq,
      ← mul_sub, abs_mul, abs_of_pos hT, abs_sub_comm]
    ring
  refine ⟨T, ξ, hT, hTR, hξ, hξends, ?_⟩
  intro t ht
  let u : unitInterval := ⟨t / T, div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩
  have hTu : T * u.1 = t := by dsimp [u]; exact mul_div_cancel₀ t hT.ne'
  have hchart : C.chart (ρ t) = pointRadialSectorPoint t ξ := by
    have h := hradial u
    change C.chart (ρ (T * u.1)) = u.1 • C.chart (ρ T) at h
    rw [hTu, heT] at h
    have hsmul : u.1 • pointRadialSectorPoint T ξ = pointRadialSectorPoint (u.1 * T) ξ := by
      simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [hsmul, mul_comm u.1 T, hTu] at h
    exact h
  exact ⟨hsource t ht, hchart, by rw [← hchart, C.chart.left_inv (hsource t ht)]⟩

end RepulsiveCoulomb
