import LeanResearch.RepulsiveCoulomb.PointFirstReturnFullSides
import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

/-! Successor draft. Convert an actual full Jordan-side smooth/physical chart
pair into the literal retained-cone-neighborhood type. The metric radius,
whole ambient disk, onto map, and full ordered interval are constructed.
No chart-width equality, angle truncation, or assumed cap metric disk is used. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem pointClosedRadialInterval_positive_smul_of_norm_le
    {R S lo hi c : ℝ} {z : ℂ} (hc : 0 < c)
    (hz : z ∈ pointClosedRadialInterval S lo hi) (hbound : ‖c • z‖ ≤ R) :
    c • z ∈ pointClosedRadialInterval R lo hi := by
  obtain ⟨r, hr, θ, hθ, rfl⟩ := hz
  have he : c • pointRadialSectorPoint r θ = pointRadialSectorPoint (c * r) θ := by
    simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hcr : 0 ≤ c * r := mul_nonneg hc.le hr.1
  refine ⟨c * r, ⟨hcr, ?_⟩, θ, hθ, he⟩
  rw [he, pointRadialSectorPoint_norm hcr] at hbound
  exact hbound

/-- The radial power transition is a positive real scaling at every nonzero
point, and fixes zero. This statement preserves all real interval parameters. -/
theorem coneRadialEquiv_exists_positive_scale {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    ∃ c : ℝ, 0 < c ∧ coneRadialEquiv α hα z = c • z := by
  by_cases hz : z = 0
  · exact ⟨1, zero_lt_one, by simp only [hz, coneRadialEquiv_zero, smul_zero]⟩
  · refine ⟨(α + 1)⁻¹ * ‖z‖ ^ α,
      mul_pos (inv_pos.mpr (by linarith)) (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _), ?_⟩
    change (α + 1)⁻¹ • (‖z‖ ^ (α + 1 - 1) • z) = _
    rw [add_sub_cancel_right, smul_smul]

/-- Radial transition preserves the full interval, once both actual radial
bounds are imposed. No principal angle or cosine comparison occurs. -/
theorem coneRadialEquiv_closed_interval_iff {α : ℝ} (hα : 0 ≤ α)
    {z : ℂ} {R S lo hi : ℝ} (hz : ‖z‖ ≤ S)
    (hFz : ‖coneRadialEquiv α hα z‖ ≤ R) :
    coneRadialEquiv α hα z ∈ pointClosedRadialInterval R lo hi ↔
      z ∈ pointClosedRadialInterval S lo hi := by
  obtain ⟨c, hc, he⟩ := coneRadialEquiv_exists_positive_scale hα z
  constructor
  · intro h
    have hinv : c⁻¹ • coneRadialEquiv α hα z = z := by
      rw [he, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    have hb : ‖c⁻¹ • coneRadialEquiv α hα z‖ ≤ S := by rwa [hinv]
    simpa only [hinv] using pointClosedRadialInterval_positive_smul_of_norm_le (inv_pos.mpr hc) h hb
  · intro h
    rw [he] at hFz ⊢
    exact pointClosedRadialInterval_positive_smul_of_norm_le hc h hFz

/-- The closed initial-sector representation and the full closed interval
representation coincide strictly inside the same disk, including both rays. -/
theorem lineClosedInitialSector_iff_closed_interval
    {z : ℂ} {R θ : ℝ} (hz : z ∈ ball (0 : ℂ) R) (hθ : 0 < θ) :
    z ∈ lineClosedInitialSector R θ ↔ z ∈ pointClosedRadialInterval R 0 θ := by
  constructor
  · rintro ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩)
    · exact ⟨r, ⟨hr.1, hr.2.le⟩, 0, ⟨le_rfl, hθ.le⟩, rfl⟩
    · exact ⟨r, ⟨hr.1, hr.2.le⟩, θ, ⟨hθ.le, le_rfl⟩, rfl⟩
    · exact ⟨r, ⟨hr.1.le, hr.2.le⟩, φ, ⟨hφ.1.le, hφ.2.le⟩, rfl⟩
  · rintro ⟨r, hr, φ, hφ, rfl⟩
    have hrR : r < R := by
      simpa only [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.1] using hz
    by_cases hφ0 : φ = 0
    · exact Or.inl (Or.inl ⟨r, ⟨hr.1, hrR⟩, by rw [hφ0]⟩)
    by_cases hφθ : φ = θ
    · exact Or.inl (Or.inr ⟨r, ⟨hr.1, hrR⟩, by rw [hφθ]⟩)
    by_cases hr0 : r = 0
    · exact Or.inl (Or.inl ⟨0, ⟨le_rfl, by linarith⟩, by simp only [hr0, pointRadialSectorPoint_zero]⟩)
    · exact Or.inr ⟨(r, φ), ⟨⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hrR⟩,
        ⟨lt_of_le_of_ne hφ.1 (Ne.symm hφ0), lt_of_le_of_ne hφ.2 hφθ⟩⟩, rfl⟩

/-- Actual same-chart full-side geometry yields a genuine retained metric
neighborhood on a constructed smaller ambient metric disk. Both metric-disk
containment and onto coverage are proved, rather than being added as inputs. -/
theorem exists_retainedConeNeighborhood_of_full_physical_side
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (E F : OpenPartialHomeomorph ℂ ℂ)
    {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hside : ∀ z ∈ ball (0 : ℂ) δ,
      E.symm z ∈ P ↔ z ∈ lineClosedInitialSector δ θ)
    (hpF : p ∈ F.source) (hF0 : F p = 0) (hFsrc : F.source ⊆ E.source)
    (hF : ∀ z, F z = coneRadialEquiv (coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) (E z))
    (hmetric : ∀ u ∈ F.source, ∀ v ∈ F.source,
      (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (F u) (F v)) :
    ∃ C : PointRetainedConeNeighborhood a y P p,
      C.chart = F ∧ C.lo = 0 ∧ C.hi = θ := by
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hpE := hFsrc hpF
  have hE0 : E p = 0 := by
    apply (coneRadialEquiv α hα).injective
    rw [← hF, hF0, coneRadialEquiv_zero]
  let O := F.source ∩ E ⁻¹' ball (0 : ℂ) δ
  have hO : O ∈ 𝓝 p := by
    refine inter_mem (F.open_source.mem_nhds hpF) ?_
    apply (E.continuousAt hpE).preimage_mem_nhds
    rw [hE0]
    exact isOpen_ball.mem_nhds (mem_ball_self hδ)
  have hOm : O ∈ @nhds ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  obtain ⟨ε, hε, hεsub⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hOm
  have h0target : (0 : ℂ) ∈ F.target := hF0 ▸ F.mapsTo hpF
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (F.open_target.mem_nhds h0target)
  let R := min ε η / 2
  have hR : 0 < R := half_pos (lt_min hε hη)
  have hRε : R < ε := by dsimp [R]; linarith [min_le_left ε η, lt_min hε hη]
  have hRη : R < η := by dsimp [R]; linarith [min_le_right ε η, lt_min hε hη]
  have hlocal (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ R) :
      z ∈ F.source ∧ E z ∈ ball (0 : ℂ) δ := by
    apply hεsub
    change (pointSmoothConformalEDist a y z p).toReal < ε
    exact hz.trans_lt hRε
  have hnorm (z : ℂ) (hz : z ∈ F.source) :
      (pointSmoothConformalEDist a y z p).toReal = ‖F z‖ := by
    rw [hmetric z hz p hpF, hF0, pointClassicalConeDist_apex]
  have honto : BijOn F {z : ℂ | (pointSmoothConformalEDist a y z p).toReal ≤ R}
      {z : ℂ | ‖z‖ ≤ R} := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      change ‖F z‖ ≤ R
      rwa [← hnorm z (hlocal z hz).1]
    · intro z hz w hw he
      exact F.injOn (hlocal z hz).1 (hlocal w hw).1 he
    · intro z hz
      have hzt : z ∈ F.target := hηsub (by
        rw [mem_ball, dist_zero_right]
        exact hz.trans_lt hRη)
      have hzs : F.symm z ∈ F.source := F.symm.mapsTo hzt
      refine ⟨F.symm z, ?_, F.right_inv hzt⟩
      change (pointSmoothConformalEDist a y (F.symm z) p).toReal ≤ R
      rw [hnorm _ hzs, F.right_inv hzt]
      exact hz
  let C : PointRetainedConeNeighborhood a y P p :=
    { chart := F
      radius := R
      radius_pos := hR
      center := hF0
      source := fun z hz => (hlocal z hz).1
      onto := honto
      metric := fun z hz w hw => hmetric z (hlocal z hz).1 w (hlocal w hw).1
      lo := 0
      hi := θ
      width_pos := hθ
      width_le_full := by simpa only [sub_zero] using hθ2.le
      retained := by
        intro z hz
        obtain ⟨hzF, hzEball⟩ := hlocal z hz
        have hzE := hFsrc hzF
        have hmem : z ∈ P ↔ E z ∈ lineClosedInitialSector δ θ := by
          simpa only [E.left_inv hzE] using hside (E z) hzEball
        have hbound : ‖F z‖ ≤ R := by rwa [← hnorm z hzF]
        have hEbound : ‖E z‖ ≤ δ := by
          exact (show ‖E z‖ < δ by simpa only [mem_ball, dist_zero_right] using hzEball).le
        have hrad : coneRadialEquiv α hα (E z) ∈ pointClosedRadialInterval R 0 θ ↔
            E z ∈ pointClosedRadialInterval δ 0 θ :=
          coneRadialEquiv_closed_interval_iff hα hEbound
            (show ‖coneRadialEquiv α hα (E z)‖ ≤ R by rwa [← hF])
        rw [← hF z] at hrad
        exact hmem.trans ((lineClosedInitialSector_iff_closed_interval hzEball hθ).trans
          hrad.symm) }
  exact ⟨C, rfl, rfl, rfl⟩

end RepulsiveCoulomb
