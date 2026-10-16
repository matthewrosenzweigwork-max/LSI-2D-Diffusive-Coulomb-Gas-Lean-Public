import LeanResearch.RepulsiveCoulomb.PointFlatLinkCornerSaturation
import LeanResearch.RepulsiveCoulomb.PointTranslatedStripCornerChart
import LeanResearch.RepulsiveCoulomb.PointTranslatedFiniteWidthLimit
import LeanResearch.RepulsiveCoulomb.PointSaturatedTwoCornerBudget

/-!
SOURCE-ONLY, UNCOMPILED. The attained translated corner has nonnegative
residual width from its actual map and incoming old edge. If equality holds,
the strip fills the old region in an actual metric neighborhood of that
corner. These conclusions require neither exact old-boundary contact nor
strict residual width. Sharp global budget consequences are then derived at
the actual limit. The global equality exclusion is deliberately not asserted.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- No old-frontier hypothesis is placed on the free ray. The only boundary
input is the actual incoming compact edge, available at the supremal limit
by closedness. -/
theorem pointTranslatedStrip_corner_width_and_equality_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 < b)
    (F : flatShearedStrip (conePhase stripAngle) b → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hedge : ∀ u : Icc (0 : ℝ) b, (F (translatedStripEdge u)).1 ∈ frontier P)
    (C : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb.le 0)).1)
    (hC : C.Admissible) :
    Real.pi - stripAngle ≤ C.flatPhysicalWidth ∧
      (C.flatPhysicalWidth = Real.pi - stripAngle →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ P,
          (pointSmoothConformalEDist a y z (F (translatedStripTop hb.le 0)).1).toReal ≤ ρ →
            z ∈ range (fun q ↦ (F q).1)) := by
  let β := Real.pi - stripAngle
  let L := b * Real.sin stripAngle / 2
  have hβ : 0 < β := sub_pos.mpr stripAngle_lt_pi
  have hβπ : β ≤ Real.pi := by dsimp [β]; linarith
  obtain ⟨hL, hLbound⟩ := translatedStripCorner_radius stripAngle_pos stripAngle_lt_pi hb
  let J := translatedStripCornerSource stripAngle_pos stripAngle_lt_pi hLbound
  let f : flatLinkSectorDisk β L → ℂ := fun q ↦ (F (J q)).1
  have hJ0 : J (flatLinkSectorDiskApex hβ.le hL.le) = translatedStripTop hb.le 0 := by
    apply Subtype.ext
    change translatedStripCornerRigid stripAngle b 0 = flatShearedPoint (conePhase stripAngle) 0 b
    exact translatedStripCornerRigid_zero stripAngle b
  have hcenter : f (flatLinkSectorDiskApex hβ.le hL.le) =
      (F (translatedStripTop hb.le 0)).1 := congrArg (fun q ↦ (F q).1) hJ0
  let C0 := C.transportCenter hcenter.symm
  have hC0 : C0.Admissible := by
    simpa only [C0, PointRetainedConeNeighborhood.transportCenter_admissible] using hC
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z := by
    rw [hF]
    exact (translatedStripCornerSource_isometry stripAngle_pos stripAngle_lt_pi hLbound).dist_eq x z
  have hfP (q : flatLinkSectorDisk β L) : f q ∈ P := (F (J q)).2
  let ρ := min L (C0.radius / 2)
  have hρ : 0 < ρ := lt_min hL (half_pos C0.radius_pos)
  have hρL : ρ ≤ L := min_le_left _ _
  have hρC : ρ < C0.radius :=
    (min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  have hρb : ρ ≤ b := hρL.trans (hLbound.trans
    (mul_le_of_le_one_right hb.le (Real.sin_le_one stripAngle)))
  let u : Icc (0 : ℝ) b := ⟨b - ρ, sub_nonneg.mpr hρb, sub_le_self _ hρ.le⟩
  have hfirst : J (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩ 0) =
      translatedStripEdge u := by
    apply Subtype.ext
    change translatedStripCornerRigid stripAngle b (sectorPolar ρ (β * (0 : unitInterval).1)) =
      flatShearedPoint (conePhase stripAngle) 0 (b - ρ)
    simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero]
    exact translatedStripCornerRigid_edge_zero stripAngle b ρ
  have hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩ 0) ∈ frontier P := by
    change (F (J _)).1 ∈ frontier P
    rw [hfirst]
    exact hedge u
  obtain ⟨hwidth, hfill⟩ := pointFlatLinkDisk_attached_width_and_equality_fullness
    ha y hβ hβπ hL f hd hfP C0 hC0 hρ hρL hρC hfront
  refine ⟨by simpa only [C0, β, PointRetainedConeNeighborhood.transportCenter_width] using hwidth, ?_⟩
  intro he
  have he0 : C0.flatPhysicalWidth = β := by
    simpa only [C0, β, PointRetainedConeNeighborhood.transportCenter_width] using he
  refine ⟨ρ, hρ, ?_⟩
  intro z hzP hz
  have hz0 : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ := by
    rwa [hcenter]
  obtain ⟨q, hq⟩ := (hfill he0 z hz0).mpr hzP
  exact ⟨J q, hq⟩

namespace PointTranslatedRegularData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} (D : PointTranslatedRegularData a y ha P ν α)

/-- The corner coefficient is identified with the actual selected width by
invariance of whole retained charts. -/
theorem apex_coefficient : ν (D.ray 0).1 = Real.pi - D.angle := by
  obtain ⟨C, _, hc⟩ := D.boundary_coeff _ (D.ray_frontier 0)
  have he : C.flatPhysicalWidth = D.corner.flatPhysicalWidth := by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y (D.ray 0).1 / 2) 1] using
      C.physical_width_eq D.corner
  exact hc.trans (congrArg (fun t ↦ Real.pi - t) he)

namespace FiniteWidthLimit
variable {D} (T : D.FiniteWidthLimit)

theorem contact_origin_frontier :
    (T.map (translatedStripTop T.positive.le 0)).1 ∈ frontier P := by
  let u : Icc (0 : ℝ) (sSup D.regularWidths) :=
    ⟨sSup D.regularWidths, T.positive.le, le_rfl⟩
  have he : translatedStripEdge (v := conePhase D.angle) u = translatedStripTop T.positive.le 0 :=
    Subtype.ext rfl
  rw [← he]
  exact T.edge_frontier u

/-- Any genuine whole retained chart at the attained origin carries the
original coefficient, by chart-width invariance. -/
theorem contact_origin_coefficient
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) :
    ν (T.map (translatedStripTop T.positive.le 0)).1 = Real.pi - C.flatPhysicalWidth := by
  obtain ⟨C0, _, hc⟩ := D.boundary_coeff _ T.contact_origin_frontier
  have he : C0.flatPhysicalWidth = C.flatPhysicalWidth := by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y
        (T.map (translatedStripTop T.positive.le 0)).1 / 2) 1] using
      C0.physical_width_eq C
  exact hc.trans (congrArg (fun t ↦ Real.pi - t) he)

/-- Attained-corner residual nonnegativity is now an output of the genuine
finite limit. Neither an attained marked point nor no-clean-ray obstruction
is needed for this local conclusion. -/
theorem corner_residual_nonnegative
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible) :
    0 ≤ C.flatPhysicalWidth - (Real.pi - D.angle) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  exact sub_nonneg.mpr (pointTranslatedStrip_corner_width_and_equality_fullness
    ha y D.angle_pos D.angle_lt_pi T.positive T.map
    (fun x z ↦ T.metric.dist_eq x z) T.edge_frontier C hC).1

/-- This is the literal zero-angle branch of the actual limit, with its
local fullness and all global signed-budget consequences. It does not claim
that local fullness propagates around the entire old boundary. -/
theorem zero_corner_consequences
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible)
    (hzero : C.flatPhysicalWidth = Real.pi - D.angle) :
    let p := (D.ray 0).1
    let z := (T.map (translatedStripTop T.positive.le 0)).1
    ν z = D.angle ∧ ν p + ν z = Real.pi ∧
      α p = 0 ∧ α z = 0 ∧
      (∀ x, α x = signedBudgetNeg (ν x)) ∧
      (∀ x, x ≠ p → x ≠ z →
        (x ∈ pointSignedMarked ν α ↔ ν x < 0) ∧
        (x ∈ pointSignedMarked ν α → 0 < α x)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ w ∈ P,
        (pointSmoothConformalEDist a y w z).toReal ≤ ρ →
          w ∈ range (fun q ↦ (T.map q).1) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let p := (D.ray 0).1
  let z := (T.map (translatedStripTop T.positive.le 0)).1
  have hp : ν p = Real.pi - D.angle := D.apex_coefficient
  have hz : ν z = D.angle := by
    dsimp [z]
    rw [T.contact_origin_coefficient C, hzero]
    ring
  have hp0 : 0 < ν p := by rw [hp]; exact sub_pos.mpr D.angle_lt_pi
  have hz0 : 0 < ν z := hz.symm ▸ D.angle_pos
  have hsum : ν p + ν z = Real.pi := by rw [hp, hz]; ring
  have hpz : p ≠ z := by
    have h := translatedStrip_apex_ne_top_origin D.direction_im_ne_zero
      T.positive T.closed.injective
    simpa only [T.bottom] using h
  obtain ⟨_, _, hα⟩ := pointSigned_two_positive_atoms_force_exact_allocation
    D.budget hpz hp0 hz0 hsum
  obtain ⟨hαp, hαz, hmarks⟩ := pointSigned_two_positive_atoms_classify_other_marks
    D.budget hpz hp0 hz0 hsum
  have hfill := (pointTranslatedStrip_corner_width_and_equality_fullness
    ha y D.angle_pos D.angle_lt_pi T.positive T.map
    (fun x z ↦ T.metric.dist_eq x z) T.edge_frontier C hC).2 hzero
  exact ⟨hz, hsum, hαp, hαz, hα, hmarks, hfill⟩

/-- Actual positive allocation at the attained corner already excludes the
zero-angle branch, without any outermost assumption or contact certificate.
The remaining hard case is a zero-allocation marked positive corner. -/
theorem corner_residual_positive_of_budget_positive
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible)
    (hα : 0 < α (T.map (translatedStripTop T.positive.le 0)).1) :
    Real.pi - D.angle < C.flatPhysicalWidth := by
  have hnonneg := T.corner_residual_nonnegative C hC
  by_contra hn
  have he : C.flatPhysicalWidth = Real.pi - D.angle := by
    have hle := le_of_not_gt hn
    linarith
  obtain ⟨_, _, _, hz, _, _, _⟩ := T.zero_corner_consequences C hC he
  exact hα.ne' hz

end FiniteWidthLimit
end PointTranslatedRegularData
end RepulsiveCoulomb
