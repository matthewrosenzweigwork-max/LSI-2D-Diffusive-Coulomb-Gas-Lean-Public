import LeanResearch.RepulsiveCoulomb.PlanarBoundaryClockOppositeRay
import LeanResearch.RepulsiveCoulomb.PointOriginalExtremeBoundaryRay
import LeanResearch.RepulsiveCoulomb.PointStrictCornerFromCleanForward
import LeanResearch.RepulsiveCoulomb.PointNoCleanBoundaryEndpoints
import LeanResearch.RepulsiveCoulomb.TranslatedStripRemovedContactRay

/-!
SOURCE-ONLY, UNCOMPILED. Strict residual angle at the actual attained corner
from original geometric data and the original no-clean-budget-ray obstruction.
The actual opposite extreme ray, its endpoint identification and its side are
constructed. No forward-ray, positive-angle, exact-contact or exhaustion
certificate is supplied by the caller.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem PointGeometricCutState.no_clean_iff_literal
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (K : PointGeometricCutState a y P ν α) :
    (¬ Nonempty K.CleanRay) ↔ PointNoCleanBudgetBoundaryRay a y P ν α := by
  constructor
  · intro hno hraw
    obtain ⟨ρ, hρ, hfront, hclean, hα⟩ := hraw
    apply hno
    exact ⟨{
      ray := ρ
      metric := hρ
      frontier := hfront
      clean := hclean
      budget_supported := Finsupp.mem_support_iff.mpr hα }⟩
  · intro hno hR
    obtain ⟨R⟩ := hR
    exact hno ⟨R.ray, R.metric, R.frontier, R.clean,
      Finsupp.mem_support_iff.mp R.budget_supported⟩

namespace PointTranslatedRegularData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} (D : PointTranslatedRegularData a y ha P ν α)

/-- This forgets only the distinguished initial ray and corner; every field
is existing original current-region data. -/
def geometricState : PointGeometricCutState a y P ν α where
  toPointRetainedSignedHalfplaneState := D.toPointRetainedSignedHalfplaneState
  budget := D.budget
  pieceCount := D.pieceCount
  pieces := D.pieces
  boundary_cover := D.boundary_cover

namespace FiniteWidthLimit
variable {D} (T : D.FiniteWidthLimit)

/-- Original no-clean-budget is the only additional hypothesis beyond the
actual finite-width construction. The conclusion is the strict inequality
required by the marked-return and actual residual producers. -/
theorem corner_residual_positive_of_no_clean
    (hno : PointNoCleanBudgetBoundaryRay a y P ν α)
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible) :
    Real.pi - D.angle < C.flatPhysicalWidth := by
  have hnonneg := T.corner_residual_nonnegative C hC
  by_contra hn
  have hzero : C.flatPhysicalWidth = Real.pi - D.angle := by
    have hle := le_of_not_gt hn
    linarith
  let p := (D.ray 0).1
  let z := (T.map (translatedStripTop T.positive.le 0)).1
  obtain ⟨hνz, hsum, _, _, _, _, _⟩ := T.zero_corner_consequences C hC hzero
  have hp : 0 < ν p := by
    change 0 < ν (D.ray 0).1
    rw [D.apex_coefficient]
    exact sub_pos.mpr D.angle_lt_pi
  have hz : 0 < ν z := hνz.symm ▸ D.angle_pos
  have hpz : p ≠ z := by
    have h := translatedStrip_apex_ne_top_origin D.direction_im_ne_zero T.positive T.closed.injective
    simpa only [T.bottom] using h
  have hzm : z ∈ pointSignedMarked ν α :=
    (mem_pointSignedMarked ν α z).mpr (Or.inl hz.ne')
  let δ : NNReal → ℂ := fun t ↦
    (T.map (translatedStripRemovedContactSource T.positive.le t)).1
  have hδ : IsClosedEmbedding δ := T.closed.comp
    (translatedStripRemovedContactSource_isClosedEmbedding D.direction_im_ne_zero T.positive.le)
  have hδ0 : δ 0 = z :=
    congrArg (fun q ↦ (T.map q).1) (translatedStripRemovedContactSource_zero T.positive.le)
  have hδb : δ (⟨sSup D.regularWidths, T.positive.le⟩ : NNReal) = p := by
    dsimp [δ]
    rw [translatedStripRemovedContactSource_after T.positive.le
      (⟨sSup D.regularWidths, T.positive.le⟩ : NNReal) le_rfl]
    have hzclock : (⟨sSup D.regularWidths - sSup D.regularWidths,
        sub_nonneg.mpr le_rfl⟩ : NNReal) = 0 := Subtype.ext (sub_self _)
    exact (congrArg (fun t : NNReal ↦ (T.map (translatedStripBottom T.positive.le t)).1) hzclock).trans
      (congrArg Subtype.val (T.bottom 0))
  let B : Set ℂ := range (fun r ↦ (T.map (translatedStripBottom T.positive.le r)).1) ∪
    range (fun u ↦ (T.map (translatedStripEdge u)).1)
  have hδrange : range δ = B := by
    change range ((fun q ↦ (T.map q).1) ∘ translatedStripRemovedContactSource T.positive.le) = B
    rw [range_comp, translatedStripRemovedContactSource_range T.positive.le, image_union,
      ← range_comp, ← range_comp]
    rfl
  have hBfront : B ⊆ frontier P := by
    rintro x (⟨r, rfl⟩ | ⟨u, rfl⟩)
    · change (T.map (translatedStripBottom T.positive.le r)).1 ∈ frontier P
      rw [T.bottom]
      exact D.ray_frontier r
    · exact T.edge_frontier u
  have hδfront : ∀ t, δ t ∈ frontier P := fun t ↦ hBfront (hδrange ▸ mem_range_self t)
  obtain ⟨β, clock, hβ, hβrange, hclock, hanti⟩ :=
    exists_full_boundary_clock_opposite_ray D.ambient D.region_eq δ hδ hδfront
  have hpsz : clock p < clock z := by
    have h := hanti (show (0 : NNReal) < ⟨sSup D.regularWidths, T.positive.le⟩ from T.positive)
    change clock (δ ⟨sSup D.regularWidths, T.positive.le⟩) < clock (δ 0) at h
    rwa [hδb, hδ0] at h
  let K := D.geometricState
  have hnoK : ¬ Nonempty K.CleanRay := K.no_clean_iff_literal.mpr hno
  obtain ⟨R⟩ := K.exists_extreme_boundary_ray_for_clock ha y
    ⟨z, hzm, T.contact_origin_frontier⟩ hnoK β hβ hβrange clock hclock
  have hzR : clock z ≤ clock R.point := R.maximal z hzm T.contact_origin_frontier
  have hRp : R.point ≠ p := by
    intro he
    rw [he] at hzR
    exact (not_le_of_gt hpsz) hzR
  have hRz : R.point = z :=
    pointSigned_saturated_last_mark_eq_target D.budget hpz hp hz hsum hRp
      R.marked R.allocation_zero
  let g : NNReal → P := fun t ↦
    ⟨R.ray t, D.toPointRetainedSignedHalfplaneState.isClosed.frontier_subset (R.frontier t)⟩
  have hg : @Isometry NNReal P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace g := by
    let M := pointRegionMetricSpace ha y P
    letI : MetricSpace P := M
    letI : PseudoMetricSpace P := M.toPseudoMetricSpace
    letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
    exact Isometry.of_dist_eq R.metric
  have hg0 : g 0 = T.map (translatedStripTop T.positive.le 0) :=
    Subtype.ext (R.start.trans hRz)
  have hgclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {(g 0).1})
      (range (fun t ↦ (g t).1)) := by
    change Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {R.ray 0}) (range R.ray)
    rw [R.start]
    exact R.clean
  have hforward : ∀ t : NNReal, 0 < t → (g t).1 ∉ B := by
    intro t ht hm
    obtain ⟨s, hs⟩ := hδrange.symm ▸ hm
    have hle := hanti.antitone (show (0 : NNReal) ≤ s from s.2)
    change clock (δ s) ≤ clock (δ 0) at hle
    rw [hs, hδ0, ← hRz] at hle
    exact (not_le_of_gt (R.outward t ht)) hle
  have hstrict := T.corner_residual_positive_of_clean_forward C hC g hg hg0
    R.frontier hgclean hforward
  rw [hzero] at hstrict
  exact (lt_irrefl _) hstrict

end FiniteWidthLimit
end PointTranslatedRegularData
end RepulsiveCoulomb
