module

public import LeanResearch.RepulsiveCoulomb.PointFlatLinkBoundaryFullness

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. One actual incoming boundary edge suffices to bound
the occupied angle by the whole old retained angle. Equality then fills the
old region locally. In particular the second source edge is NOT assumed to
lie on the old boundary, and no positive residual-angle premise is present.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem contactCorner_interval_radius_iff {r R lo hi : ℝ} (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    z ∈ pointClosedRadialInterval R lo hi ↔ z ∈ pointClosedRadialInterval r lo hi := by
  constructor
  · rintro ⟨s, hs, θ, hθ, he⟩
    refine ⟨s, ⟨hs.1, ?_⟩, θ, hθ, he⟩
    rw [he, pointRadialSectorPoint_norm hs.1] at hz
    exact hz
  · rintro ⟨s, hs, θ, hθ, he⟩
    exact ⟨s, ⟨hs.1, hs.2.trans hrR⟩, θ, hθ, he⟩

/-- Genuine link subtraction at an actual attached sector. The equality
branch proves local whole-region coverage, rather than treating zero angle
as impossible by definition. It applies to marked and unmarked corners. -/
theorem pointFlatLinkDisk_attached_width_and_equality_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hadm : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L)
    (hρC : ρ < C.radius)
    (hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩ 0) ∈ frontier P) :
    β ≤ C.flatPhysicalWidth ∧
      (C.flatPhysicalWidth = β →
        ∀ z, (pointSmoothConformalEDist a y z
            (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
          (z ∈ range f ↔ z ∈ P)) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by
    dsimp [k]
    linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β / k := div_pos hβ hk
  have hwidthFormula : C.flatPhysicalWidth = k * (C.hi - C.lo) := rfl
  have hcancel : k * (β / k) = β := mul_div_cancel₀ _ hk.ne'
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hρ hρL hρC hfront with hlo | hhi
  · obtain ⟨hbound, hocc⟩ := pointFlatLinkDisk_old_lower_occupancy
      ha y hβ hβπ hL f hd hfP C hadm hρ hρL hρC.le hlo
    have hspan : β / k ≤ C.hi - C.lo := by linarith
    have hβC : β ≤ C.flatPhysicalWidth := by
      calc
        β = k * (β / k) := hcancel.symm
        _ ≤ k * (C.hi - C.lo) := mul_le_mul_of_nonneg_left hspan hk.le
        _ = C.flatPhysicalWidth := hwidthFormula.symm
    refine ⟨hβC, ?_⟩
    intro he z hz
    have hspanEq : C.hi - C.lo = β / k := by
      apply mul_left_cancel₀ hk.ne'
      rw [← hwidthFormula, he, hcancel]
    have hend : C.lo + β / k = C.hi := by linarith
    have hn : ‖C.chart z‖ ≤ ρ :=
      (C.retainedWidth_chart_norm (hz.trans hρC.le)).trans_le hz
    have ho := hocc z hz
    rw [hend] at ho
    exact ho.trans ((contactCorner_interval_radius_iff hρC.le hn).symm.trans
      (C.retained z (hz.trans hρC.le)).symm)
  · obtain ⟨hbound, hocc⟩ := pointFlatLinkDisk_old_upper_occupancy
      ha y hβ hβπ hL f hd hfP C hadm hρ hρL hρC.le hhi
    have hspan : β / k ≤ C.hi - C.lo := by linarith
    have hβC : β ≤ C.flatPhysicalWidth := by
      calc
        β = k * (β / k) := hcancel.symm
        _ ≤ k * (C.hi - C.lo) := mul_le_mul_of_nonneg_left hspan hk.le
        _ = C.flatPhysicalWidth := hwidthFormula.symm
    refine ⟨hβC, ?_⟩
    intro he z hz
    have hspanEq : C.hi - C.lo = β / k := by
      apply mul_left_cancel₀ hk.ne'
      rw [← hwidthFormula, he, hcancel]
    have hend : C.hi - β / k = C.lo := by linarith
    have hn : ‖C.chart z‖ ≤ ρ :=
      (C.retainedWidth_chart_norm (hz.trans hρC.le)).trans_le hz
    have ho := hocc z hz
    rw [hend] at ho
    exact ho.trans ((contactCorner_interval_radius_iff hρC.le hn).symm.trans
      (C.retained z (hz.trans hρC.le)).symm)

end RepulsiveCoulomb
