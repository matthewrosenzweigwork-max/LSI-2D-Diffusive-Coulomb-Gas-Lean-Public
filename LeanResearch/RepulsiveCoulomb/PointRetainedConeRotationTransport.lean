import LeanResearch.RepulsiveCoulomb.PointRetainedConeRotation

/-! Isolated, uncompiled transport of genuine ray germs under the constructed
whole-retained-chart rotation. Only actual chart values are used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The radial direction of an actual point shifts by the same full real
amount as the old retained endpoints, while its actual metric radius is fixed. -/
theorem sectorReturn_rotated_chart_radial_germ
    (E F : ℂ → ℂ) {φ θ : ℝ}
    (hF : ∀ z, F z = conePhase (-φ) * E z) {z : ℂ}
    (hgerm : E z = pointRadialSectorPoint ‖E z‖ θ) :
    F z = pointRadialSectorPoint ‖F z‖ (θ - φ) := by
  have hn : ‖F z‖ = ‖E z‖ := by rw [hF, norm_mul, conePhase_norm, one_mul]
  calc
    F z = conePhase (-φ) * pointRadialSectorPoint ‖E z‖ θ :=
      (hF z).trans (congrArg (fun w : ℂ => conePhase (-φ) * w) hgerm)
    _ = pointRadialSectorPoint ‖E z‖ (θ - φ) := sectorReturn_rotate_radial_point _ _ _
    _ = pointRadialSectorPoint ‖F z‖ (θ - φ) := by rw [hn]

/-- The inverse-chart radial point is the SAME actual physical point after
rotation. This transports original old-ray collars without choosing a new ray. -/
theorem sectorReturn_rotated_chart_inverse_radial
    (E F : OpenPartialHomeomorph ℂ ℂ) {φ r θ : ℝ}
    (hsource : F.source = E.source)
    (hF : ∀ z, F z = conePhase (-φ) * E z)
    (htarget : pointRadialSectorPoint r θ ∈ E.target) :
    F.symm (pointRadialSectorPoint r (θ - φ)) = E.symm (pointRadialSectorPoint r θ) := by
  have hs : E.symm (pointRadialSectorPoint r θ) ∈ F.source := by
    rw [hsource]
    exact E.symm.mapsTo htarget
  have he : F (E.symm (pointRadialSectorPoint r θ)) = pointRadialSectorPoint r (θ - φ) := by
    rw [hF, E.right_inv htarget, sectorReturn_rotate_radial_point]
  rw [← he, F.left_inv hs]

/-- Normalize a genuine interior old-link direction to zero while preserving
its original full ordered distances from both boundary endpoints. -/
theorem PointRetainedConeNeighborhood.exists_normalize_interior_direction
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) {φ : ℝ} (hφ : φ ∈ Ioo C.lo C.hi) :
    ∃ D : PointRetainedConeNeighborhood a y P p,
      D.radius = C.radius ∧ D.chart.source = C.chart.source ∧
      (∀ z, D.chart z = conePhase (-φ) * C.chart z) ∧
      D.lo = C.lo - φ ∧ D.hi = C.hi - φ ∧
      D.lo < 0 ∧ 0 < D.hi ∧ D.hi - D.lo = C.hi - C.lo ∧
      (1 + coalescedPointExponent a y p / 2) * (-D.lo) =
        (1 + coalescedPointExponent a y p / 2) * (φ - C.lo) := by
  obtain ⟨D, hR, hs, hF, hlo, hhi⟩ := C.exists_rotate φ
  refine ⟨D, hR, hs, hF, hlo, hhi, ?_, ?_, ?_, ?_⟩
  · rw [hlo]
    exact sub_neg.mpr hφ.1
  · rw [hhi]
    exact sub_pos.mpr hφ.2
  · rw [hlo, hhi]
    ring
  · rw [hlo]
    ring

end RepulsiveCoulomb
