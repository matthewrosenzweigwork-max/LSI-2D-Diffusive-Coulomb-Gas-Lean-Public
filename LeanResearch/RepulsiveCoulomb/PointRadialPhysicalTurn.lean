module

public import LeanResearch.RepulsiveCoulomb.PointPhysicalDirectedSector
public import LeanResearch.RepulsiveCoulomb.PointRadialC1PlaneArc

@[expose] public section

/-! The raw vectors retained by adjacent macro-arcs and their actual physical
outward tangents have exactly the same two cone-sector angles. Both tangents
share the derivative of the SAME chosen holomorphic chart, which cancels in
the angle ratio. This is the missing compatibility bridge for turn exclusion. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem cone_sector_angles_common_complex_factor (α : ℝ) {D : ℂ} (hD : D ≠ 0) (u v : ℂ) :
    coneShortSectorAngle α (D * u) (D * v) = coneShortSectorAngle α u v ∧
      coneLongSectorAngle α (D * u) (D * v) = coneLongSectorAngle α u v := by
  have hs : coneShortSectorAngle α (D * u) (D * v) = coneShortSectorAngle α u v := by
    rw [coneShortSectorAngle, coneShortSectorAngle, mul_div_mul_left _ _ hD]
  exact ⟨hs, by rw [coneLongSectorAngle, coneLongSectorAngle, hs]⟩

/-- Retained inward/outward radial germs give actual endpoint derivatives
in their one common chosen chart. No change of chart is introduced here. -/
theorem PointRadialC1PlaneArc.physical_sector_angles
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (e f : PointRadialC1PlaneArc ha y) (hjoin : e.curve 1 = f.curve 0) (α : ℝ) :
    coneShortSectorAngle α (-deriv e.curve 1) (deriv f.curve 0) =
        coneShortSectorAngle α e.rightVector f.leftVector ∧
      coneLongSectorAngle α (-deriv e.curve 1) (deriv f.curve 0) =
        coneLongSectorAngle α e.rightVector f.leftVector := by
  let E := pointChosenSmoothRadialChart ha y (e.curve 1)
  let H : ℂ → ℂ := E.symm
  obtain ⟨R, hR, hep, hp, hinv, _, _⟩ := pointChosenSmoothRadialChart_spec ha y (e.curve 1)
  have h0t : (0 : ℂ) ∈ E.target := hep ▸ E.mapsTo hp
  have hH : DifferentiableAt ℂ H 0 := (hinv 0 h0t).differentiableAt
  have heGerm : e.curve =ᶠ[𝓝 (1 : ℝ)] (fun t => H ((1 - t) • e.rightVector)) := e.right_radial
  have hfGerm : f.curve =ᶠ[𝓝 (0 : ℝ)] (fun t => H (t • f.leftVector)) := by
    have h := f.left_radial
    rw [← hjoin] at h
    exact h
  have heRad : HasDerivAt (fun t : ℝ => (1 - t) • e.rightVector) (-e.rightVector) 1 := by
    simpa only [id_eq, Pi.sub_apply, zero_sub, neg_one_smul] using
      ((hasDerivAt_const 1 (1 : ℝ)).sub (hasDerivAt_id 1)).smul_const e.rightVector
  have hfRad : HasDerivAt (fun t : ℝ => t • f.leftVector) f.leftVector 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const f.leftVector
  have hHe : HasDerivAt H (deriv H 0) (((1 : ℝ) - 1) • e.rightVector) := by
    simpa only [sub_self, zero_smul] using hH.hasDerivAt
  have hHf : HasDerivAt H (deriv H 0) ((0 : ℝ) • f.leftVector) := by
    simpa only [zero_smul] using hH.hasDerivAt
  have hde : deriv e.curve 1 = -(deriv H 0 * e.rightVector) := by
    have h := (hHe.comp (h := fun t : ℝ => (1 - t) • e.rightVector) 1 heRad).congr_of_eventuallyEq heGerm
    simpa only [mul_neg] using h.deriv
  have hdf : deriv f.curve 0 = deriv H 0 * f.leftVector :=
    ((hHf.comp (h := fun t : ℝ => t • f.leftVector) 0 hfRad).congr_of_eventuallyEq hfGerm).deriv
  have hD : deriv H 0 ≠ 0 := by
    intro hzero
    have hfne := f.regular 0 (by norm_num)
    apply hfne
    rw [hdf, hzero, zero_mul]
  rw [hde, neg_neg, hdf]
  exact cone_sector_angles_common_complex_factor α hD e.rightVector f.leftVector

/-- Same-chosen-chart passage turn bounds transfer to actual physical
outward tangent sectors without a hidden normalization hypothesis. -/
theorem PointRadialC1PlaneArc.physical_sector_turns_nonpos
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (e f : PointRadialC1PlaneArc ha y) (hjoin : e.curve 1 = f.curve 0) (α : ℝ)
    (hshort : Real.pi - coneShortSectorAngle α e.rightVector f.leftVector ≤ 0)
    (hlong : Real.pi - coneLongSectorAngle α e.rightVector f.leftVector ≤ 0) :
    Real.pi - coneShortSectorAngle α (-deriv e.curve 1) (deriv f.curve 0) ≤ 0 ∧
      Real.pi - coneLongSectorAngle α (-deriv e.curve 1) (deriv f.curve 0) ≤ 0 := by
  obtain ⟨hs, hl⟩ := e.physical_sector_angles f hjoin α
  exact ⟨by rwa [hs], by rwa [hl]⟩

end RepulsiveCoulomb
