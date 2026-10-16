import LeanResearch.RepulsiveCoulomb.PointRetainedConeRotation
import LeanResearch.RepulsiveCoulomb.PointRetainedWidthInvariance
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Isolated, uncompiled local frontier bridge. Principal polar coordinates
are used only on a small auxiliary angular neighborhood to prove openness.
The retained interval and its physical angular coordinates are never truncated. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- On a genuine small argument window, the radial-sector parametrization is
literally the inverse polar chart. Its open image is an open subset of the plane. -/
theorem sectorReturn_isOpen_radial_sector_of_pi_bounds
    {R lo hi : ℝ} (hlo : -Real.pi ≤ lo) (hhi : hi ≤ Real.pi) :
    IsOpen (pointOpenRadialSector R lo hi) := by
  have hpolar : (fun q : ℝ × ℝ => pointRadialSectorPoint q.1 q.2) =
      Complex.polarCoord.symm := by
    funext q
    simp only [pointRadialSectorPoint, Circle.coe_exp,
      Complex.exp_ofReal_mul_I, Complex.polarCoord_symm_apply]
  have hsub : Ioo (0 : ℝ) R ×ˢ Ioo lo hi ⊆ Complex.polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    change 0 < r ∧ -Real.pi < θ ∧ θ < Real.pi
    exact ⟨hr.1, hlo.trans_lt hθ.1, hθ.2.trans_le hhi⟩
  rw [pointOpenRadialSector, hpolar]
  exact Complex.polarCoord.isOpen_image_symm_of_subset_target
    (isOpen_Ioo.prod isOpen_Ioo) hsub

/-- Every strictly interior real angular coordinate and strictly interior
positive radius is an interior point of the literal full retained interval.
Only a small neighborhood is placed in a principal polar-coordinate window. -/
theorem sectorReturn_radial_point_mem_interior_interval
    {R lo hi r θ : ℝ} (hr : 0 < r) (hrR : r < R) (hθ : θ ∈ Ioo lo hi) :
    pointRadialSectorPoint r θ ∈ interior (pointClosedRadialInterval R lo hi) := by
  let a := max (lo - θ) (-Real.pi / 2)
  let b := min (hi - θ) (Real.pi / 2)
  have ha : a < 0 := by
    dsimp [a]
    exact max_lt (sub_neg.mpr hθ.1) (by linarith [Real.pi_pos])
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (sub_pos.mpr hθ.2) (by linarith [Real.pi_pos])
  have halower : -Real.pi ≤ a := by
    have h := le_max_right (lo - θ) (-Real.pi / 2)
    dsimp [a]
    linarith [Real.pi_pos]
  have hbupper : b ≤ Real.pi := by
    have h := min_le_right (hi - θ) (Real.pi / 2)
    dsimp [b]
    linarith [Real.pi_pos]
  let O := (fun z : ℂ => conePhase (-θ) * z) ⁻¹' pointOpenRadialSector R a b
  have hO : IsOpen O :=
    (sectorReturn_isOpen_radial_sector_of_pi_bounds halower hbupper).preimage
      (continuous_const.mul continuous_id)
  have hpoint : pointRadialSectorPoint r θ ∈ O := by
    change conePhase (-θ) * pointRadialSectorPoint r θ ∈ pointOpenRadialSector R a b
    rw [sectorReturn_rotate_radial_point, sub_self]
    exact ⟨(r, 0), ⟨⟨hr, hrR⟩, ⟨ha, hb⟩⟩, rfl⟩
  have hsub : O ⊆ pointClosedRadialInterval R lo hi := by
    intro z hz
    change conePhase (-θ) * z ∈ pointOpenRadialSector R a b at hz
    obtain ⟨⟨s, φ⟩, ⟨hs, hφ⟩, he⟩ := hz
    have hφlo : lo - θ ≤ φ :=
      (le_max_left (lo - θ) (-Real.pi / 2)).trans hφ.1.le
    have hφhi : φ ≤ hi - θ :=
      hφ.2.le.trans (min_le_left (hi - θ) (Real.pi / 2))
    apply (sectorReturn_rotate_closed_interval_iff R lo hi θ z).mp
    exact ⟨s, ⟨hs.1.le, hs.2.le⟩, φ, ⟨hφlo, hφhi⟩, he.symm⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hO.mem_nhds hpoint) hsub)

 theorem sectorReturn_closed_interval_norm_le
    {R lo hi : ℝ} {w : ℂ} (hw : w ∈ pointClosedRadialInterval R lo hi) : ‖w‖ ≤ R := by
  obtain ⟨r, hr, θ, _, rfl⟩ := hw
  rw [pointRadialSectorPoint_norm hr.1]
  exact hr.2

/-- Pull the literal open radial neighborhood through the genuine whole-disk
chart. All physical neighborhood and membership facts are constructed. -/
theorem PointRetainedConeNeighborhood.mem_interior_of_strict_radial_coordinate
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hzR : (pointSmoothConformalEDist a y z p).toReal < C.radius)
    {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo C.lo C.hi)
    (hchart : C.chart z = pointRadialSectorPoint r θ) : z ∈ interior P := by
  have hrR : r < C.radius := by
    have hn := C.retainedWidth_chart_norm hzR.le
    rw [hchart, pointRadialSectorPoint_norm hr.le] at hn
    exact hn.trans_lt hzR
  let O := interior (pointClosedRadialInterval C.radius C.lo C.hi)
  have hO : IsOpen O := isOpen_interior
  have htarget : O ⊆ C.chart.target := by
    intro w hw
    exact (C.retainedWidth_inverse
      (sectorReturn_closed_interval_norm_le (interior_subset hw))).1
  let W := C.chart.symm '' O
  have hW : IsOpen W := C.chart.isOpen_image_symm_of_subset_target hO htarget
  have hzW : z ∈ W := by
    refine ⟨C.chart z, ?_, C.chart.left_inv (C.source hzR.le)⟩
    rw [hchart]
    exact sectorReturn_radial_point_mem_interior_interval hr hrR hθ
  have hWP : W ⊆ P := by
    rintro x ⟨w, hw, rfl⟩
    have hinterval : w ∈ pointClosedRadialInterval C.radius C.lo C.hi := interior_subset hw
    have hn := sectorReturn_closed_interval_norm_le hinterval
    obtain ⟨_, he, hd⟩ := C.retainedWidth_inverse hn
    apply (C.retained (C.chart.symm w) (hd.trans_le hn)).mpr
    rwa [he]
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hW.mem_nhds hzW) hWP)

/-- A non-apex frontier point in a genuine retained chart has one of the two
FULL retained endpoint coordinates. Admissibility is not needed for this local
implication, and no bound on the physical retained angle is imposed. -/
theorem PointRetainedConeNeighborhood.frontier_radial_coordinate_endpoint
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hz : z ∈ frontier P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal < C.radius)
    {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Icc C.lo C.hi)
    (hchart : C.chart z = pointRadialSectorPoint r θ) : θ = C.lo ∨ θ = C.hi := by
  by_contra hn
  have hlo : θ ≠ C.lo := fun he => hn (Or.inl he)
  have hhi : θ ≠ C.hi := fun he => hn (Or.inr he)
  have hstrict : θ ∈ Ioo C.lo C.hi :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hlo), lt_of_le_of_ne hθ.2 hhi⟩
  exact hz.2 (C.mem_interior_of_strict_radial_coordinate hzR hr hstrict hchart)

end RepulsiveCoulomb
