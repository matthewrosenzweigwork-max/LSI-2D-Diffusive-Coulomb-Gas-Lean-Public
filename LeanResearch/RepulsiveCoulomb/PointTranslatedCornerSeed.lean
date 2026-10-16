import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart
import LeanResearch.RepulsiveCoulomb.ShearedRectangleGeometry
import LeanResearch.RepulsiveCoulomb.EuclideanRetainedChord

/-! ISOLATED SOURCE-ONLY DRAFT. Construct an actual positive two-dimensional
translated rectangle directly from the genuine positive-turn retained corner.
The supplied corner is a geometric retained chart, not a development family.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Nonnegative coordinates in the two genuine wedge directions lie in the
literal Euclidean short sector. -/
theorem flatShearedPoint_mem_closedSector {stripAngle r u : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    flatShearedPoint (conePhase stripAngle) r u ∈ closedEuclideanSector stripAngle := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).le
  apply mem_closedEuclideanSector_of_halfplanes stripAngle_pos stripAngle_lt_pi
  · simpa [flatShearedPoint, Complex.mul_im, conePhase_im] using mul_nonneg hu hs
  · simp only [flatShearedPoint, Complex.add_im, Complex.add_re, Complex.mul_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      zero_add, sub_zero, add_zero, conePhase_re, conePhase_im]
    nlinarith [mul_nonneg hr hs]

/-- The radius estimate uses the actual Euclidean source, not a product norm. -/
theorem flatShearedPoint_norm_le {v : ℂ} (hv : ‖v‖ = 1)
    {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) : ‖flatShearedPoint v r u‖ ≤ r + u := by
  calc
    _ ≤ ‖(r : ℂ)‖ + ‖(u : ℂ) * v‖ := norm_add_le _ _
    _ = r + u := by
      rw [norm_mul, hv, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hu]

/-- A concrete rectangle in a genuine retained corner. Both dimensions are
constructed positive and may be made smaller than any prescribed clearance. -/
theorem point_exists_translated_corner_seed
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hwidth : C.flatPhysicalWidth < Real.pi)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ ε : ℝ, 0 < ε ∧ ε < delta ∧
      ∃ F : flatShearedRectangle (conePhase C.flatPhysicalWidth) ε ε → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        ∀ z, (F z).1 = C.flatInverse z.1 := by
  let ε := min (C.radius / 4) (delta / 2)
  have hε : 0 < ε := lt_min (by linarith [C.radius_pos]) (half_pos hdelta)
  have hεδ : ε < delta := (min_le_right _ _).trans_lt (half_lt_self hdelta)
  have hεR : 2 * ε ≤ C.radius := by
    have h := min_le_left (C.radius / 4) (delta / 2)
    change ε ≤ C.radius / 4 at h
    linarith [C.radius_pos]
  have hsub : flatShearedRectangle (conePhase C.flatPhysicalWidth) ε ε ⊆
      retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    rintro z ⟨r, hr, u, hu, rfl⟩
    refine ⟨flatShearedPoint_mem_closedSector C.flatPhysicalWidth_pos hwidth hr.1 hu.1, ?_⟩
    have hru : r + u ≤ C.radius := by linarith [hr.2, hu.2]
    exact (flatShearedPoint_norm_le (conePhase_norm _) hr.1 hu.1).trans hru
  let incl : flatShearedRectangle (conePhase C.flatPhysicalWidth) ε ε →
      retainedFlatSectorDisk C.flatPhysicalWidth C.radius := Set.inclusion hsub
  let F := C.flatSectorChart ∘ incl
  refine ⟨ε, hε, hεδ, F, ?_, fun _ ↦ rfl⟩
  intro x z
  exact C.flatInverse_dist hwidth.le (hsub x.2) (hsub z.2)

end RepulsiveCoulomb
