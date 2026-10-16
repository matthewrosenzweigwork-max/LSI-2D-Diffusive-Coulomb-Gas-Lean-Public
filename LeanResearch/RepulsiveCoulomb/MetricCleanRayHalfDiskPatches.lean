import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment
import LeanResearch.RepulsiveCoulomb.MetricFlatChartInterior

/-! Successor source-only draft. Actual arclength-aligned halfdisk patches
along a clean minimizing ray, away from its base. Genuine retained halfdisks
supply the chart input; alignment, source width and bottom matching are outputs. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A Euclidean upper halfdisk centered on the specified real arclength. -/
def flatRayHalfDisk (r ε : ℝ) : Set ℂ := {z | dist z (r : ℂ) < ε ∧ 0 ≤ z.im}

/-- Construct one genuine bottom-collar patch at any positive ray parameter.
The normalized boundary coordinate is proved from the actual metric ray. -/
theorem exists_metricRay_aligned_halfDisk_patch {Y : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ) (r : NNReal) (hr : 0 < r)
    (C : MetricFlatHalfDiskChart Y (ρ r)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < (r : ℝ) ∧ ε < C.radius ∧ 2 * ε ≤ C.radius ∧
      ∃ F : flatRayHalfDisk r ε → Y, Isometry F ∧
        (∀ t : NNReal, ∀ ht : (t : ℂ) ∈ flatRayHalfDisk r ε,
          F ⟨(t : ℂ), ht⟩ = ρ t) ∧
        (∀ z, 0 < z.1.im → Nonempty (MetricFlatDiskChart Y (F z))) ∧
        ∃ e : flatUpperDisk C.radius ≃ᵢ ball (ρ r) C.radius,
          ∀ z, ∃ hz : z.1 - (r : ℂ) ∈ flatUpperDisk C.radius,
            F z = (e ⟨z.1 - (r : ℂ), hz⟩).1 := by
  have hrR : 0 < (r : ℝ) := hr
  let L := min ((r : ℝ) / 2) (C.radius / 2)
  have hL : 0 < L := lt_min (half_pos hrR) (half_pos C.radius_pos)
  have hLr : L < (r : ℝ) := (min_le_left _ _).trans_lt (half_lt_self hrR)
  have hLR : L < C.radius := (min_le_right _ _).trans_lt (half_lt_self C.radius_pos)
  let τ : Icc (-L) L → NNReal := fun t ↦ ⟨(r : ℝ) + t.1, by
    have hlow := t.2.1
    linarith⟩
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro t u
    change |((r : ℝ) + t.1) - ((r : ℝ) + u.1)| = |t.1 - u.1|
    congr 1
    ring
  have hτzero : τ (complexSymmetricIntervalZero hL) = r := by
    apply Subtype.ext
    simp [τ, complexSymmetricIntervalZero]
  obtain ⟨e, he0, heline⟩ := C.exists_aligned_to_short_interval hL hLR
    (ρ ∘ τ) (hρ.comp hτ) (congrArg ρ hτzero)
  let E : MetricFlatHalfDiskChart Y (ρ r) := ⟨C.radius, C.radius_pos, e, he0⟩
  have hsrc (z : flatRayHalfDisk r L) : z.1 - (r : ℂ) ∈ flatUpperDisk C.radius := by
    refine ⟨?_, ?_⟩
    · rw [← dist_eq_norm]
      exact z.2.1.trans hLR
    · simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using z.2.2
  let F : flatRayHalfDisk r L → Y := fun z ↦ (e ⟨z.1 - (r : ℂ), hsrc z⟩).1
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (e ⟨z.1 - (r : ℂ), hsrc z⟩) (e ⟨w.1 - (r : ℂ), hsrc w⟩) = dist z w
    rw [e.dist_eq]
    change dist (z.1 - (r : ℂ)) (w.1 - (r : ℂ)) = dist z.1 w.1
    exact dist_sub_right z.1 w.1 (r : ℂ)
  have htwo : 2 * L ≤ C.radius := by
    have h := min_le_right ((r : ℝ) / 2) (C.radius / 2)
    change L ≤ C.radius / 2 at h
    linarith
  refine ⟨L, hL, hLr, hLR, htwo, F, hF, ?_, ?_, e, ?_⟩
  · intro t ht
    have htabs : |(t : ℝ) - r| < L := by
      have h := ht.1
      simpa only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
    let u : Icc (-L) L := ⟨(t : ℝ) - r, (abs_lt.mp htabs).1.le, (abs_lt.mp htabs).2.le⟩
    have hu : τ u = t := by
      apply Subtype.ext
      dsimp [τ, u]
      ring
    have hearg : (⟨(t : ℂ) - (r : ℂ), hsrc ⟨(t : ℂ), ht⟩⟩ : flatUpperDisk C.radius) =
        halfDiskIntervalReal hLR u := by
      apply Subtype.ext
      simp only [halfDiskIntervalReal, u, Complex.ofReal_sub]
    change (e ⟨(t : ℂ) - (r : ℂ), hsrc ⟨(t : ℂ), ht⟩⟩).1 = ρ t
    rw [hearg, heline u]
    exact congrArg ρ hu
  · intro z hz
    apply E.exists_full_at ⟨z.1 - (r : ℂ), hsrc z⟩
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hz
  · intro z
    exact ⟨hsrc z, rfl⟩

end RepulsiveCoulomb
