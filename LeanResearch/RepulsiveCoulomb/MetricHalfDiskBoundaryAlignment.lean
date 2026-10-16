import LeanResearch.RepulsiveCoulomb.MetricFlatHalfDiskChart
import LeanResearch.RepulsiveCoulomb.ComplexUpperIntervalRigidity

/-! Successor source-only draft. An actual two-sided unit-speed old boundary
segment determines the horizontal arclength coordinate of a genuine retained
halfdisk. The sign is derived, and corrected by an upper-side-preserving
reflection. No boundary-coordinate or orientation certificate is an input. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def halfDiskIntervalReal {R L : ℝ} (hLR : L < R) (t : Icc (-L) L) : flatUpperDisk R := by
  refine ⟨(t.1 : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr t.2).trans_lt hLR
  · simp

/-- Normalize a genuine whole metric halfdisk using only an actual isometric
boundary interval through its center. Its image automatically becomes the
real diameter; no assertion about the chart boundary is assumed. -/
theorem MetricFlatHalfDiskChart.exists_aligned_to_short_interval {Y : Type*} [MetricSpace Y] {p : Y}
    (C : MetricFlatHalfDiskChart Y p)
    {L : ℝ} (hL : 0 < L) (hLR : L < C.radius)
    (ρ : Icc (-L) L → Y) (hρ : Isometry ρ)
    (hzero : ρ (complexSymmetricIntervalZero hL) = p) :
    ∃ e : flatUpperDisk C.radius ≃ᵢ ball p C.radius,
      (e (flatUpperDiskZero C.radius_pos)).1 = p ∧
      ∀ t, (e (halfDiskIntervalReal hLR t)).1 = ρ t := by
  let z0 := complexSymmetricIntervalZero hL
  have hball (t : Icc (-L) L) : ρ t ∈ ball p C.radius := by
    change dist (ρ t) p < C.radius
    have hd := hρ.dist_eq t (complexSymmetricIntervalZero hL)
    rw [hzero] at hd
    rw [hd]
    change dist (t.1 : ℝ) (0 : ℝ) < C.radius
    rw [Real.dist_eq, sub_zero]
    exact (abs_le.mpr t.2).trans_lt hLR
  let τ : Icc (-L) L → ℂ :=
    fun t ↦ (C.fromEuclidean.symm ⟨ρ t, hball t⟩).1
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro t u
    change dist (C.fromEuclidean.symm ⟨ρ t, hball t⟩)
      (C.fromEuclidean.symm ⟨ρ u, hball u⟩) = dist t u
    rw [C.fromEuclidean.symm.dist_eq]
    exact hρ.dist_eq t u
  have hτzero : τ z0 = 0 := by
    have he : (⟨ρ z0, hball z0⟩ : ball p C.radius) =
        C.fromEuclidean (flatUpperDiskZero C.radius_pos) := by
      apply Subtype.ext
      exact hzero.trans C.center.symm
    change (C.fromEuclidean.symm ⟨ρ z0, hball z0⟩).1 = 0
    rw [he, C.fromEuclidean.symm_apply_apply]
    rfl
  obtain ⟨σ, hσ, hcoord⟩ := complex_upper_interval_isometry_eq_signed_real
    hL τ hτ hτzero (fun t ↦ (C.fromEuclidean.symm ⟨ρ t, hball t⟩).2.2)
  rcases hσ with hσ | hσ
  · refine ⟨C.fromEuclidean, C.center, ?_⟩
    intro t
    have he : C.fromEuclidean.symm ⟨ρ t, hball t⟩ = halfDiskIntervalReal hLR t := by
      apply Subtype.ext
      change τ t = (t.1 : ℂ)
      simpa only [hσ, one_mul] using hcoord t
    rw [← he, C.fromEuclidean.apply_symm_apply]
  · let e := (flatUpperDiskFlip C.radius).trans C.fromEuclidean
    refine ⟨e, ?_, ?_⟩
    · change (C.fromEuclidean (flatUpperDiskFlip C.radius (flatUpperDiskZero C.radius_pos))).1 = p
      rw [flatUpperDiskFlip_zero]
      exact C.center
    · intro t
      have he : C.fromEuclidean.symm ⟨ρ t, hball t⟩ =
          flatUpperDiskFlip C.radius (halfDiskIntervalReal hLR t) := by
        apply Subtype.ext
        change τ t = -star (t.1 : ℂ)
        simpa only [hσ, neg_one_mul, Complex.ofReal_neg, Complex.star_def,
          Complex.conj_ofReal] using hcoord t
      change (C.fromEuclidean (flatUpperDiskFlip C.radius (halfDiskIntervalReal hLR t))).1 = ρ t
      rw [← he, C.fromEuclidean.apply_symm_apply]

end RepulsiveCoulomb
