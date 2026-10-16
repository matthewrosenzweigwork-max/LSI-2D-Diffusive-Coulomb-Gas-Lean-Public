module

public import LeanResearch.RepulsiveCoulomb.MetricFlatHalfDiskChart
public import LeanResearch.RepulsiveCoulomb.ComplexBoundarySideRigidity

@[expose] public section

/-! Successor source-only draft. Closed-side two-anchor uniqueness is derived
from Euclidean distances. This is the comparison tool for actual overlapping
bottom halfdisk patches; no chart-transition identity is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Conjugate points in the same closed upper halfplane coincide. -/
theorem complex_eq_of_two_real_dist_eq_of_nonneg_im {s t : ℝ} (hst : s ≠ t)
    {x y : ℂ} (hs : dist x (s : ℂ) = dist y (s : ℂ))
    (ht : dist x (t : ℂ) = dist y (t : ℂ))
    (hx : 0 ≤ x.im) (hy : 0 ≤ y.im) : x = y := by
  rcases complex_eq_or_conj_of_two_real_dist_eq hst hs ht with he | he
  · exact he
  · have hre : x.re = y.re := by simpa only [Complex.star_def, Complex.conj_re] using congrArg Complex.re he
    have him : x.im = -y.im := by simpa only [Complex.star_def, Complex.conj_im] using congrArg Complex.im he
    exact Complex.ext hre (by linarith)

/-- Actual metric halfdisk points are determined by their distances to two
specified real-boundary anchors. No upper-side label replaces coordinates. -/
theorem metricHalfDisk_two_anchor_unique {Y : Type*} [MetricSpace Y]
    {p : Y} {R : ℝ} (e : flatUpperDisk R ≃ᵢ ball p R)
    {s t : ℝ} (hst : s ≠ t) (hs : (s : ℂ) ∈ flatUpperDisk R)
    (ht : (t : ℂ) ∈ flatUpperDisk R) {x y : ball p R}
    (hsd : dist x (e ⟨(s : ℂ), hs⟩) = dist y (e ⟨(s : ℂ), hs⟩))
    (htd : dist x (e ⟨(t : ℂ), ht⟩) = dist y (e ⟨(t : ℂ), ht⟩)) : x = y := by
  apply e.symm.injective
  apply Subtype.ext
  apply complex_eq_of_two_real_dist_eq_of_nonneg_im hst
    (x := (e.symm x).1) (y := (e.symm y).1)
  · change dist (e.symm x) (⟨(s : ℂ), hs⟩ : flatUpperDisk R) =
      dist (e.symm y) (⟨(s : ℂ), hs⟩ : flatUpperDisk R)
    rw [← e.dist_eq, ← e.dist_eq, e.apply_symm_apply, e.apply_symm_apply]
    exact hsd
  · change dist (e.symm x) (⟨(t : ℂ), ht⟩ : flatUpperDisk R) =
      dist (e.symm y) (⟨(t : ℂ), ht⟩ : flatUpperDisk R)
    rw [← e.dist_eq, ← e.dist_eq, e.apply_symm_apply, e.apply_symm_apply]
    exact htd
  · exact (e.symm x).2.2
  · exact (e.symm y).2.2

end RepulsiveCoulomb
