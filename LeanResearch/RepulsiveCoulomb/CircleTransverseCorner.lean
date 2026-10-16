module

public import LeanResearch.RepulsiveCoulomb.JordanPhysicalHalfplane
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The exact algebra needed at a cap circle. Eventual radial transversality
of the actual minimizing tail is intentionally not asserted here. -/
noncomputable section
namespace RepulsiveCoulomb

def physicalDet (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re
def physicalRadialProjection (p v : ℂ) : ℝ := p.re * v.re + p.im * v.im

theorem physicalDet_ne_zero_left {u v : ℂ} (h : physicalDet u v ≠ 0) : u ≠ 0 := by
  intro heq
  simp [physicalDet, heq] at h

theorem physicalDet_ne_zero_right {u v : ℂ} (h : physicalDet u v ≠ 0) : v ≠ 0 := by
  intro heq
  simp [physicalDet, heq] at h

theorem physical_transverse_ratio_mem_slitPlane {u v : ℂ}
    (htrans : physicalDet u v ≠ 0) : v / u ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  rw [Complex.div_im, ← sub_div]
  apply div_ne_zero
  · convert htrans using 1 <;> unfold physicalDet <;> ring
  · exact (Complex.normSq_pos.mpr (physicalDet_ne_zero_left htrans)).ne'

theorem physicalDet_circle_tangent (p v : ℂ) (k : ℝ) :
    physicalDet v (k • (Complex.I * p)) = k * physicalRadialProjection p v := by
  simp [physicalDet, physicalRadialProjection, Complex.real_smul, Complex.mul_re, Complex.mul_im]
  ring

/-- A nonzero radial component forces a transverse circle junction and hence
the actual non-antipodal velocity quotient used by the turning theorem. -/
theorem transverse_circle_corner_mem_slitPlane {p v : ℂ} {k : ℝ}
    (hk : k ≠ 0) (hradial : physicalRadialProjection p v ≠ 0) :
    (k • (Complex.I * p)) / v ∈ Complex.slitPlane := by
  apply physical_transverse_ratio_mem_slitPlane
  rw [physicalDet_circle_tangent]
  exact mul_ne_zero hk hradial

theorem physicalDet_swap (u v : ℂ) : physicalDet v u = -physicalDet u v := by
  unfold physicalDet
  ring

/-- The same conclusion holds with incoming and outgoing arcs interchanged. -/
theorem transverse_circle_corner_reverse_mem_slitPlane {p v : ℂ} {k : ℝ}
    (hk : k ≠ 0) (hradial : physicalRadialProjection p v ≠ 0) :
    v / (k • (Complex.I * p)) ∈ Complex.slitPlane := by
  apply physical_transverse_ratio_mem_slitPlane
  rw [physicalDet_swap, physicalDet_circle_tangent]
  exact neg_ne_zero.mpr (mul_ne_zero hk hradial)

end RepulsiveCoulomb
