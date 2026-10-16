import LeanResearch.RepulsiveCoulomb.EuclideanClosedSectorSource
import LeanResearch.RepulsiveCoulomb.ComplexDirectMotionRigidity
import Mathlib.Analysis.Complex.Basic

/-! SOURCE-ONLY, UNCOMPILED. Actual halfdisk source models at a nonapex
point of either boundary ray. The beta = pi endpoint is handled separately.
The top-edge model is reflected so its inward side is always the upper
halfdisk. These are explicit Euclidean changes of coordinates, not assumptions
about the physical angle at the image point. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def sectorBottomEdgeChart (r : ℝ) : ℂ ≃ᵢ ℂ :=
  complexDirectMotion 1 (r : ℂ) (norm_one : ‖(1 : ℂ)‖ = 1)

def sectorTopEdgeChart (r β : ℝ) : ℂ ≃ᵢ ℂ :=
  Complex.conjLIE.toIsometryEquiv.trans
    (complexDirectMotion (conePhase β) (sectorPolar r β) (conePhase_norm β))

@[simp] theorem sectorBottomEdgeChart_apply (r : ℝ) (w : ℂ) :
    sectorBottomEdgeChart r w = w + (r : ℂ) := by
  change 1 * w + (r : ℂ) = _
  rw [one_mul]

@[simp] theorem sectorBottomEdgeChart_zero (r : ℝ) :
    sectorBottomEdgeChart r 0 = (r : ℂ) := by simp

@[simp] theorem sectorTopEdgeChart_zero (r β : ℝ) :
    sectorTopEdgeChart r β 0 = sectorPolar r β := by
  change conePhase β * star (0 : ℂ) + sectorPolar r β = _
  simp

theorem sectorTopEdgeChart_support (r β : ℝ) (w : ℂ) :
    Real.cos β * (sectorTopEdgeChart r β w).im -
      Real.sin β * (sectorTopEdgeChart r β w).re = -w.im := by
  change Real.cos β * (conePhase β * star w + sectorPolar r β).im -
    Real.sin β * (conePhase β * star w + sectorPolar r β).re = _
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, conePhase_re, conePhase_im,
    sectorPolar_re, sectorPolar_im]
  calc
    _ = -(Real.sin β ^ 2 + Real.cos β ^ 2) * w.im := by ring
    _ = -w.im := by rw [Real.sin_sq_add_cos_sq]; ring

theorem exists_sectorBottomEdgeChart_halfdisk {r β : ℝ}
    (hr : 0 < r) (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, ‖w‖ ≤ R →
      (sectorBottomEdgeChart r w ∈ closedEuclideanSector β ↔ 0 ≤ w.im) := by
  by_cases heq : β = Real.pi
  · refine ⟨1, by norm_num, fun w _ ↦ ?_⟩
    subst β
    rw [closedEuclideanSector_eq_halfplanes hβ le_rfl]
    simp only [Set.mem_ofPred_eq, sectorBottomEdgeChart_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero, Real.cos_pi, Real.sin_pi,
      zero_mul, sub_zero, neg_one_mul]
    constructor
    · exact And.left
    · intro hw
      exact ⟨hw, neg_nonpos.mpr hw⟩
  · have hβlt : β < Real.pi := lt_of_le_of_ne hβπ heq
    let V : Set ℂ := {w | Real.cos β * (sectorBottomEdgeChart r w).im -
      Real.sin β * (sectorBottomEdgeChart r w).re < 0}
    have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
    have h0 : (0 : ℂ) ∈ V := by
      change Real.cos β * (sectorBottomEdgeChart r 0).im -
        Real.sin β * (sectorBottomEdgeChart r 0).re < 0
      rw [sectorBottomEdgeChart_zero]
      simp only [Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_sub]
      exact neg_neg_of_pos (mul_pos (Real.sin_pos_of_pos_of_lt_pi hβ hβlt) hr)
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0
    refine ⟨ε / 2, half_pos hε, fun w hw ↦ ?_⟩
    have hwV : w ∈ V := hεV (by
      rw [mem_ball, dist_zero_right]
      exact hw.trans_lt (half_lt_self hε))
    rw [closedEuclideanSector_eq_halfplanes hβ hβπ]
    have him : (sectorBottomEdgeChart r w).im = w.im := by simp
    exact ⟨fun h ↦ him ▸ h.1, fun h ↦ ⟨him.symm ▸ h, hwV.le⟩⟩

theorem exists_sectorTopEdgeChart_halfdisk {r β : ℝ}
    (hr : 0 < r) (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, ‖w‖ ≤ R →
      (sectorTopEdgeChart r β w ∈ closedEuclideanSector β ↔ 0 ≤ w.im) := by
  by_cases heq : β = Real.pi
  · refine ⟨1, by norm_num, fun w _ ↦ ?_⟩
    subst β
    rw [closedEuclideanSector_eq_halfplanes hβ le_rfl]
    have him : (sectorTopEdgeChart r Real.pi w).im = w.im := by
      change (conePhase Real.pi * star w + sectorPolar r Real.pi).im = w.im
      simp only [Complex.add_im, Complex.mul_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, conePhase_re, conePhase_im, sectorPolar_im,
        Real.cos_pi, Real.sin_pi]
      ring
    simp only [Set.mem_ofPred_eq]
    rw [sectorTopEdgeChart_support, him]
    exact ⟨And.left, fun hw ↦ ⟨hw, neg_nonpos.mpr hw⟩⟩
  · have hβlt : β < Real.pi := lt_of_le_of_ne hβπ heq
    let V : Set ℂ := {w | 0 < (sectorTopEdgeChart r β w).im}
    have hV : IsOpen V := isOpen_lt continuous_const
      (Complex.continuous_im.comp (sectorTopEdgeChart r β).continuous)
    have h0 : (0 : ℂ) ∈ V := by
      change 0 < (sectorTopEdgeChart r β 0).im
      rw [sectorTopEdgeChart_zero, sectorPolar_im]
      exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hβ hβlt)
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0
    refine ⟨ε / 2, half_pos hε, fun w hw ↦ ?_⟩
    have hwV : w ∈ V := hεV (by
      rw [mem_ball, dist_zero_right]
      exact hw.trans_lt (half_lt_self hε))
    rw [closedEuclideanSector_eq_halfplanes hβ hβπ]
    simp only [Set.mem_ofPred_eq]
    rw [sectorTopEdgeChart_support]
    exact ⟨fun h ↦ neg_nonpos.mp h.2, fun h ↦ ⟨hwV.le, neg_nonpos.mpr h⟩⟩

end RepulsiveCoulomb
