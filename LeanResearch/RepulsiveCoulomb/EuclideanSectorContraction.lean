import LeanResearch.RepulsiveCoulomb.PointPolyhedralCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Sharp metric bounds for angular contraction of a flat sector. This is the
local deformation used in Bonk--Lang's negative-curvature step; existence and
global assembly of the disjoint sectors are separate obligations. -/
noncomputable section
namespace RepulsiveCoulomb

def sectorPolar (r θ : ℝ) : ℂ := (r : ℂ) * conePhase θ

theorem conePhase_re (θ : ℝ) : (conePhase θ).re = Real.cos θ := by
  simp [conePhase, Complex.exp_re]

theorem conePhase_im (θ : ℝ) : (conePhase θ).im = Real.sin θ := by
  simp [conePhase, Complex.exp_im]

theorem sectorPolar_re (r θ : ℝ) : (sectorPolar r θ).re = r * Real.cos θ := by
  simp [sectorPolar, Complex.mul_re, conePhase_re]

theorem sectorPolar_im (r θ : ℝ) : (sectorPolar r θ).im = r * Real.sin θ := by
  simp [sectorPolar, Complex.mul_im, conePhase_im]

theorem sectorPolar_distance_sq (r s θ φ : ℝ) :
    ‖sectorPolar r θ - sectorPolar s φ‖ ^ 2 =
      r ^ 2 + s ^ 2 - 2 * r * s * Real.cos (θ - φ) := by
  calc
    _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
        s ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) -
        2 * r * s * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        sectorPolar_re, sectorPolar_im]
      ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, Real.cos_sq_add_sin_sq, ← Real.cos_sub]; ring

theorem sectorPolar_distance_sq_half_angle (r s θ φ : ℝ) :
    ‖sectorPolar r θ - sectorPolar s φ‖ ^ 2 =
      (r - s) ^ 2 + 4 * r * s * Real.sin ((θ - φ) / 2) ^ 2 := by
  rw [sectorPolar_distance_sq]
  have hc := Real.cos_two_mul ((θ - φ) / 2)
  rw [show 2 * ((θ - φ) / 2) = θ - φ by ring] at hc
  have hs := Real.sin_sq_add_cos_sq ((θ - φ) / 2)
  have he : Real.cos (θ - φ) = 1 - 2 * Real.sin ((θ - φ) / 2) ^ 2 := by linarith
  rw [he]
  ring

theorem sin_angular_contraction {L t : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi / 2) :
    L * Real.sin t ≤ Real.sin (L * t) ∧ Real.sin (L * t) ≤ Real.sin t := by
  constructor
  · have h := strictConcaveOn_sin_Icc.concaveOn.2
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      (show t ∈ Set.Icc 0 Real.pi from ⟨ht0, by linarith [Real.pi_pos]⟩)
      (show 0 ≤ 1 - L from sub_nonneg.mpr hL1) hL0 (show (1 - L) + L = 1 by ring)
    simpa using h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) ht1
      (mul_le_of_le_one_left ht0 hL1)

theorem sin_sq_half_abs (t : ℝ) : Real.sin (t / 2) ^ 2 = Real.sin (|t| / 2) ^ 2 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, neg_div, Real.sin_neg, neg_sq]

theorem sectorPolar_distance_sq_abs_half (r s θ φ : ℝ) :
    ‖sectorPolar r θ - sectorPolar s φ‖ ^ 2 =
      (r - s) ^ 2 + 4 * r * s * Real.sin (|θ - φ| / 2) ^ 2 := by
  rw [sectorPolar_distance_sq_half_angle, sin_sq_half_abs]

theorem sectorPolar_angular_contraction {L r s θ φ : ℝ}
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : |θ - φ| ≤ Real.pi) :
    L * ‖sectorPolar r θ - sectorPolar s φ‖ ≤ ‖sectorPolar r (L * θ) - sectorPolar s (L * φ)‖ ∧
      ‖sectorPolar r (L * θ) - sectorPolar s (L * φ)‖ ≤ ‖sectorPolar r θ - sectorPolar s φ‖ := by
  let t := |θ - φ| / 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ Real.pi / 2 := by dsimp [t]; linarith
  have hsin := sin_angular_contraction hL0 hL1 ht0 ht1
  have hst : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith [Real.pi_pos]⟩
  have hsLt : 0 ≤ Real.sin (L * t) := Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg hL0 ht0, (mul_le_of_le_one_left ht0 hL1).trans (by linarith [Real.pi_pos])⟩
  have hsqlo : (L * Real.sin t) ^ 2 ≤ Real.sin (L * t) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (mul_nonneg hL0 hst) hsin.1
  have hsqhi : Real.sin (L * t) ^ 2 ≤ Real.sin t ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hsLt hsin.2
  have hM : 0 ≤ 4 * r * s := by positivity
  have hlo := mul_le_mul_of_nonneg_left hsqlo hM
  have hhi := mul_le_mul_of_nonneg_left hsqhi hM
  have hLsq : L ^ 2 ≤ 1 := by nlinarith
  have hrad := mul_le_mul_of_nonneg_right hLsq (sq_nonneg (r - s))
  have hA := sectorPolar_distance_sq_abs_half r s θ φ
  have hB := sectorPolar_distance_sq_abs_half r s (L * θ) (L * φ)
  have he : |L * θ - L * φ| / 2 = L * t := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hL0]
    dsimp [t]
    ring
  rw [he] at hB
  change ‖sectorPolar r θ - sectorPolar s φ‖ ^ 2 = (r - s) ^ 2 + 4 * r * s * Real.sin t ^ 2 at hA
  have hna := norm_nonneg (sectorPolar r θ - sectorPolar s φ)
  have hnb := norm_nonneg (sectorPolar r (L * θ) - sectorPolar s (L * φ))
  constructor
  · have hLA : 0 ≤ L * ‖sectorPolar r θ - sectorPolar s φ‖ := mul_nonneg hL0 hna
    have hAscale := congrArg (fun q : ℝ ↦ L ^ 2 * q) hA
    nlinarith
  · nlinarith

end RepulsiveCoulomb
