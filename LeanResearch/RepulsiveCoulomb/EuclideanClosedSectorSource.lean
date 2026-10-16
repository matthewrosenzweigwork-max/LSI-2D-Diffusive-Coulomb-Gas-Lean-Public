module

public import LeanResearch.RepulsiveCoulomb.PointRetainedCappedSectorSeed
public import LeanResearch.RepulsiveCoulomb.PointRadialFrontClosedExtension
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Literal source geometry for closed sectors,
including width pi. These are ordinary Euclidean facts and contain no target
map, continuation, curvature, or first-contact premise. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A short positive sector is the intersection of its two closed supporting
halfplanes. The halfplane endpoint beta = pi is included. -/
theorem closedEuclideanSector_eq_halfplanes {β : ℝ} (hβ : 0 < β)
    (hβπ : β ≤ Real.pi) :
    closedEuclideanSector β =
      {z : ℂ | 0 ≤ z.im ∧ Real.cos β * z.im - Real.sin β * z.re ≤ 0} := by
  ext z
  have hid : ‖z‖ * Real.sin (Complex.arg z - β) =
      Real.cos β * z.im - Real.sin β * z.re := by
    calc
      _ = (‖z‖ * Real.sin (Complex.arg z)) * Real.cos β -
          (‖z‖ * Real.cos (Complex.arg z)) * Real.sin β := by
            rw [Real.sin_sub]
            ring
      _ = _ := by rw [Complex.norm_mul_sin_arg, Complex.norm_mul_cos_arg]; ring
  constructor
  · intro hz
    refine ⟨Complex.arg_nonneg_iff.mp hz.1, ?_⟩
    rw [← hid]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (sub_nonpos.mpr hz.2) (by linarith [hz.1]))
  · rintro ⟨him, hside⟩
    refine ⟨Complex.arg_nonneg_iff.mpr him, ?_⟩
    by_cases hz : z = 0
    · simp [hz, hβ.le]
    · by_contra hn
      have hlt : β < Complex.arg z := lt_of_not_ge hn
      have hsin : 0 < Real.sin (Complex.arg z - β) :=
        Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt) (by linarith [Complex.arg_le_pi z])
      have hp := mul_pos (norm_pos_iff.mpr hz) hsin
      rw [hid] at hp
      exact (not_lt_of_ge hside) hp

theorem closedEuclideanSector_convex {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    Convex ℝ (closedEuclideanSector β) := by
  rw [closedEuclideanSector_eq_halfplanes hβ hβπ]
  intro x hx z hz a b ha hb hab
  change 0 ≤ (a • x + b • z).im ∧
    Real.cos β * (a • x + b • z).im - Real.sin β * (a • x + b • z).re ≤ 0
  simp only [Complex.add_im, Complex.smul_im, Complex.add_re, Complex.smul_re, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hz.1), ?_⟩
  have h := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.2)
    (mul_nonpos_of_nonneg_of_nonpos hb hz.2)
  nlinarith

theorem closedEuclideanSector_isClosed {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    IsClosed (closedEuclideanSector β) := by
  rw [closedEuclideanSector_eq_halfplanes hβ hβπ]
  exact (isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le (show Continuous (fun z : ℂ ↦ Real.cos β * z.im - Real.sin β * z.re) from by fun_prop) continuous_const)

theorem closedEuclideanSector_nonneg_smul {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    {z : ℂ} (hz : z ∈ closedEuclideanSector β) {t : ℝ} (ht : 0 ≤ t) :
    t • z ∈ closedEuclideanSector β := by
  rw [closedEuclideanSector_eq_halfplanes hβ hβπ] at hz ⊢
  change 0 ≤ (t • z).im ∧
    Real.cos β * (t • z).im - Real.sin β * (t • z).re ≤ 0
  simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul]
  refine ⟨mul_nonneg ht hz.1, ?_⟩
  have h := mul_nonpos_of_nonneg_of_nonpos ht hz.2
  nlinarith

/-- The bounded sector source agrees literally with the generic radial
truncation used by the compact-front extension. -/
theorem retainedFlatSectorDisk_eq_radialTruncation (β R : ℝ) :
    retainedFlatSectorDisk β R = flatRadialTruncation (closedEuclideanSector β) R := by
  ext z
  simp only [retainedFlatSectorDisk, flatRadialTruncation, mem_inter_iff,
    mem_setOf_eq, mem_closedBall, dist_zero_right]

theorem retainedFlatSectorDisk_interior_nonempty {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 < R) :
    (interior (retainedFlatSectorDisk β R)).Nonempty := by
  let V : Set ℂ := {z | 0 < z.im ∧
    Real.cos β * z.im - Real.sin β * z.re < 0 ∧ ‖z‖ < R}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      ((isOpen_lt (show Continuous (fun z : ℂ ↦ Real.cos β * z.im - Real.sin β * z.re) from by fun_prop) continuous_const).inter
        (isOpen_lt continuous_norm continuous_const))
  have hVK : V ⊆ retainedFlatSectorDisk β R := by
    intro z hz
    refine ⟨?_, hz.2.2.le⟩
    rw [closedEuclideanSector_eq_halfplanes hβ hβπ]
    exact ⟨hz.1.le, hz.2.1.le⟩
  let q := sectorPolar (R / 2) (β / 2)
  have hsin : 0 < Real.sin (β / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (half_pos hβ) (by linarith [Real.pi_pos])
  have hside : Real.cos β * q.im - Real.sin β * q.re =
      -(R / 2 * Real.sin (β / 2)) := by
    change Real.cos β * (sectorPolar (R / 2) (β / 2)).im -
      Real.sin β * (sectorPolar (R / 2) (β / 2)).re = _
    rw [sectorPolar_im, sectorPolar_re]
    have hh := Real.sin_sub (β / 2) β
    rw [show β / 2 - β = -(β / 2) by ring, Real.sin_neg] at hh
    nlinarith
  have hqV : q ∈ V := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 < (sectorPolar (R / 2) (β / 2)).im
      rw [sectorPolar_im]
      exact mul_pos (half_pos hR) hsin
    · rw [hside]
      exact neg_neg_of_pos (mul_pos (half_pos hR) hsin)
    · rw [show q = sectorPolar (R / 2) (β / 2) from rfl, sectorPolar_norm (half_pos hR).le]
      exact half_lt_self hR
  exact ⟨q, interior_mono hVK (by simpa only [hV.interior_eq] using hqV)⟩

end RepulsiveCoulomb
