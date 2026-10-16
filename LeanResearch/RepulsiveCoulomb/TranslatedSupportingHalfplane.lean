module

public import LeanResearch.RepulsiveCoulomb.MetricRelativeHalfDiskPatchExtension
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleInteriorGeometry

@[expose] public section

/-! Pure Euclidean supporting geometry for the compact top. The supporting
set is the halfplane on the inward side of the adjacent old edge. It is not
the entire wedge: every positive-r top point is interior to this halfplane,
while the moving compact-edge endpoint is on its boundary. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem conePhase_neg_mul_self (stripAngle : ℝ) : conePhase (-stripAngle) * conePhase stripAngle = 1 := by
  unfold conePhase
  rw [← Complex.exp_add]
  have hz : ((-stripAngle : ℝ) : ℂ) * Complex.I + (stripAngle : ℂ) * Complex.I = 0 := by
    push_cast
    ring
  rw [hz, Complex.exp_zero]

/-- Adjacent-edge coordinate, pointing backward along the old compact edge.
Its imaginary direction points into the source strip. -/
def translatedSupportingRigid (stripAngle s : ℝ) : ℂ ≃ᵢ ℂ := by
  let v := conePhase stripAngle
  let w := conePhase (-stripAngle)
  have hwv : w * v = 1 := conePhase_neg_mul_self stripAngle
  have hvw : v * w = 1 := by rw [mul_comm]; exact hwv
  let F : ℂ → ℂ := fun z ↦ (s : ℂ) - w * z
  let G : ℂ → ℂ := fun z ↦ v * ((s : ℂ) - z)
  refine { toFun := F, invFun := G, left_inv := ?_, right_inv := ?_, isometry_toFun := ?_ }
  · intro z
    change v * ((s : ℂ) - ((s : ℂ) - w * z)) = z
    rw [sub_sub_cancel, ← mul_assoc, hvw, one_mul]
  · intro z
    change (s : ℂ) - w * (v * ((s : ℂ) - z)) = z
    rw [← mul_assoc, hwv, one_mul, sub_sub_cancel]
  · apply Isometry.of_dist_eq
    intro z x
    rw [dist_eq_norm, dist_eq_norm]
    change ‖((s : ℂ) - w * z) - ((s : ℂ) - w * x)‖ = ‖z - x‖
    rw [show ((s : ℂ) - w * z) - ((s : ℂ) - w * x) = w * (x - z) by ring,
      norm_mul, conePhase_norm, one_mul, norm_sub_rev]

/-- Exact arclength coordinate formula, valid on the whole source plane. -/
theorem translatedSupportingRigid_sheared (stripAngle s r u : ℝ) :
    translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) r u) =
      ((s - u : ℝ) : ℂ) - (r : ℂ) * conePhase (-stripAngle) := by
  change (s : ℂ) - conePhase (-stripAngle) * ((r : ℂ) + (u : ℂ) * conePhase stripAngle) = _
  rw [mul_add, show conePhase (-stripAngle) * ((u : ℂ) * conePhase stripAngle) = (u : ℂ) by
    calc
      conePhase (-stripAngle) * ((u : ℂ) * conePhase stripAngle) =
          (u : ℂ) * (conePhase (-stripAngle) * conePhase stripAngle) := by ring
      _ = (u : ℂ) := by rw [conePhase_neg_mul_self, mul_one]]
  push_cast
  ring

@[simp] theorem translatedSupportingRigid_top_origin (stripAngle s : ℝ) :
    translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) 0 s) = 0 := by
  rw [translatedSupportingRigid_sheared]
  simp

theorem translatedSupportingRigid_sheared_im (stripAngle s r u : ℝ) :
    (translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) r u)).im = r * Real.sin stripAngle := by
  rw [translatedSupportingRigid_sheared]
  simp [Complex.mul_im, conePhase_im, Real.sin_neg]

/-- Literal supporting halfplane for the adjacent edge. -/
def translatedSupportingHalfplane (stripAngle : ℝ) : Set ℂ :=
  {z | 0 ≤ Real.sin stripAngle * z.re - Real.cos stripAngle * z.im}

theorem translatedSupportingHalfplane_eq_rigid (stripAngle s : ℝ) :
    translatedSupportingHalfplane stripAngle = rigidUpperHalfplane (translatedSupportingRigid stripAngle s) := by
  ext z
  change (0 ≤ Real.sin stripAngle * z.re - Real.cos stripAngle * z.im) ↔
    (0 ≤ ((s : ℂ) - conePhase (-stripAngle) * z).im)
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    conePhase_re, conePhase_im, Real.cos_neg, Real.sin_neg]
  constructor <;> intro h <;> linarith

theorem translatedSupportingHalfplane_convex (stripAngle : ℝ) :
    Convex ℝ (translatedSupportingHalfplane stripAngle) := by
  intro x hx z hz a b ha hb hab
  change 0 ≤ Real.sin stripAngle * (a • x + b • z).re - Real.cos stripAngle * (a • x + b • z).im
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  have h : 0 ≤ a * (Real.sin stripAngle * x.re - Real.cos stripAngle * x.im) +
      b * (Real.sin stripAngle * z.re - Real.cos stripAngle * z.im) :=
    add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hz)
  nlinarith

theorem flatShearedRectangle_subset_translatedSupportingHalfplane
    {stripAngle : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (R s : ℝ) :
    flatShearedRectangle (conePhase stripAngle) R s ⊆ translatedSupportingHalfplane stripAngle := by
  rw [translatedSupportingHalfplane_eq_rigid stripAngle s]
  rintro z ⟨r, hr, u, hu, rfl⟩
  change 0 ≤ (translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) r u)).im
  rw [translatedSupportingRigid_sheared_im]
  exact mul_nonneg hr.1 (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).le

/-- Every positive longitudinal top point is genuinely interior to the
supporting halfplane. This is false at r = 0, where the halfdisk theorem is used. -/
theorem translatedSupportingHalfplane_interior_positive
    {stripAngle r : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hr : 0 < r) (u : ℝ) :
    flatShearedPoint (conePhase stripAngle) r u ∈ interior (translatedSupportingHalfplane stripAngle) := by
  let U : Set ℂ := {z | 0 < Real.sin stripAngle * z.re - Real.cos stripAngle * z.im}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hUH : U ⊆ translatedSupportingHalfplane stripAngle := by
    intro z hz
    change 0 ≤ Real.sin stripAngle * z.re - Real.cos stripAngle * z.im
    exact (show 0 < Real.sin stripAngle * z.re - Real.cos stripAngle * z.im from hz).le
  apply interior_mono hUH
  rw [hU.interior_eq]
  change 0 < Real.sin stripAngle * (flatShearedPoint (conePhase stripAngle) r u).re -
    Real.cos stripAngle * (flatShearedPoint (conePhase stripAngle) r u).im
  simp only [flatShearedPoint, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, zero_add, add_zero, conePhase_re, conePhase_im]
  nlinarith [mul_pos hr (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi)]

end RepulsiveCoulomb
