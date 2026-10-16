import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift

/-! Concrete branch-cut avoidance and one-sided argument limits for the ratio
(z−iε)/(z+iε). This is the signed local-jump calculation for an actual normal
segment crossing. The geometric normal-segment exclusion is supplied by a
separate actual compact-separation construction, not inferred here.
Records-only phase-five candidate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def normalSegmentRatio (ε : ℝ) (z : ℂ) : ℂ :=
  (z - (ε : ℂ) * Complex.I) / (z + (ε : ℂ) * Complex.I)

theorem normalSegmentRatio_re (ε : ℝ) (z : ℂ) :
    (normalSegmentRatio ε z).re =
      (z.re ^ 2 + z.im ^ 2 - ε ^ 2) / (z.re ^ 2 + (z.im + ε) ^ 2) := by
  simp only [normalSegmentRatio, Complex.div_re, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, Complex.normSq_apply]
  ring

theorem normalSegmentRatio_im (ε : ℝ) (z : ℂ) :
    (normalSegmentRatio ε z).im =
      -(2 * ε * z.re) / (z.re ^ 2 + (z.im + ε) ^ 2) := by
  simp only [normalSegmentRatio, Complex.div_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, Complex.normSq_apply]
  ring

theorem normalSegmentRatio_im_neg {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.re) :
    (normalSegmentRatio ε z).im < 0 := by
  rw [normalSegmentRatio_im]
  have hd : 0 < z.re ^ 2 + (z.im + ε) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hd

theorem normalSegmentRatio_im_pos {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : z.re < 0) :
    0 < (normalSegmentRatio ε z).im := by
  rw [normalSegmentRatio_im]
  have hd : 0 < z.re ^ 2 + (z.im + ε) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hz.ne) (sq_nonneg _)
  exact div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) hz)) hd

/-- If the actual point is not on the closed normal segment, its ratio avoids
the negative-real branch cut. The convenient metric formulation handles all
points on the normal line outside the chosen segment. -/
theorem normalSegmentRatio_mem_slitPlane {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (haway : z.re = 0 → ε < ‖z‖) : normalSegmentRatio ε z ∈ Complex.slitPlane := by
  by_cases hz : z.re = 0
  · have hdist := haway hz
    have hnorm : ‖z‖ ^ 2 = z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hz]
      ring
    have hnum : 0 < z.im ^ 2 - ε ^ 2 := by nlinarith [norm_nonneg z]
    have hden : z.im + ε ≠ 0 := by
      intro heq
      nlinarith
    apply Or.inl
    rw [normalSegmentRatio_re, hz, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    exact div_pos hnum (by simpa only [zero_add] using sq_pos_of_ne_zero hden)
  · apply Or.inr
    rw [normalSegmentRatio_im]
    have hnum : -(2 * ε * z.re) ≠ 0 := neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) hε.ne') hz)
    have hden : 0 < z.re ^ 2 + (z.im + ε) ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hz) (sq_nonneg _)
    exact div_ne_zero hnum hden.ne'

@[simp] theorem normalSegmentRatio_zero {ε : ℝ} (hε : ε ≠ 0) :
    normalSegmentRatio ε 0 = -1 := by
  have he : (ε : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hε) Complex.I_ne_zero
  simp [normalSegmentRatio, he]

theorem normalSegmentRatio_continuousAt_zero {ε : ℝ} (hε : ε ≠ 0) :
    ContinuousAt (normalSegmentRatio ε) 0 := by
  unfold normalSegmentRatio
  exact (continuousAt_id.sub continuousAt_const).div
    (continuousAt_id.add continuousAt_const) (by
      simpa using mul_ne_zero (Complex.ofReal_ne_zero.mpr hε) Complex.I_ne_zero)

/-- Approaching the crossing from the right, the actual principal argument
of the ratio converges to −π. -/
theorem normalSegmentRatio_arg_tendsto_right {X : Type*} {l : Filter X}
    {f : X → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : Tendsto f l (𝓝 0)) (hside : ∀ᶠ x in l, 0 < (f x).re) :
    Tendsto (fun x => Complex.arg (normalSegmentRatio ε (f x))) l (𝓝 (-Real.pi)) := by
  have hratio : Tendsto (fun x => normalSegmentRatio ε (f x)) l (𝓝 (-1 : ℂ)) := by
    simpa only [normalSegmentRatio_zero hε.ne', Function.comp_def] using
      (normalSegmentRatio_continuousAt_zero hε.ne').tendsto.comp hf
  apply (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨hratio, hside.mono (fun x hx => normalSegmentRatio_im_neg hε hx)⟩

/-- Approaching the crossing from the left, the actual principal argument
of the ratio converges to +π. -/
theorem normalSegmentRatio_arg_tendsto_left {X : Type*} {l : Filter X}
    {f : X → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : Tendsto f l (𝓝 0)) (hside : ∀ᶠ x in l, (f x).re < 0) :
    Tendsto (fun x => Complex.arg (normalSegmentRatio ε (f x))) l (𝓝 Real.pi) := by
  have hratio : Tendsto (fun x => normalSegmentRatio ε (f x)) l (𝓝 (-1 : ℂ)) := by
    simpa only [normalSegmentRatio_zero hε.ne', Function.comp_def] using
      (normalSegmentRatio_continuousAt_zero hε.ne').tendsto.comp hf
  apply (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨hratio, hside.mono (fun x hx => (normalSegmentRatio_im_pos hε hx).le)⟩

end RepulsiveCoulomb
