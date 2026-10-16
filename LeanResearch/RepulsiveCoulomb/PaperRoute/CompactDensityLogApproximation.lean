import LeanResearch.RepulsiveCoulomb.PaperRoute.LogFundamentalSolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Actual compact-product logarithmic integrability and explicit normalized
smooth bump mollification of signed bounded compact densities. The producer
preserves mass exactly, derives common support and pointwise bounds, proves
almost-everywhere convergence, and passes the genuine product log energy by
an integrable majorant. No Green or positivity conclusion is assumed. -/

noncomputable section
open MeasureTheory Set Metric Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace RepulsiveCoulomb.PaperRoute

def compactLogAbsKernel (R : ℝ) (p : ℂ × ℂ) : ℝ :=
  (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R).indicator
    (fun p => |-Real.log ‖p.1 - p.2‖|) p

theorem signedDensity_integrable_of_bounded_compact {η : ℂ → ℝ} {R B : ℝ}
    (hηm : Measurable η) (hηB : ∀ x, |η x| ≤ B)
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0) : Integrable η := by
  have hi : Integrable ((closedBall (0 : ℂ) R).indicator (fun _ => B)) := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  apply hi.mono' hηm.aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
    exact hηB x
  · rw [Set.indicator_of_notMem hx, hηR x hx, norm_zero]

theorem log_abs_le_positive_add_cap {z : ℂ} {R : ℝ} (hzR : ‖z‖ ≤ R) :
    |-Real.log ‖z‖| ≤ max (-Real.log ‖z‖) 0 + Real.log (max 1 R) := by
  have hC : 0 ≤ Real.log (max 1 R) := Real.log_nonneg (le_max_left _ _)
  have hP : 0 ≤ max (-Real.log ‖z‖) 0 := le_max_right _ _
  by_cases hz : z = 0
  · subst z
    simpa using hC
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hl : Real.log ‖z‖ ≤ Real.log (max 1 R) :=
    Real.log_le_log hr (hzR.trans (le_max_right _ _))
  have hp := le_max_left (-Real.log ‖z‖) 0
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual compact-product logarithmic integrability. The singular positive
part is controlled by a globally integrable convolution integrand; only the
negative logarithm needs the finite-volume compact product. -/
theorem compactLogAbsKernel_integrable (R : ℝ) :
    Integrable (compactLogAbsKernel R) (volume.prod volume) := by
  let K : Set ℂ := closedBall 0 R
  let b : ℂ → ℝ := K.indicator (fun _ => 1)
  let P : ℂ → ℝ := fun z => max (-Real.log ‖z‖) 0
  let C : ℝ := Real.log (max 1 (2 * R))
  have hK : IsCompact K := isCompact_closedBall _ _
  have hb : Integrable b := by
    apply (integrable_indicator_iff hK.measurableSet).mpr
    exact integrableOn_const hK.measure_lt_top.ne
  have hb0 (x : ℂ) : 0 ≤ b x := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hP0 (z : ℂ) : 0 ≤ P z := le_max_right _ _
  have hC0 : 0 ≤ C := Real.log_nonneg (le_max_left _ _)
  have hPos : Integrable (fun p : ℂ × ℂ => b p.2 * P (p.1-p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply', P] using
      hb.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) logPositive_integrable
  have hNeg : Integrable (fun p : ℂ × ℂ => C * (b p.1 * b p.2))
      (volume.prod volume) := (hb.mul_prod hb).const_mul C
  have hF0 (p : ℂ × ℂ) : 0 ≤ compactLogAbsKernel R p := by
    exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) p
  apply (hPos.add hNeg).mono'
    (show AEStronglyMeasurable (compactLogAbsKernel R) (volume.prod volume) from by
      apply Measurable.aestronglyMeasurable
      unfold compactLogAbsKernel
      apply Measurable.indicator _ (hK.measurableSet.prod hK.measurableSet)
      fun_prop)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 p)]
  by_cases hp : p ∈ K ×ˢ K
  · have hx : ‖p.1‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hp.1
    have hy : ‖p.2‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hp.2
    have hxy : ‖p.1-p.2‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by linarith)
    have he := log_abs_le_positive_add_cap hxy
    simpa only [compactLogAbsKernel, K, Set.indicator_of_mem hp,
      Pi.add_apply, b, Set.indicator_of_mem hp.1, Set.indicator_of_mem hp.2,
      one_mul, mul_one, P, C] using he
  · rw [show compactLogAbsKernel R p = 0 from Set.indicator_of_notMem hp _]
    exact add_nonneg (mul_nonneg (hb0 _) (hP0 _))
      (mul_nonneg hC0 (mul_nonneg (hb0 _) (hb0 _)))

theorem signedLogEnergy_integrable_of_bounded_compact
    {η : ℂ → ℝ} {R B : ℝ} (hηm : Measurable η) (hB : 0 ≤ B)
    (hηB : ∀ x, |η x| ≤ B)
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0) :
    Integrable (fun p : ℂ × ℂ => (-Real.log ‖p.1-p.2‖) * η p.1 * η p.2)
      (volume.prod volume) := by
  apply ((compactLogAbsKernel_integrable R).const_mul (B^2)).mono'
    (by fun_prop)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  by_cases hx : p.1 ∈ closedBall (0 : ℂ) R
  · by_cases hy : p.2 ∈ closedBall (0 : ℂ) R
    · have hh : |η p.1| * |η p.2| ≤ B * B :=
        mul_le_mul (hηB _) (hηB _) (abs_nonneg _) hB
      have hp : p ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := ⟨hx,hy⟩
      rw [compactLogAbsKernel, Set.indicator_of_mem hp]
      calc
        |-Real.log ‖p.1-p.2‖| * |η p.1| * |η p.2| =
          |-Real.log ‖p.1-p.2‖| * (|η p.1| * |η p.2|) := by ring
        _ ≤ |-Real.log ‖p.1-p.2‖| * (B * B) :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ = B^2 * |-Real.log ‖p.1-p.2‖| := by ring
    · have hp : p ∉ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := fun hp => hy hp.2
      simp only [hηR _ hy, abs_zero, mul_zero, compactLogAbsKernel,
        Set.indicator_of_notMem hp, le_refl]
  · have hp : p ∉ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := fun hp => hx hp.1
    simp only [hηR _ hx, abs_zero, mul_zero, zero_mul, compactLogAbsKernel,
      Set.indicator_of_notMem hp, le_refl]

theorem signedLogEnergy_norm_le_of_bounded_compact
    {η : ℂ → ℝ} {R B : ℝ} (hB : 0 ≤ B)
    (hηB : ∀ x, |η x| ≤ B)
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0) (p : ℂ × ℂ) :
    ‖(-Real.log ‖p.1-p.2‖) * η p.1 * η p.2‖ ≤ B^2 * compactLogAbsKernel R p := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  by_cases hx : p.1 ∈ closedBall (0 : ℂ) R
  · by_cases hy : p.2 ∈ closedBall (0 : ℂ) R
    · have hh : |η p.1| * |η p.2| ≤ B * B :=
        mul_le_mul (hηB _) (hηB _) (abs_nonneg _) hB
      have hp : p ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := ⟨hx,hy⟩
      rw [compactLogAbsKernel, Set.indicator_of_mem hp]
      calc
        |-Real.log ‖p.1-p.2‖| * |η p.1| * |η p.2| =
          |-Real.log ‖p.1-p.2‖| * (|η p.1| * |η p.2|) := by ring
        _ ≤ |-Real.log ‖p.1-p.2‖| * (B * B) :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ = B^2 * |-Real.log ‖p.1-p.2‖| := by ring
    · have hp : p ∉ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := fun hp => hy hp.2
      simp only [hηR _ hy, abs_zero, mul_zero, compactLogAbsKernel,
        Set.indicator_of_notMem hp, le_refl]
  · have hp : p ∉ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := fun hp => hx hp.1
    simp only [hηR _ hx, abs_zero, mul_zero, zero_mul, compactLogAbsKernel,
      Set.indicator_of_notMem hp, le_refl]



def compactSignedBump (n : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨logRegularizationScale n / 2, logRegularizationScale n,
    by have := logRegularizationScale_pos n; positivity,
    by have := logRegularizationScale_pos n; linarith⟩

def compactSignedKernel (n : ℕ) : ℂ → ℝ := (compactSignedBump n).normed volume

def compactSignedMollification (η : ℂ → ℝ) (n : ℕ) : ℂ → ℝ :=
  compactSignedKernel n ⋆[lsmul ℝ ℝ, volume] η

theorem compactSignedKernel_integrable (n : ℕ) : Integrable (compactSignedKernel n) :=
  (compactSignedBump n).integrable_normed

theorem compactSignedKernel_nonneg (n : ℕ) (x : ℂ) : 0 ≤ compactSignedKernel n x :=
  (compactSignedBump n).nonneg_normed x

theorem compactSignedKernel_integral (n : ℕ) : (∫ x : ℂ, compactSignedKernel n x) = 1 :=
  (compactSignedBump n).integral_normed

theorem compactSignedMollification_contDiff {η : ℂ → ℝ} (hη : Integrable η)
    (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (compactSignedMollification η n) := by
  exact (compactSignedBump n).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (compactSignedBump n).contDiff_normed hη.locallyIntegrable

theorem compactSignedMollification_integrable {η : ℂ → ℝ} (hη : Integrable η)
    (n : ℕ) : Integrable (compactSignedMollification η n) :=
  (compactSignedKernel_integrable n).integrable_convolution (lsmul ℝ ℝ) hη

/-- Literal mass preservation, including signed mass zero. -/
theorem compactSignedMollification_integral {η : ℂ → ℝ} (hη : Integrable η)
    (n : ℕ) : (∫ x : ℂ, compactSignedMollification η n x) = ∫ x : ℂ, η x := by
  have h := integral_convolution (lsmul ℝ ℝ) (compactSignedKernel_integrable n) hη
  simpa only [compactSignedMollification, compactSignedKernel_integral,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul] using h

theorem compactSignedMollification_ae_tendsto {η : ℂ → ℝ} (hη : Integrable η) :
    ∀ᵐ x : ℂ, Tendsto (fun n => compactSignedMollification η n x) atTop (𝓝 (η x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := compactSignedBump) (K := 2) ?_ ?_ hη.locallyIntegrable
  · exact logRegularizationScale_tendsto
  · filter_upwards with n
    change logRegularizationScale n ≤ 2 * (logRegularizationScale n/2)
    linarith

theorem compactSignedMollification_integrand_bound {η : ℂ → ℝ} {B : ℝ}
    (hηB : ∀ x, |η x| ≤ B) (n : ℕ) (x y : ℂ) :
    ‖compactSignedKernel n y * η (x-y)‖ ≤ B * compactSignedKernel n y := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (compactSignedKernel_nonneg n y)]
  simpa only [mul_comm B] using
    mul_le_mul_of_nonneg_left (hηB (x-y)) (compactSignedKernel_nonneg n y)

theorem compactSignedMollification_integrand_integrable {η : ℂ → ℝ} {B : ℝ}
    (hηm : Measurable η) (hηB : ∀ x, |η x| ≤ B) (n : ℕ) (x : ℂ) :
    Integrable (fun y : ℂ => compactSignedKernel n y * η (x-y)) := by
  apply ((compactSignedKernel_integrable n).const_mul B).mono'
    (by
      have hm : Measurable (compactSignedKernel n) :=
        (compactSignedBump n).continuous_normed.measurable
      fun_prop)
  exact Eventually.of_forall (compactSignedMollification_integrand_bound hηB n x)

theorem compactSignedMollification_abs_le {η : ℂ → ℝ} {B : ℝ}
    (hηm : Measurable η) (hηB : ∀ x, |η x| ≤ B) (n : ℕ) (x : ℂ) :
    |compactSignedMollification η n x| ≤ B := by
  change |∫ y : ℂ, compactSignedKernel n y * η (x-y)| ≤ B
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ y : ℂ, compactSignedKernel n y * η (x-y)‖ ≤
      ∫ y : ℂ, ‖compactSignedKernel n y * η (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℂ, B * compactSignedKernel n y := by
      apply integral_mono
        (compactSignedMollification_integrand_integrable hηm hηB n x).norm
        ((compactSignedKernel_integrable n).const_mul B)
      exact compactSignedMollification_integrand_bound hηB n x
    _ = B := by rw [integral_const_mul, compactSignedKernel_integral, mul_one]

/-- One fixed closed ball contains every mollified signed density. -/
theorem compactSignedMollification_eq_zero_outside {η : ℂ → ℝ} {R : ℝ}
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0)
    (n : ℕ) {x : ℂ} (hx : x ∉ closedBall (0 : ℂ) (R+1)) :
    compactSignedMollification η n x = 0 := by
  change (∫ y : ℂ, compactSignedKernel n y * η (x-y)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : compactSignedKernel n y = 0
  · simp only [hy, zero_mul, Pi.zero_apply]
  have hys : y ∈ Function.support ((compactSignedBump n).normed volume) := hy
  rw [(compactSignedBump n).support_normed_eq] at hys
  have hyn : ‖y‖ < logRegularizationScale n := by
    simpa only [mem_ball, dist_zero_right, compactSignedBump] using hys
  have hxn : R+1 < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hx
  have hxy : x-y ∉ closedBall (0 : ℂ) R := by
    intro hxy
    have hxy' : ‖x-y‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hxy
    have hn : ‖x‖ ≤ ‖x-y‖+‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-y) y
    have hscale := logRegularizationScale_le_one n
    linarith
  simp only [hηR (x-y) hxy, mul_zero, Pi.zero_apply]

theorem compactSignedMollification_hasCompactSupport {η : ℂ → ℝ} {R : ℝ}
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0) (n : ℕ) :
    HasCompactSupport (compactSignedMollification η n) := by
  apply exists_compact_iff_hasCompactSupport.mp
  exact ⟨closedBall (0 : ℂ) (R+1), isCompact_closedBall _ _,
    fun x hx => compactSignedMollification_eq_zero_outside hηR n hx⟩


theorem compactSignedMollification_logEnergy_tendsto {η : ℂ → ℝ} {R B : ℝ}
    (hηm : Measurable η) (hη : Integrable η) (hB : 0 ≤ B)
    (hηB : ∀ x, |η x| ≤ B)
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0) :
    Tendsto (fun n => ∫ p : ℂ × ℂ,
      (-Real.log ‖p.1-p.2‖) * compactSignedMollification η n p.1 * 
        compactSignedMollification η n p.2 ∂volume.prod volume) atTop
      (𝓝 (∫ p : ℂ × ℂ, (-Real.log ‖p.1-p.2‖) * η p.1 * η p.2
        ∂volume.prod volume)) := by
  let bound : ℂ × ℂ → ℝ := fun p => B^2 * compactLogAbsKernel (R+1) p
  have hbound : Integrable bound (volume.prod volume) :=
    (compactLogAbsKernel_integrable (R+1)).const_mul (B^2)
  have hbn (n : ℕ) : ∀ᵐ p : ℂ × ℂ ∂volume.prod volume,
      ‖(-Real.log ‖p.1-p.2‖) * compactSignedMollification η n p.1 * 
        compactSignedMollification η n p.2‖ ≤ bound p := by
    exact Eventually.of_forall (signedLogEnergy_norm_le_of_bounded_compact hB
      (compactSignedMollification_abs_le hηm hηB n)
      (fun x hx => compactSignedMollification_eq_zero_outside hηR n hx))
  have hae := compactSignedMollification_ae_tendsto hη
  have hf : ∀ᵐ p : ℂ × ℂ ∂volume.prod volume,
      Tendsto (fun n => compactSignedMollification η n p.1) atTop (𝓝 (η p.1)) :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae hae
  have hs : ∀ᵐ p : ℂ × ℂ ∂volume.prod volume,
      Tendsto (fun n => compactSignedMollification η n p.2) atTop (𝓝 (η p.2)) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae hae
  have hlim : ∀ᵐ p : ℂ × ℂ ∂volume.prod volume,
      Tendsto (fun n => (-Real.log ‖p.1-p.2‖) * 
        compactSignedMollification η n p.1 * compactSignedMollification η n p.2)
        atTop (𝓝 ((-Real.log ‖p.1-p.2‖) * η p.1 * η p.2)) := by
    filter_upwards [hf,hs] with p hp hq
    exact (tendsto_const_nhds.mul hp).mul hq
  exact tendsto_integral_of_dominated_convergence bound
    (fun n => by
      have hm : Measurable (compactSignedMollification η n) :=
        (compactSignedMollification_contDiff hη n).continuous.measurable
      fun_prop)
    hbound hbn hlim



end RepulsiveCoulomb.PaperRoute
