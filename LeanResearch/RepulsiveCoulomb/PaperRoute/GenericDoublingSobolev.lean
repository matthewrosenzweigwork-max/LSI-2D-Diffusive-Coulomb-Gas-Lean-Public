import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevWeakMeasure
import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericSmoothStrongMean

/-!
# Actual C1 Sobolev producer from supplied global doubling and weak PI

The same arbitrary positive-finite-ball measure occurs throughout. All physical
C1 weak PI inputs are displayed; no Sobolev or maximal certificate is assumed.
The new doubling constant determines s = ceil D + 2 and kappa = s/(s-1).
The final normalization uses the supplied D's fourfold iterate, so the outer
energy is exactly the average on 11B and its loss is D^4, outside the root.
-/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem strong_sobolev_measure_form {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in ball c R, ENNReal.ofReal
      (‖f x - (⨍ z in ball c R, f z ∂μ)‖ ^ (2 * doublingSobolevKappa D)) ∂μ) ≤
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * doublingSobolevKappa D))) *
      (2 * ENNReal.ofReal ((16 : ℝ) ^ (2 * doublingSobolevKappa D))) *
      ENNReal.ofReal (doublingWeakSobolevBallFactor D P μ c R) *
        (ENNReal.ofReal (universalSmoothTruncationConstant ^ 2) *
          ∫⁻ x in ball c (11 * R), ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ) ^ doublingSobolevKappa D := by
  let σ := μ.restrict (ball c R)
  let ν := (μ).restrict (ball c (11 * R))
  let : IsFiniteMeasure σ := ⟨by simpa only [σ, Measure.restrict_apply_univ] using hμ.ball_lt_top c R⟩
  let : NeZero σ := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (hμ c R hR).1.ne' (by simpa [σ] using he)⟩
  have hκ : 1 ≤ doublingSobolevKappa D := (doublingSobolevKappa_gt_one D).le
  have hq : 1 ≤ 2 * doublingSobolevKappa D := by linarith
  have hfi : Integrable f σ := hμ.continuous_ball_integrable hf.continuous c R
  have hb : ∃ L U : ℝ, ∀ᵐ x ∂σ, L ≤ f x ∧ f x ≤ U := by
    obtain ⟨L, hL⟩ := (isCompact_closedBall c R).bddBelow_image hf.continuous.continuousOn
    obtain ⟨U, hU⟩ := (isCompact_closedBall c R).bddAbove_image hf.continuous.continuousOn
    refine ⟨L, U, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ⟨hL (mem_image_of_mem f (ball_subset_closedBall hx)),
      hU (mem_image_of_mem f (ball_subset_closedBall hx))⟩
  have hp (b : ℝ) : Integrable (fun x => ‖f x - b‖ ^ (2 * doublingSobolevKappa D)) σ :=
    hμ.continuous_ball_integrable
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * doublingSobolevKappa D)).comp
        (hf.continuous.sub continuous_const).norm) c R
  apply smooth_weak_to_strong_mean σ ν hf hfi hb hq hκ universalSmoothTruncationConstant_pos.le
    universalSmoothTruncationConstant_bound hp
  intro v hv t ht
  exact weak_sobolev_measure_form hD hμ hP v hv (hPI v hv) c hR ht


def doublingStrongUpgradeFactor (D : ℝ) : ℝ :=
  (2 * (2 : ℝ) ^ (2 * doublingSobolevKappa D)) * (2 * (16 : ℝ) ^ (2 * doublingSobolevKappa D)) *
    (universalSmoothTruncationConstant ^ 2) ^ doublingSobolevKappa D

def doublingStrongSobolevConstant (D P : ℝ) : ℝ := doublingStrongUpgradeFactor D * doublingWeakSobolevConstant D P

theorem doublingStrongUpgradeFactor_pos (D : ℝ) : 0 < doublingStrongUpgradeFactor D := by
  unfold doublingStrongUpgradeFactor
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)))
    (Real.rpow_pos_of_pos (sq_pos_of_pos universalSmoothTruncationConstant_pos) _)

theorem doublingStrongSobolevConstant_pos {D : ℝ} (hD : 1 ≤ D) {P : ℝ} (hP : 0 < P) :
    0 < doublingStrongSobolevConstant D P :=
  mul_pos (doublingStrongUpgradeFactor_pos D) (doublingWeakSobolevConstant_pos hD hP)

theorem ofReal_doublingStrongUpgradeFactor (D : ℝ) :
    ENNReal.ofReal (doublingStrongUpgradeFactor D) =
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * doublingSobolevKappa D))) *
      (2 * ENNReal.ofReal ((16 : ℝ) ^ (2 * doublingSobolevKappa D))) *
      ENNReal.ofReal ((universalSmoothTruncationConstant ^ 2) ^ doublingSobolevKappa D) := by
  unfold doublingStrongUpgradeFactor
  have hA : 0 ≤ 2 * (2 : ℝ) ^ (2 * doublingSobolevKappa D) := by positivity
  have hB : 0 ≤ 2 * (16 : ℝ) ^ (2 * doublingSobolevKappa D) := by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hA hB), ENNReal.ofReal_mul hA,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem strong_sobolev_of_poincare {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ^
      (2 * doublingSobolevKappa D) ∂μ) ≤
      doublingStrongSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
        (μ).real (ball c R) *
        ((∫ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂μ) /
          (μ).real (ball c R)) ^ doublingSobolevKappa D := by
  have hκ : 0 ≤ doublingSobolevKappa D := (lt_trans zero_lt_one (doublingSobolevKappa_gt_one D)).le
  let I := ∫ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg _)
  have hg : Continuous (fun x => ‖gradient f x‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hf.continuous_fderiv one_ne_zero).norm.pow 2
  have hi : ENNReal.ofReal I = ∫⁻ x in ball c (11 * R), ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (hμ.continuous_ball_integrable hg c _)
      (Eventually.of_forall (fun x => sq_nonneg _))
  have h := strong_sobolev_measure_form hD hμ hP hPI f hf c hR
  rw [← hi, ENNReal.mul_rpow_of_nonneg _ _ hκ,
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg universalSmoothTruncationConstant) hκ,
    ENNReal.ofReal_rpow_of_nonneg hI hκ] at h
  have he :
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * doublingSobolevKappa D))) *
      (2 * ENNReal.ofReal ((16 : ℝ) ^ (2 * doublingSobolevKappa D))) *
      ENNReal.ofReal (doublingWeakSobolevBallFactor D P μ c R) *
      (ENNReal.ofReal ((universalSmoothTruncationConstant ^ 2) ^ doublingSobolevKappa D) * ENNReal.ofReal (I ^ doublingSobolevKappa D)) =
      ENNReal.ofReal (doublingStrongUpgradeFactor D) *
        (ENNReal.ofReal (doublingWeakSobolevBallFactor D P μ c R) * ENNReal.ofReal (I ^ doublingSobolevKappa D)) := by
    rw [ofReal_doublingStrongUpgradeFactor]
    ring
  rw [he, ← ENNReal.ofReal_mul (doublingWeakSobolevBallFactor_nonneg hD.1 hP μ c hR.le),
    doublingWeakSobolevBallFactor_mul_energy D P μ c R hI,
    ← ENNReal.ofReal_mul (doublingStrongUpgradeFactor_pos D).le] at h
  have hrhs : doublingStrongUpgradeFactor D * (doublingWeakSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
      (μ).real (ball c R) * (I / (μ).real (ball c R)) ^ doublingSobolevKappa D) =
      doublingStrongSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
      (μ).real (ball c R) * (I / (μ).real (ball c R)) ^ doublingSobolevKappa D := by
    unfold doublingStrongSobolevConstant
    ring
  rw [hrhs] at h
  have hp : IntegrableOn (fun x => ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ^
      (2 * doublingSobolevKappa D)) (ball c R) (μ) :=
    hμ.continuous_ball_integrable
      ((Real.continuous_rpow_const (show 0 ≤ 2 * doublingSobolevKappa D by linarith)).comp
        (hf.continuous.sub continuous_const).norm) c R
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))] at h
  have hn : 0 ≤ doublingStrongSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
      (μ).real (ball c R) * (I / (μ).real (ball c R)) ^ doublingSobolevKappa D :=
    mul_nonneg (mul_nonneg (mul_nonneg (doublingStrongSobolevConstant_pos hD.1 hP).le
      (Real.rpow_nonneg hR.le _)) ENNReal.toReal_nonneg)
      (Real.rpow_nonneg (div_nonneg hI ENNReal.toReal_nonneg) _)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    ENNReal.toReal_ofReal hn] using ht


theorem energy_ratio_le_outer_average {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (g : ℂ → ℝ) (hgn : ∀ x, 0 ≤ g x) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball c (11 * R), g x ∂μ) / (μ).real (ball c R) ≤
      D ^ 4 *
        (⨍ x in ball c (11 * R), g x ∂μ) := by
  have hM : 0 < (μ).real (ball c R) :=
    ENNReal.toReal_pos (hμ c R hR).1.ne' (hμ.ball_lt_top c R).ne
  have hN : 0 < (μ).real (ball c (11 * R)) :=
    ENNReal.toReal_pos (hμ c _ (by positivity)).1.ne' (hμ.ball_lt_top c _).ne
  have hm := hD.real_ball_eleven_le hμ c hR
  have hI : 0 ≤ ∫ x in ball c (11 * R), g x ∂μ := integral_nonneg hgn
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (∫ x in ball c (11 * R), g x ∂μ) /
      (μ).real (ball c R) ≤
      D ^ 4 *
      (((μ).real (ball c (11 * R)))⁻¹ * ∫ x in ball c (11 * R), g x ∂μ)
  rw [mul_comm _ (∫ x in ball c (11 * R), g x ∂μ), ← div_eq_mul_inv, ← mul_div_assoc]
  apply (div_le_div_iff₀ hM hN).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm hI]

theorem strong_sobolev_average_moment {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ^
      (2 * doublingSobolevKappa D) ∂μ) ≤
      doublingStrongSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
        ((∫ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂μ) /
          (μ).real (ball c R)) ^ doublingSobolevKappa D := by
  have h := strong_sobolev_of_poincare hD hμ hP hPI f hf c hR
  have hM : 0 < (μ).real (ball c R) :=
    ENNReal.toReal_pos (hμ c R hR).1.ne' (hμ.ball_lt_top c R).ne
  rw [setAverage_eq, smul_eq_mul]
  change ((μ).real (ball c R))⁻¹ * _ ≤ _
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hM).mpr
  convert h using 1; ring


theorem generic_sobolev_moment_root {A C R E κ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hκ : 0 < κ)
    (h : A ≤ C * R ^ (2 * κ) * E ^ κ) :
    A ^ (1 / κ) ≤ C ^ (1 / κ) * R ^ 2 * E := by
  have ht := Real.rpow_le_rpow hA h (show 0 ≤ 1 / κ by positivity)
  have he1 : (2 * κ) * (1 / κ) = 2 := by field_simp
  have he2 : κ * (1 / κ) = 1 := by field_simp
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hR _)) (Real.rpow_nonneg hE _),
    Real.mul_rpow hC (Real.rpow_nonneg hR _), ← Real.rpow_mul hR,
    ← Real.rpow_mul hE, he1, he2, Real.rpow_two, Real.rpow_one] at ht
  exact ht

def doublingLocalSobolevConstant (D P : ℝ) : ℝ :=
  (doublingStrongSobolevConstant D P) ^ (1 / doublingSobolevKappa D) *
    D ^ 4

theorem doublingLocalSobolevConstant_pos {D : ℝ} (hD : 1 ≤ D) {P : ℝ} (hP : 0 < P) :
    0 < doublingLocalSobolevConstant D P :=
  mul_pos (Real.rpow_pos_of_pos (doublingStrongSobolevConstant_pos hD hP) _)
    (pow_pos (zero_lt_one.trans_le hD) _)

theorem strong_sobolev_squared_norm {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ^
      (2 * doublingSobolevKappa D) ∂μ) ^ (1 / doublingSobolevKappa D) ≤
      doublingLocalSobolevConstant D P * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂μ) := by
  have hκ : 0 < doublingSobolevKappa D := lt_trans zero_lt_one (doublingSobolevKappa_gt_one D)
  have h := generic_sobolev_moment_root
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (doublingStrongSobolevConstant_pos hD.1 hP).le hR.le
    (div_nonneg (integral_nonneg (fun x => sq_nonneg _)) ENNReal.toReal_nonneg) hκ
    (strong_sobolev_average_moment hD hμ hP hPI f hf c hR)
  have he := energy_ratio_le_outer_average hD hμ (fun x => ‖gradient f x‖ ^ 2)
    (fun x => sq_nonneg _) c hR
  apply h.trans
  calc
    _ ≤ (doublingStrongSobolevConstant D P) ^ (1 / doublingSobolevKappa D) * R ^ 2 *
        (D ^ 4 *
          (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (doublingStrongSobolevConstant_pos hD.1 hP).le _) (sq_nonneg R))
    _ = _ := by unfold doublingLocalSobolevConstant; ring


/-- Enlarge a physical energy average from 2B to 5B, using only the supplied D. -/
theorem sqrt_average_two_le_five {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ x, 0 ≤ g x)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (⨍ z in ball c (2 * r), g z ∂μ) ≤
      D * Real.sqrt (⨍ z in ball c (5 * r), g z ∂μ) := by
  have h2 : 0 < 2 * r := by positivity
  have h5 : 0 < 5 * r := by positivity
  have hm : μ.real (ball c (5 * r)) ≤ D ^ 2 * μ.real (ball c (2 * r)) := by
    have h := hD.real_ball_four_le hμ c h2
    exact (ENNReal.toReal_mono (hμ.ball_lt_top c (4 * (2 * r))).ne
      (measure_mono (ball_subset_ball (by linarith)))).trans h
  have hav := setAverage_nonneg_subset_bound_generic μ (ball_subset_ball (by linarith : 2 * r ≤ 5 * r))
    (hμ c _ h2).1.ne' (hμ c _ h2).2.ne (hμ c _ h5).1.ne' (hμ c _ h5).2.ne
    (hμ.continuous_ball_integrable hg c (5 * r)) hgn
  have hav' : (⨍ z in ball c (2 * r), g z ∂μ) ≤ D ^ 2 * (⨍ z in ball c (5 * r), g z ∂μ) :=
    hav.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ (hμ.real_ball_pos c h2)).mpr hm)
      (average_nonneg hgn))
  have hn : 0 ≤ D * Real.sqrt (⨍ z in ball c (5 * r), g z ∂μ) :=
    mul_nonneg (zero_le_one.trans hD.1) (Real.sqrt_nonneg _)
  apply (Real.sqrt_le_left hn).mpr
  simpa only [mul_pow, Real.sq_sqrt (average_nonneg hgn)] using hav'

/-- Actual physical dilation-2 weak PI can feed the dilation-5 proof with cost D. -/
theorem weak_poincare_five_of_two {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (2 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
      (P * D) * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂μ) := by
  have hg : Continuous (fun w => ‖gradient v w‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hv.continuous_fderiv one_ne_zero).norm.pow 2
  apply (hPI v hv z r hr).trans
  have h := mul_le_mul_of_nonneg_left
    (sqrt_average_two_le_five hD hμ _ hg (fun _ => sq_nonneg _) z hr) (mul_pos hP hr).le
  convert h using 1; ring

/-- Direct consumer for the new map-backed producer's actual dilation-2 PI. -/
theorem strong_sobolev_squared_norm_of_dilation_two {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (2 * r), ‖gradient v w‖ ^ 2 ∂μ))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ^
      (2 * doublingSobolevKappa D) ∂μ) ^ (1 / doublingSobolevKappa D) ≤
      doublingLocalSobolevConstant D (P * D) * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂μ) :=
  strong_sobolev_squared_norm hD hμ (mul_pos hP (zero_lt_one.trans_le hD.1))
    (weak_poincare_five_of_two hD hμ hP hPI) f hf c hR

end RepulsiveCoulomb.PaperRoute
