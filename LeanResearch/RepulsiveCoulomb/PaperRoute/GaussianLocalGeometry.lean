module

public import LeanResearch.RepulsiveCoulomb.PointGaussianCenterComparison
public import LeanResearch.RepulsiveCoulomb.PowerMeanComparison
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Calculus.Gradient

@[expose] public section

/-! Additive experimental source. Verification status is recorded separately in evidence. Gaussian local geometry from an actual
supplied raw strong Sobolev inequality, with an independent exponent κ.
The raw premise must be discharged by the new generic doubling/Sobolev route.
No old point Sobolev exponent, constant, or unconditional endpoint is selected. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- Actual new raw Sobolev input, uniform before each configuration is chosen.
The total-weight cap Q and the independently constructed exponent κ are distinct. -/
def UniformRawStrongSobolev (Q κ S : ℝ) : Prop :=
  ∀ (m : ℕ) (a : Fin m → ℝ), (∀ j, 0 ≤ a j) → ∀ (y : Fin m → ℂ),
    (∑ j, a j ≤ Q) → ∀ f : ℂ → ℝ, ContDiff ℝ 1 f → ∀ R : ℝ, 0 < R →
    (⨍ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂rawPointMeasure a y)‖ ^ (2 * κ)
        ∂rawPointMeasure a y) ^ (1 / κ) ≤
      S * R ^ 2 * (⨍ x in ball (0 : ℂ) (11 * R),
        ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y)

/-- A supplied configuration-uniform half-mass disk. The final original-input
route must produce this from the written normalization/tail argument. -/
def UniformHalfMassBall (γ Q R₀ : ℝ) : Prop :=
  ∀ (m : ℕ) (a : Fin m → ℝ) (y : Fin m → ℂ),
    (∀ j, 0 ≤ a j) → (∑ j, a j ≤ Q) →
      (1 / 2 : ENNReal) ≤ pointMeasure γ a y (ball (0 : ℂ) R₀)

def gaussianSobolevFactor (κ S : ℝ) : ℝ :=
  (2 * (2 : ℝ) ^ (2 * κ)) ^ (1 / κ) * S

theorem gaussianSobolevFactor_pos (κ : ℝ) {S : ℝ} (hS : 0 < S) :
    0 < gaussianSobolevFactor κ S :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) _)
    hS

theorem gaussian_strong_sobolev_squared_norm
    {m : ℕ} {γ κ S : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hκ : 1 < κ) (hS : 0 < S) (y : Fin m → ℂ)
    (hraw : ∀ f : ℂ → ℝ, ContDiff ℝ 1 f → ∀ R : ℝ, 0 < R →
      (⨍ x in ball (0 : ℂ) R,
        ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂rawPointMeasure a y)‖ ^ (2 * κ)
          ∂rawPointMeasure a y) ^ (1 / κ) ≤
        S * R ^ 2 * (⨍ x in ball (0 : ℂ) (11 * R),
          ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
      (2 * κ) ∂pointMeasure γ a y) ^ (1 / κ) ≤
      gaussianSobolevFactor κ S * Real.exp (61 * γ * R ^ 2) * R ^ 2 *
        (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by
  have hq : 1 ≤ 2 * κ := by linarith
  let T := 2 * (2 : ℝ) ^ (2 * κ)
  let D := Real.exp (γ * R ^ 2 / 2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hD : 1 ≤ D := Real.one_le_exp_iff.mpr (by nlinarith [sq_nonneg R])
  have hroot := rpow_compare_factor
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hT hD hκ.le
    (pointMeasure_raw_centered_moment_comparison hγ ha y hR hq f hf.continuous)
  have hs := hraw f hf R hR
  have hg : Continuous (fun x => ‖gradient f x‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hf.continuous_fderiv one_ne_zero).norm.pow 2
  have hgrad := (pointMeasure_raw_average_comparison hγ ha y (show 0 < 11 * R by positivity)
    (fun x => ‖gradient f x‖ ^ 2) hg (fun x => sq_nonneg _)).2
  have he : D * Real.exp (γ * (11 * R) ^ 2 / 2) = Real.exp (61 * γ * R ^ 2) := by
    dsimp [D]
    rw [← Real.exp_add]
    congr 1
    ring
  apply hroot.trans
  calc
    _ ≤ T ^ (1 / κ) * D *
        (S * R ^ 2 * (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (Real.rpow_nonneg hT _) (Real.exp_pos _).le)
    _ ≤ T ^ (1 / κ) * D *
        (S * R ^ 2 * (Real.exp (γ * (11 * R) ^ 2 / 2) *
          (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrad
        (mul_nonneg hS.le (sq_nonneg R)))
        (mul_nonneg (Real.rpow_nonneg hT _) (Real.exp_pos _).le)
    _ = (T ^ (1 / κ) * S) * (D * Real.exp (γ * (11 * R) ^ 2 / 2)) * R ^ 2 *
        (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by ring
    _ = _ := by rw [he]; rfl

theorem gaussian_sobolev_sqrt {A F b R E κ : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F) (hR : 0 ≤ R)
    (h : A ^ (1 / κ) ≤ F * Real.exp b * R ^ 2 * E) :
    A ^ (1 / (2 * κ)) ≤ Real.sqrt F * Real.exp (b / 2) * R * Real.sqrt E := by
  have ht := Real.sqrt_le_sqrt h
  have heA : Real.sqrt (A ^ (1 / κ)) = A ^ (1 / (2 * κ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hA]
    congr 1
    ring
  have heE : Real.sqrt (Real.exp b) = Real.exp (b / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hF (Real.exp_pos _).le) (sq_nonneg R)) E,
    Real.sqrt_mul (mul_nonneg hF (Real.exp_pos _).le) (R ^ 2), Real.sqrt_mul hF (Real.exp b),
    Real.sqrt_sq hR, heA, heE] at ht
  exact ht

def gaussianLocalConstant (γ κ S : ℝ) : ℝ :=
  1 + Real.sqrt (gaussianSobolevFactor κ S) + 61 * γ

theorem gaussianLocalConstant_pos {γ : ℝ} (hγ : 0 < γ) (κ S : ℝ) :
    0 < gaussianLocalConstant γ κ S := by
  unfold gaussianLocalConstant
  have := Real.sqrt_nonneg (gaussianSobolevFactor κ S)
  linarith

theorem gaussian_local_sobolev
    {m : ℕ} {γ κ S : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hκ : 1 < κ) (hS : 0 < S) (y : Fin m → ℂ)
    (hraw : ∀ f : ℂ → ℝ, ContDiff ℝ 1 f → ∀ R : ℝ, 0 < R →
      (⨍ x in ball (0 : ℂ) R,
        ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂rawPointMeasure a y)‖ ^ (2 * κ)
          ∂rawPointMeasure a y) ^ (1 / κ) ≤
        S * R ^ 2 * (⨍ x in ball (0 : ℂ) (11 * R),
          ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
      (2 * κ) ∂pointMeasure γ a y) ^ (1 / (2 * κ)) ≤
      gaussianLocalConstant γ κ S * Real.exp (gaussianLocalConstant γ κ S * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs := gaussian_strong_sobolev_squared_norm hγ ha hκ hS y hraw f hf hR0
  have h := gaussian_sobolev_sqrt (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (gaussianSobolevFactor_pos κ hS).le hR0.le hs
  have hC := gaussianLocalConstant_pos hγ κ S
  have hcf : Real.sqrt (gaussianSobolevFactor κ S) ≤ gaussianLocalConstant γ κ S := by
    unfold gaussianLocalConstant
    linarith
  have hce : 61 * γ / 2 ≤ gaussianLocalConstant γ κ S := by
    unfold gaussianLocalConstant
    have := Real.sqrt_nonneg (gaussianSobolevFactor κ S)
    linarith
  have he : Real.exp (61 * γ * R ^ 2 / 2) ≤ Real.exp (gaussianLocalConstant γ κ S * R ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hce (sq_nonneg R)])
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hcf he (Real.exp_pos _).le hC.le) hR0.le)
    (Real.sqrt_nonneg _))

theorem gaussian_local_poincare
    {m : ℕ} {γ κ S : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hκ : 1 < κ) (hS : 0 < S) (y : Fin m → ℂ)
    (hraw : ∀ f : ℂ → ℝ, ContDiff ℝ 1 f → ∀ R : ℝ, 0 < R →
      (⨍ x in ball (0 : ℂ) R,
        ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂rawPointMeasure a y)‖ ^ (2 * κ)
          ∂rawPointMeasure a y) ^ (1 / κ) ≤
        S * R ^ 2 * (⨍ x in ball (0 : ℂ) (11 * R),
          ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y))
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball (0 : ℂ) R, ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^ 2 ∂pointMeasure γ a y) ≤
      (gaussianSobolevFactor κ S * Real.exp (61 * γ * R ^ 2) * R ^ 2) *
        ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y := by
  let μ := (pointMeasure γ a y).restrict (ball (0 : ℂ) R)
  let u : ℂ → ℝ := fun x => f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)
  let M := (pointMeasure γ a y).real (ball (0 : ℂ) R)
  let N := (pointMeasure γ a y).real (ball (0 : ℂ) (11 * R))
  let I := ∫ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y
  let A := gaussianSobolevFactor κ S * Real.exp (61 * γ * R ^ 2) * R ^ 2
  letI := pointMeasure_isProbability hγ ha y
  letI : IsFiniteMeasure μ := inferInstance
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun η : Measure ℂ => η univ) h
    exact (pointMeasure_origin_ball_pos hγ ha y hR).ne' (by simpa [μ] using he)⟩
  have hu : Continuous u := hf.continuous.sub continuous_const
  have hs : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    pointMeasure_continuous_ball_integrable hγ ha y (hu.norm.pow 2) 0 R
  have hp : Integrable (fun x => ‖u x‖ ^ (2 * κ)) μ :=
    pointMeasure_continuous_ball_integrable hγ ha y
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * κ)).comp hu.norm) 0 R
  have hvar := (average_sq_le_average_rpow μ u hκ.le hs hp).trans
    (gaussian_strong_sobolev_squared_norm hγ ha hκ hS y hraw f hf hR)
  have h := mul_le_mul_of_nonneg_left hvar (show 0 ≤ M from ENNReal.toReal_nonneg)
  have hv : M * (⨍ x, ‖u x‖ ^ 2 ∂μ) = ∫ x in ball (0 : ℂ) R, ‖u x‖ ^ 2 ∂pointMeasure γ a y := by
    simpa only [smul_eq_mul] using measure_smul_setAverage (μ := pointMeasure γ a y)
      (fun x => ‖u x‖ ^ 2) (s := ball (0 : ℂ) R) (measure_ne_top _ _)
  rw [hv] at h
  have hN : 0 < N := ENNReal.toReal_pos
    (pointMeasure_origin_ball_pos hγ ha y (show 0 < 11 * R by positivity)).ne' (measure_ne_top _ _)
  have hMN : M / N ≤ 1 := (div_le_one hN).mpr
    (measureReal_mono (ball_subset_ball (by linarith)))
  have he : (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) = I / N := by
    rw [setAverage_eq, smul_eq_mul]
    change N⁻¹ * I = I / N
    ring
  rw [he] at h
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (gaussianSobolevFactor_pos κ hS).le (Real.exp_pos _).le) (sq_nonneg R)
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg _)
  apply h.trans
  change M * (A * (I / N)) ≤ A * I
  calc
    _ = A * (M / N) * I := by ring
    _ ≤ A * 1 * I := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMN hA) hI
    _ = _ := by ring

end RepulsiveCoulomb.PaperRoute
