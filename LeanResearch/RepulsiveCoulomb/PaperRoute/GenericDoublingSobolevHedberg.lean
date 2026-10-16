module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevEnergy
public import LeanResearch.RepulsiveCoulomb.DyadicHedberg

@[expose] public section

/-! Actual Hedberg split and pointwise oscillation from supplied global doubling
and the displayed weak PI. The exponent is determined by the new D alone. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem localMaximalEnergy_sqrt_average_bound {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {c x : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ ball c R) (g : ℂ → ℝ) (hg : Continuous g)
    (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ) ≤
      Real.sqrt (doublingLocalMaximalEnergy μ c R g x).toReal := by
  rw [doublingMeanRadius_energy]
  exact Real.sqrt_le_sqrt (hμ.localMaximalEnergy_average_bound hR hx g hg hgn n)

theorem localEnergy_scaled_mean_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (1 / 2 : ℝ) ^ n * Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ) ≤
      Real.sqrt (doublingLocalEnergy μ c R g) *
        ((2 : ℝ) ^ ((doublingDimension D : ℝ) - 1)) ^ n := by
  rw [doublingMeanRadius_energy]
  exact hD.local_energy_scaled_bound hμ hR hx g hg hgn n

theorem generic_hedberg_quotient_eq_power {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : 0 < t) (ht1 : t < 1) :
    A / (A / B) ^ t = A ^ (1 - t) * B ^ t := by
  by_cases ha : A = 0
  · simp [ha, Real.zero_rpow (by linarith : 1 - t ≠ 0)]
  by_cases hb : B = 0
  · simp [hb, Real.zero_rpow ht.ne']
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
  rw [Real.div_rpow hA hB, div_div_eq_mul_div, Real.rpow_sub hAp, Real.rpow_one]
  ring

theorem doubling_hedberg_sqrt_quotient_eq_power (D : ℝ) {M E : ℝ}
    (hM : 0 ≤ M) (hE : 0 ≤ E) :
    Real.sqrt M / (Real.sqrt M / Real.sqrt E) ^ (1 / (doublingDimension D : ℝ)) =
      M ^ (1 / (2 * doublingSobolevKappa D)) * E ^ doublingSobolevGain D := by
  have hs := doublingDimension_real_ge_two D
  have hs0 : 0 < (doublingDimension D : ℝ) := by linarith
  have ht : 0 < 1 / (doublingDimension D : ℝ) := by positivity
  have ht1 : 1 / (doublingDimension D : ℝ) < 1 := (div_lt_one hs0).mpr (by linarith)
  rw [generic_hedberg_quotient_eq_power (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ht ht1,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hM, ← Real.rpow_mul hE]
  congr 1
  · congr 1
    unfold doublingSobolevKappa
    field_simp
  · congr 1
    unfold doublingSobolevGain
    field_simp

def doublingPoincareSeries (μ : Measure ℂ)
    (R : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
    Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ))

theorem poincareSeries_hedberg_pos {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hE : 0 < doublingLocalEnergy μ c R g)
    (hM : 0 < (doublingLocalMaximalEnergy μ c R g x).toReal) :
    doublingPoincareSeries μ R g x ≤ ENNReal.ofReal
      (5 * Real.sqrt (doublingLocalMaximalEnergy μ c R g x).toReal /
        (Real.sqrt (doublingLocalMaximalEnergy μ c R g x).toReal /
          Real.sqrt (doublingLocalEnergy μ c R g)) ^ (1 / (doublingDimension D : ℝ))) := by
  apply dyadic_series_hedberg (Real.sqrt_pos.mpr hM) (Real.sqrt_pos.mpr hE) (doublingDimension_real_ge_two D)
  · intro n
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (localMaximalEnergy_sqrt_average_bound hμ hR hx g hg hgn n)
      (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity)
  · intro n
    exact ENNReal.ofReal_le_ofReal (localEnergy_scaled_mean_bound hD hμ hR hx g hg hgn n)

theorem poincareSeries_zero_of_energy_zero {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hE : doublingLocalEnergy μ c R g = 0) : doublingPoincareSeries μ R g x = 0 := by
  apply dyadic_series_zero_of_zero_bound
  intro n
  have h := ENNReal.ofReal_le_ofReal (localEnergy_scaled_mean_bound hD hμ hR hx g hg hgn n)
  simpa only [hE, Real.sqrt_zero, zero_mul, ENNReal.ofReal_zero] using h

theorem poincareSeries_zero_of_maximal_zero {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hM : (doublingLocalMaximalEnergy μ c R g x).toReal = 0) : doublingPoincareSeries μ R g x = 0 := by
  apply dyadic_series_zero_of_zero_bound
  intro n
  have h := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (localMaximalEnergy_sqrt_average_bound hμ hR hx g hg hgn n)
    (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity))
  simpa only [hM, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] using h


theorem poincareSeries_hedberg {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) :
    doublingPoincareSeries μ R g x ≤ ENNReal.ofReal
      (5 * Real.sqrt (doublingLocalMaximalEnergy μ c R g x).toReal /
        (Real.sqrt (doublingLocalMaximalEnergy μ c R g x).toReal /
          Real.sqrt (doublingLocalEnergy μ c R g)) ^ (1 / (doublingDimension D : ℝ))) := by
  by_cases hE : doublingLocalEnergy μ c R g = 0
  · rw [poincareSeries_zero_of_energy_zero hD hμ hR hx g hg hgn hE]
    exact bot_le
  by_cases hM : (doublingLocalMaximalEnergy μ c R g x).toReal = 0
  · rw [poincareSeries_zero_of_maximal_zero hμ hR hx g hg hgn hM]
    exact bot_le
  exact poincareSeries_hedberg_pos hD hμ hR hx g hg hgn
    (lt_of_le_of_ne (doublingLocalEnergy_nonneg μ c R g hgn) (Ne.symm hE))
    (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM))

theorem poincareSeries_lt_top {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) :
    doublingPoincareSeries μ R g x < ⊤ :=
  (poincareSeries_hedberg hD hμ hR hx g hg hgn).trans_lt ENNReal.ofReal_lt_top

theorem oscillation_le_series {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 ≤ P)
    (f g : ℂ → ℝ) (hf : Continuous f)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂μ))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ≤
      ENNReal.ofReal (2 * R * P * (D + D ^ 2)) *
        doublingPoincareSeries μ R g x := by
  have h := hD.poincare_chain hμ f g hf hPI c hR hx
  let S := doublingPoincareSeries μ R g x
  have he (n : ℕ) : D *
      (P * doublingMeanRadius (2 * R) n *
        Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ)) =
      (2 * R * P * D) * ((1 / 2 : ℝ) ^ n *
        Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ)) := by
    unfold doublingMeanRadius
    ring
  have hD : 0 ≤ 2 * R * P * D := by
    have := (zero_le_one.trans hD.1)
    positivity
  have hA : 0 ≤ 2 * R * P * D ^ 2 := by
    have := (sq_nonneg D)
    positivity
  simp_rw [he, ENNReal.ofReal_mul hD] at h
  rw [ENNReal.tsum_mul_left] at h
  have hzero : ENNReal.ofReal (Real.sqrt (⨍ z in ball x (10 * R), g z ∂μ)) ≤ S := by
    have hh := ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
      Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ))) 0
    simpa only [S, doublingPoincareSeries, doublingMeanRadius, pow_zero, one_mul, show 5 * (2 * R) = 10 * R by ring] using hh
  have hi : ENNReal.ofReal (D ^ 2 *
      (P * (2 * R) * Real.sqrt (⨍ z in ball x (10 * R), g z ∂μ))) ≤
      ENNReal.ofReal (2 * R * P * D ^ 2) * S := by
    rw [show D ^ 2 *
      (P * (2 * R) * Real.sqrt (⨍ z in ball x (10 * R), g z ∂μ)) =
      (2 * R * P * D ^ 2) *
        Real.sqrt (⨍ z in ball x (10 * R), g z ∂μ) by ring,
      ENNReal.ofReal_mul hA]
    exact mul_le_mul' le_rfl hzero
  apply h.trans
  change ENNReal.ofReal (2 * R * P * D) * S + _ ≤ _
  calc
    _ ≤ ENNReal.ofReal (2 * R * P * D) * S +
        ENNReal.ofReal (2 * R * P * D ^ 2) * S := add_le_add le_rfl hi
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add hD hA]
      congr 2
      ring


def doublingHedbergConstant (D P : ℝ) : ℝ :=
  10 * P * (D + D ^ 2)

theorem doublingHedbergConstant_pos {D : ℝ} (hD : 1 ≤ D) {P : ℝ} (hP : 0 < P) :
    0 < doublingHedbergConstant D P := by
  unfold doublingHedbergConstant
  exact mul_pos (mul_pos (by norm_num) hP)
    (add_pos (zero_lt_one.trans_le hD) (sq_pos_of_pos (zero_lt_one.trans_le hD)))

theorem poincareSeries_power_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) :
    doublingPoincareSeries μ R g x ≤ ENNReal.ofReal
      (5 * (doublingLocalMaximalEnergy μ c R g x).toReal ^ (1 / (2 * doublingSobolevKappa D)) *
        (doublingLocalEnergy μ c R g) ^ doublingSobolevGain D) := by
  have h := poincareSeries_hedberg hD hμ hR hx g hg hgn
  have he := doubling_hedberg_sqrt_quotient_eq_power (M := (doublingLocalMaximalEnergy μ c R g x).toReal)
    D ENNReal.toReal_nonneg
    (doublingLocalEnergy_nonneg μ c R g hgn)
  have he5 := congrArg (fun t : ℝ => 5 * t) he
  simp only [← mul_div_assoc, ← mul_assoc] at he5
  rw [he5] at h
  exact h

theorem hedberg_oscillation {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂μ))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ≤
      doublingHedbergConstant D P * R *
        (doublingLocalMaximalEnergy μ c R g x).toReal ^ (1 / (2 * doublingSobolevKappa D)) *
        (doublingLocalEnergy μ c R g) ^ doublingSobolevGain D := by
  have h := (oscillation_le_series hD hμ hP.le f g hf hPI c hR hx).trans
    (mul_le_mul' le_rfl (poincareSeries_power_bound hD hμ hR hx g hg hgn))
  have hC : 0 ≤ 2 * R * P * (D + D ^ 2) := by
    have := (zero_le_one.trans hD.1)
    have := (sq_nonneg D)
    positivity
  rw [← ENNReal.ofReal_mul hC] at h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal (by
    apply mul_nonneg hC
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg (doublingLocalEnergy_nonneg μ c R g hgn) _))] at ht
  convert ht using 1
  unfold doublingHedbergConstant
  ring


end RepulsiveCoulomb.PaperRoute
