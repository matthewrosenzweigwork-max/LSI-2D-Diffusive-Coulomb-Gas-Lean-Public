module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevMeans
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevMaximal

@[expose] public section

/-! Pointwise dyadic representation conditional on a displayed weak Poincare
estimate. This is the telescoping step of the Sobolev upgrade, not a proof of
the missing David--Semmes estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem GlobalDoublingWith.poincare_chain {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (f g : ℂ → ℝ) (hf : Continuous f)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂μ))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ≤
      (∑' n : ℕ, ENNReal.ofReal (D *
        (P * doublingMeanRadius (2 * R) n *
          Real.sqrt (⨍ z in ball x (5 * doublingMeanRadius (2 * R) n), g z ∂μ)))) +
      ENNReal.ofReal (D ^ 2 *
        (P * (2 * R) * Real.sqrt (⨍ z in ball x (10 * R), g z ∂μ))) := by
  apply (hD.global_dyadic_mean_oscillation hμ f hf c hR hx).trans
  apply add_le_add
  · apply ENNReal.tsum_le_tsum
    intro n
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hPI x _ (doublingMeanRadius_pos (by positivity) n)) (zero_le_one.trans hD.1))
  · apply ENNReal.ofReal_le_ofReal
    have h := hPI x (2 * R) (by positivity)
    rw [show 5 * (2 * R) = 10 * R by ring] at h
    exact mul_le_mul_of_nonneg_left h (sq_nonneg D)


/-- Normalized energy on the exact physical ball 11B. Its numerator has no
point-product growth multiplier. -/
def doublingLocalEnergy (μ : Measure ℂ) (c : ℂ) (R : ℝ) (g : ℂ → ℝ) : ℝ :=
  (∫ z in ball c (11 * R), g z ∂μ) / μ.real (ball c R)

theorem doublingLocalEnergy_nonneg (μ : Measure ℂ) (c : ℂ) (R : ℝ)
    (g : ℂ → ℝ) (hgn : ∀ z, 0 ≤ g z) : 0 ≤ doublingLocalEnergy μ c R g :=
  div_nonneg (integral_nonneg hgn) ENNReal.toReal_nonneg

/-- The global-energy bound genuinely consumes the supplied D's exact dyadic iterate. -/
theorem GlobalDoublingWith.local_energy_average_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (⨍ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤
      (2 : ℝ) ^ (doublingDimension D * n) * doublingLocalEnergy μ c R g := by
  have hM := hμ.real_ball_pos x (doublingDyadicRadius_pos hR n)
  have hN := hμ.real_ball_pos c hR
  have hi : (∫ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤
      ∫ z in ball c (11 * R), g z ∂μ :=
    setIntegral_mono_set (hμ.continuous_ball_integrable hg c _)
      (Eventually.of_forall hgn) (Eventually.of_forall (doublingDyadicBall_subset_outer hR hx n))
  have he : 0 ≤ ∫ z in ball c (11 * R), g z ∂μ := integral_nonneg hgn
  have hm := hD.real_ball_le_dyadic_dimension hμ hR hx n
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (μ.real (ball x (doublingDyadicRadius R n)))⁻¹ *
    (∫ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤ _
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_le_div_of_nonneg_right hi hM.le).trans
  unfold doublingLocalEnergy
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hN).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hM).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm he]

theorem GlobalDoublingWith.local_energy_sqrt_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    Real.sqrt (⨍ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤
      Real.sqrt (doublingLocalEnergy μ c R g) * ((2 : ℝ) ^ n) ^ (doublingDimension D : ℝ) := by
  have ht : 1 ≤ ((2 : ℝ) ^ n) ^ (doublingDimension D : ℝ) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (Nat.cast_nonneg _)
  have hE := doublingLocalEnergy_nonneg μ c R g hgn
  have h := hD.local_energy_average_bound hμ hR hx g hg hgn n
  have he : (2 : ℝ) ^ (doublingDimension D * n) =
      ((2 : ℝ) ^ n) ^ (doublingDimension D : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, Nat.mul_comm]
  rw [he, mul_comm] at h
  apply (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) (by positivity))).mpr
  rw [mul_pow, Real.sq_sqrt hE]
  exact h.trans (mul_le_mul_of_nonneg_left (by nlinarith :
    ((2 : ℝ) ^ n) ^ (doublingDimension D : ℝ) ≤
      (((2 : ℝ) ^ n) ^ (doublingDimension D : ℝ)) ^ 2) hE)

theorem GlobalDoublingWith.local_energy_scaled_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (1 / 2 : ℝ) ^ n * Real.sqrt (⨍ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤
      Real.sqrt (doublingLocalEnergy μ c R g) *
        ((2 : ℝ) ^ ((doublingDimension D : ℝ) - 1)) ^ n := by
  have h := mul_le_mul_of_nonneg_left (hD.local_energy_sqrt_bound hμ hR hx g hg hgn n)
    (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity)
  apply h.trans_eq
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : ((2 : ℝ) ^ n) ^ (doublingDimension D : ℝ) =
      ((2 : ℝ) ^ n) ^ ((doublingDimension D : ℝ) - 1) * (2 : ℝ) ^ n := by
    convert Real.rpow_add_one hp ((doublingDimension D : ℝ) - 1) using 1; congr 1; ring
  rw [he, div_pow, one_pow]
  have hc : ((2 : ℝ) ^ n) ^ ((doublingDimension D : ℝ) - 1) =
      ((2 : ℝ) ^ ((doublingDimension D : ℝ) - 1)) ^ n := by
    rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]
  rw [hc]
  field_simp

end RepulsiveCoulomb.PaperRoute
