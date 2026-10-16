module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.MetricDoublingComparison
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Actual global doubling implies polynomial growth and volume balance

Every measure estimate is derived from the supplied `GlobalDoublingWith μ D`.
The measure is arbitrary on the plane; no point-product volume formula,
Poincaré premise, growth certificate, or Sobolev endpoint is imported. The
centered coefficient is `2^s` and the nested coefficient is `4^s`.

The integer dimension `s = ceil(D) + 2` is deliberately non-optimal. It gives a
strictly superquadratic exponent `2 * s / (s - 1)` satisfying the manuscript's
same-measure volume balance. This module proves volume control and balance,
not the analytic Sobolev upgrade.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb.PaperRoute

/-- A dimension determined solely by the supplied global doubling constant. -/
def doublingDimension (D : ℝ) : ℕ := Nat.ceil D + 2

/-- The admissible Sobolev gain chosen from the new doubling dimension. -/
def doublingSobolevKappa (D : ℝ) : ℝ :=
  (doublingDimension D : ℝ) / ((doublingDimension D : ℝ) - 1)

/-- The scalar interpolation exponent used for volume balance. -/
def doublingSobolevGain (D : ℝ) : ℝ := 1 / (2 * (doublingDimension D : ℝ))

theorem doublingDimension_ge_two (D : ℝ) : 2 ≤ doublingDimension D := by
  unfold doublingDimension
  omega

theorem doublingDimension_real_ge_two (D : ℝ) : 2 ≤ (doublingDimension D : ℝ) := by
  exact_mod_cast doublingDimension_ge_two D

theorem le_two_pow_doublingDimension (D : ℝ) : D ≤ (2 : ℝ) ^ doublingDimension D := by
  have hceil : D ≤ (Nat.ceil D : ℝ) := Nat.le_ceil D
  have hdim : (Nat.ceil D : ℝ) ≤ (doublingDimension D : ℝ) := by
    simp only [doublingDimension, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hpow : (doublingDimension D : ℝ) ≤ (2 : ℝ) ^ doublingDimension D := by
    exact_mod_cast (Nat.lt_two_pow_self (n := doublingDimension D)).le
  exact hceil.trans (hdim.trans hpow)

theorem doublingSobolevKappa_gt_one (D : ℝ) : 1 < doublingSobolevKappa D := by
  have hs := doublingDimension_real_ge_two D
  unfold doublingSobolevKappa
  apply (one_lt_div (by linarith)).2
  linarith

theorem doublingSobolevGain_pos (D : ℝ) : 0 < doublingSobolevGain D := by
  have hs := doublingDimension_real_ge_two D
  unfold doublingSobolevGain
  positivity

theorem doublingSobolevGain_add_inverse (D : ℝ) :
    doublingSobolevGain D + 1 / (2 * doublingSobolevKappa D) = 1 / 2 := by
  have hs := doublingDimension_real_ge_two D
  unfold doublingSobolevGain doublingSobolevKappa
  field_simp [show (doublingDimension D : ℝ) ≠ 0 by linarith,
    show (doublingDimension D : ℝ) - 1 ≠ 0 by linarith]
  ring

theorem doublingSobolevGain_volume_exponent (D : ℝ) :
    (doublingDimension D : ℝ) * doublingSobolevGain D = 1 / 2 := by
  have hs := doublingDimension_real_ge_two D
  unfold doublingSobolevGain
  field_simp [show (doublingDimension D : ℝ) ≠ 0 by linarith]

theorem doublingSobolev_balance_condition (D : ℝ) :
    (doublingDimension D : ℝ) * (1 / 2 - 1 / (2 * doublingSobolevKappa D)) ≤ 1 := by
  have he := doublingSobolevGain_add_inverse D
  have hv := doublingSobolevGain_volume_exponent D
  have : 1 / 2 - 1 / (2 * doublingSobolevKappa D) = doublingSobolevGain D := by
    linarith
  rw [this, hv]
  norm_num

theorem doublingSobolev_superPoincare_power (D : ℝ) :
    doublingSobolevKappa D / (doublingSobolevKappa D - 1) = (doublingDimension D : ℝ) := by
  have hs := doublingDimension_real_ge_two D
  unfold doublingSobolevKappa
  field_simp [show (doublingDimension D : ℝ) - 1 ≠ 0 by linarith]
  ring

/-- Positivity and finiteness are checked before real-valued measure arithmetic. -/
theorem PositiveFiniteBalls.real_ball_pos {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < μ.real (ball c r) :=
  ENNReal.toReal_pos (hμ c r hr).1.ne' (hμ c r hr).2.ne

/-- Exact iteration of the supplied global constant, including the zero step. -/
theorem GlobalDoublingWith.ball_pow_two_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (c : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    μ (ball c ((2 : ℝ) ^ k * r)) ≤ ENNReal.ofReal (D ^ k) * μ (ball c r) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD.1
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        μ (ball c ((2 : ℝ) ^ (k + 1) * r))
            = μ (ball c (2 * ((2 : ℝ) ^ k * r))) := by congr 2; ring
        _ ≤ ENNReal.ofReal D * μ (ball c ((2 : ℝ) ^ k * r)) :=
          hD.2 c _ (mul_pos (pow_pos (by norm_num) _) hr)
        _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (D ^ k) * μ (ball c r)) :=
          mul_le_mul_right ih _
        _ = ENNReal.ofReal (D ^ (k + 1)) * μ (ball c r) := by
          rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hD0 _)]
          ring

/-- The finite-mass real counterpart of exact global iteration. -/
theorem GlobalDoublingWith.real_ball_pow_two_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    μ.real (ball c ((2 : ℝ) ^ k * r)) ≤ D ^ k * μ.real (ball c r) := by
  have hf : ENNReal.ofReal (D ^ k) * μ (ball c r) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hμ c r hr).2.ne
  have h := ENNReal.toReal_mono hf (hD.ball_pow_two_le c hr k)
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (zero_le_one.trans hD.1) _)] using h

theorem GlobalDoublingWith.real_ball_four_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    μ.real (ball c (4 * r)) ≤ D ^ 2 * μ.real (ball c r) := by
  convert hD.real_ball_pow_two_le hμ c hr 2 using 1
  norm_num

theorem GlobalDoublingWith.real_ball_eleven_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    μ.real (ball c (11 * r)) ≤ D ^ 4 * μ.real (ball c r) := by
  calc
    _ ≤ μ.real (ball c ((2 : ℝ) ^ 4 * r)) :=
      measureReal_mono (ball_subset_ball (by norm_num; linarith))
        (hμ c _ (by positivity)).2.ne
    _ ≤ _ := hD.real_ball_pow_two_le hμ c hr 4

/-- Safe fourfold closed-ball control requires no sphere-null assumption. -/
theorem GlobalDoublingWith.closedBall_four_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    μ (closedBall c (4 * r)) ≤ ENNReal.ofReal (D ^ 3) * μ (ball c r) := by
  calc
    _ ≤ μ (ball c ((2 : ℝ) ^ 3 * r)) :=
      measure_mono (closedBall_subset_ball (by norm_num; linarith))
    _ ≤ _ := hD.ball_pow_two_le c hr 3

/-- Arbitrary-scale growth has centered coefficient `2^s`, not `4^s`. -/
theorem GlobalDoublingWith.ball_scale_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) {s : ℕ} (hDs : D ≤ (2 : ℝ) ^ s)
    (c : ℂ) {r scale : ℝ} (hr : 0 < r) (hscale : 1 ≤ scale) :
    μ (ball c (scale * r)) ≤ ENNReal.ofReal ((2 : ℝ) ^ s * scale ^ s) * μ (ball c r) := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hscale (by norm_num : (1 : ℝ) < 2)
  have hp : D ^ (k + 1) ≤ (2 : ℝ) ^ s * scale ^ s := by
    calc
      D ^ (k + 1) ≤ ((2 : ℝ) ^ s) ^ (k + 1) :=
        pow_le_pow_left₀ (zero_le_one.trans hD.1) hDs _
      _ = (2 : ℝ) ^ s * ((2 : ℝ) ^ k) ^ s := by
        rw [pow_succ, ← pow_mul, ← pow_mul, Nat.mul_comm s k]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hk _) (by positivity)
  calc
    _ ≤ μ (ball c ((2 : ℝ) ^ (k + 1) * r)) :=
      measure_mono (ball_subset_ball (mul_le_mul_of_nonneg_right hk'.le hr.le))
    _ ≤ ENNReal.ofReal (D ^ (k + 1)) * μ (ball c r) := hD.ball_pow_two_le c hr _
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hp) _

/-- Real mass growth from actual arbitrary-scale doubling. -/
theorem GlobalDoublingWith.real_ball_scale_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {s : ℕ} (hDs : D ≤ (2 : ℝ) ^ s) (c : ℂ) {r scale : ℝ}
    (hr : 0 < r) (hscale : 1 ≤ scale) :
    μ.real (ball c (scale * r)) ≤ (2 : ℝ) ^ s * scale ^ s * μ.real (ball c r) := by
  have hf : ENNReal.ofReal ((2 : ℝ) ^ s * scale ^ s) * μ (ball c r) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hμ c r hr).2.ne
  have h := ENNReal.toReal_mono hf (hD.ball_scale_le hDs c hr hscale)
  have hscale0 : 0 ≤ scale := zero_le_one.trans hscale
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (2 : ℝ) ^ s * scale ^ s by positivity)] using h

/-- Nested balls yield the coefficient `4^s` after moving the center. -/
theorem GlobalDoublingWith.real_nested_ball_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {s : ℕ} (hDs : D ≤ (2 : ℝ) ^ s) {c d : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hsub : ball c r ⊆ ball d R) :
    μ.real (ball d R) ≤ (4 : ℝ) ^ s * (R / r) ^ s * μ.real (ball c r) := by
  have hR : 0 < R := hr.trans_le hrR
  have hcd : dist c d < R := hsub (mem_ball_self hr)
  have hlarge : ball d R ⊆ ball c (2 * R) :=
    ball_subset_ball' (by rw [dist_comm]; linarith)
  have hscale : 1 ≤ 2 * R / r := (le_div_iff₀ hr).2 (by linarith)
  have heq : (2 * R / r) * r = 2 * R := by field_simp
  have hcoef : (2 : ℝ) ^ s * (2 * R / r) ^ s = (4 : ℝ) ^ s * (R / r) ^ s := by
    rw [show 2 * R / r = 2 * (R / r) by ring, mul_pow, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    _ ≤ μ.real (ball c (2 * R)) := measureReal_mono hlarge (hμ c _ (by positivity)).2.ne
    _ ≤ (2 : ℝ) ^ s * (2 * R / r) ^ s * μ.real (ball c r) := by
      simpa only [heq] using hD.real_ball_scale_le hμ hDs c hr hscale
    _ = _ := by rw [hcoef]

/-- The positive nested mass ratio, in natural-power lower-growth form. -/
theorem GlobalDoublingWith.nested_radius_pow_le_mass_ratio {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {s : ℕ} (hDs : D ≤ (2 : ℝ) ^ s) {c d : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hsub : ball c r ⊆ ball d R) :
    (r / R) ^ s ≤ (4 : ℝ) ^ s * (μ.real (ball c r) / μ.real (ball d R)) := by
  have hR : 0 < R := hr.trans_le hrR
  have hm := hD.real_nested_ball_le hμ hDs hr hrR hsub
  have ht : 0 ≤ (r / R) ^ s := pow_nonneg (div_nonneg hr.le hR.le) _
  have heq : (R / r) ^ s * (r / R) ^ s = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (hμ.real_ball_pos d hR)).2
  calc
    _ ≤ ((4 : ℝ) ^ s * (R / r) ^ s * μ.real (ball c r)) * (r / R) ^ s := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hm ht
    _ = (4 : ℝ) ^ s * μ.real (ball c r) := by
      calc
        _ = (4 : ℝ) ^ s * μ.real (ball c r) * ((R / r) ^ s * (r / R) ^ s) := by ring
        _ = _ := by rw [heq, mul_one]

/-- The manuscript's inverse-coefficient lower volume bound. -/
theorem GlobalDoublingWith.nested_mass_ratio_lower {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c d : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hsub : ball c r ⊆ ball d R) :
    (4 : ℝ) ^ (-(doublingDimension D : ℝ)) * (r / R) ^ (doublingDimension D : ℝ) ≤
      μ.real (ball c r) / μ.real (ball d R) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_inv_mul]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) _)).2
  simpa only [mul_comm] using hD.nested_radius_pow_le_mass_ratio hμ
    (le_two_pow_doublingDimension D) hr hrR hsub

/-- Scalar power balance; its input is an actual mass bound below. -/
private theorem growth_power_balance {t u A s δ β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hu : 0 < u) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hsδ : s * δ ≤ 1) (he : δ + β = 1 / 2) (hm : t ^ s ≤ A * u) :
    t * u ^ β ≤ A ^ δ * u ^ (1 / 2 : ℝ) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg ht.le _) hm hδ
  rw [← Real.rpow_mul ht.le, Real.mul_rpow hA.le hu.le] at h
  have ht' : t ≤ t ^ (s * δ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hsδ
  calc
    _ ≤ (A ^ δ * u ^ δ) * u ^ β :=
      mul_le_mul_of_nonneg_right (ht'.trans h) (Real.rpow_nonneg hu.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hu, he]

/-- Actual same-measure balance produced from the new doubling witness. -/
theorem GlobalDoublingWith.nested_ball_balance {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c d : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hsub : ball c r ⊆ ball d R) :
    (r / R) * (μ.real (ball c r) / μ.real (ball d R)) ^
        (1 / (2 * doublingSobolevKappa D)) ≤
      (4 : ℝ) ^ (1 / 2 : ℝ) * (μ.real (ball c r) / μ.real (ball d R)) ^ (1 / 2 : ℝ) := by
  have hR : 0 < R := hr.trans_le hrR
  have hm : (r / R) ^ (doublingDimension D : ℝ) ≤
      (4 : ℝ) ^ doublingDimension D * (μ.real (ball c r) / μ.real (ball d R)) := by
    rw [Real.rpow_natCast]
    exact hD.nested_radius_pow_le_mass_ratio hμ (le_two_pow_doublingDimension D) hr hrR hsub
  have hb := growth_power_balance (div_pos hr hR) ((div_le_one hR).2 hrR)
    (div_pos (hμ.real_ball_pos c hr) (hμ.real_ball_pos d hR))
    (pow_pos (by norm_num : (0 : ℝ) < 4) (doublingDimension D))
    (doublingSobolevGain_pos D).le
    (show (doublingDimension D : ℝ) * doublingSobolevGain D ≤ 1 by
      rw [doublingSobolevGain_volume_exponent]; norm_num)
    (doublingSobolevGain_add_inverse D) hm
  have hc : ((4 : ℝ) ^ doublingDimension D) ^ doublingSobolevGain D = (4 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
      doublingSobolevGain_volume_exponent]
  simpa only [hc] using hb

/-- The energy balls used in the fixed-center dyadic Sobolev proof. -/
def doublingDyadicRadius (R : ℝ) (k : ℕ) : ℝ := 10 * R * (1 / 2 : ℝ) ^ k

theorem doublingDyadicRadius_pos {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 < doublingDyadicRadius R k := by unfold doublingDyadicRadius; positivity

theorem pow_two_mul_doublingDyadicRadius (R : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k * doublingDyadicRadius R k = 10 * R := by
  unfold doublingDyadicRadius
  calc
    _ = (10 * R) * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

theorem doublingDyadicRadius_le_ten {R : ℝ} (hR : 0 < R) (k : ℕ) :
    doublingDyadicRadius R k ≤ 10 * R := by
  unfold doublingDyadicRadius
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem ball_subset_dyadic_base {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hx : x ∈ ball c R) : ball c R ⊆ ball x (10 * R) := by
  apply ball_subset_ball'
  rw [dist_comm]
  have hxc : dist x c < R := hx
  linarith

theorem doublingDyadicBall_subset_outer {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hx : x ∈ ball c R) (k : ℕ) :
    ball x (doublingDyadicRadius R k) ⊆ ball c (11 * R) := by
  apply ball_subset_ball'
  have hxc : dist x c < R := hx
  have hk := doublingDyadicRadius_le_ten hR k
  linarith

/-- Exact `D^k` lower mass control for all the actual dyadic energy balls. -/
theorem GlobalDoublingWith.real_ball_le_dyadic {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R) (k : ℕ) :
    μ.real (ball c R) ≤ D ^ k * μ.real (ball x (doublingDyadicRadius R k)) := by
  calc
    _ ≤ μ.real (ball x (10 * R)) :=
      measureReal_mono (ball_subset_dyadic_base hR hx) (hμ x _ (by positivity)).2.ne
    _ ≤ _ := by
      simpa only [pow_two_mul_doublingDyadicRadius] using
        hD.real_ball_pow_two_le hμ x (doublingDyadicRadius_pos hR k) k

/-- The conventional negative-power notation names exactly the same radius. -/
theorem doublingDyadicRadius_eq_negative_power (R : ℝ) (k : ℕ) :
    doublingDyadicRadius R k = 10 * R * (2 : ℝ) ^ (-(k : ℝ)) := by
  simp only [doublingDyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, ← inv_pow, one_div]

/-- Dimension-form dyadic control, with the exponent produced solely by `D`. -/
theorem GlobalDoublingWith.real_ball_le_dyadic_dimension {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R) (k : ℕ) :
    μ.real (ball c R) ≤ (2 : ℝ) ^ (doublingDimension D * k) *
      μ.real (ball x (doublingDyadicRadius R k)) := by
  calc
    _ ≤ D ^ k * μ.real (ball x (doublingDyadicRadius R k)) :=
      hD.real_ball_le_dyadic hμ hR hx k
    _ ≤ ((2 : ℝ) ^ doublingDimension D) ^ k *
        μ.real (ball x (doublingDyadicRadius R k)) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (zero_le_one.trans hD.1) (le_two_pow_doublingDimension D) _)
        measureReal_nonneg
    _ = _ := by rw [← pow_mul]

end RepulsiveCoulomb.PaperRoute
