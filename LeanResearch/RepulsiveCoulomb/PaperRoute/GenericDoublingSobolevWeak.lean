module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevHedberg

@[expose] public section

/-! Actual weak distribution and normalized local Sobolev inequality, derived
from global doubling and the displayed weak (1,2) Poincare hypothesis. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem generic_weak_distribution_of_power_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (u : X → ℝ) (M : X → ℝ≥0∞)
    {K α q : ℝ} (hK : 0 < K) (hq : 0 < q) (hαq : α * q = 1)
    (hfinite : ∀ x ∈ S, M x ≠ ⊤)
    (hpoint : ∀ x ∈ S, u x ≤ K * (M x).toReal ^ α)
    {C : ℝ≥0∞} (hweak : ∀ t : ℝ≥0∞, t * μ {x | t < M x} ≤ C)
    {L : ℝ} (hL : 0 < L) :
    ENNReal.ofReal (L ^ q) * μ {x | x ∈ S ∧ L < u x} ≤ ENNReal.ofReal (K ^ q) * C := by
  let t : ℝ := (L / K) ^ q
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hL hK) q
  have hsub : {x | x ∈ S ∧ L < u x} ⊆ {x | ENNReal.ofReal t < M x} := by
    intro x hx
    apply (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfinite x hx.1)).mpr
    have hlt : L / K < (M x).toReal ^ α := (div_lt_iff₀ hK).mpr (by
      simpa only [mul_comm] using hx.2.trans_le (hpoint x hx.1))
    have h := Real.rpow_lt_rpow (div_nonneg hL.le hK.le) hlt hq
    rw [← Real.rpow_mul ENNReal.toReal_nonneg, hαq, Real.rpow_one] at h
    exact h
  have hw : ENNReal.ofReal t * μ {x | x ∈ S ∧ L < u x} ≤ C :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans (hweak (ENNReal.ofReal t))
  have he : ENNReal.ofReal (K ^ q) * ENNReal.ofReal t = ENNReal.ofReal (L ^ q) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
    congr 1
    dsimp [t]
    rw [Real.div_rpow hL.le hK.le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos hK q).ne']
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (K ^ q))) hw
  rwa [← mul_assoc, he] at h


theorem generic_sobolev_distribution_coefficient {C D G R I N q δ κ : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hR : 0 ≤ R) (hI : 0 ≤ I) (hN : 0 < N)
    (hexp : δ * q + 1 = κ) (hκ : κ ≠ 0) :
    (C * R * (G * I / N) ^ δ) ^ q * (D * I) =
      (D * C ^ q * G ^ (δ * q)) * R ^ q * N * (I / N) ^ κ := by
  have hu : 0 ≤ I / N := div_nonneg hI hN.le
  have hE : 0 ≤ G * I / N := div_nonneg (mul_nonneg hG hI) hN.le
  rw [Real.mul_rpow (mul_nonneg hC hR) (Real.rpow_nonneg hE δ),
    Real.mul_rpow hC hR, ← Real.rpow_mul hE]
  rw [mul_div_assoc, Real.mul_rpow hG hu]
  have hi : I = N * (I / N) := by field_simp
  have hp : (I / N) ^ (δ * q) * (I / N) = (I / N) ^ κ := by
    rw [← Real.rpow_add_one' hu (by rwa [hexp]), hexp]
  calc
    _ = (D * C ^ q * G ^ (δ * q)) * R ^ q * N *
        ((I / N) ^ (δ * q) * (I / N)) := by
      conv_lhs => rhs; rhs; rw [hi]
      ring
    _ = _ := by rw [hp]


theorem doublingSobolevGain_times_q_add_one (D : ℝ) :
    doublingSobolevGain D * (2 * doublingSobolevKappa D) + 1 = doublingSobolevKappa D := by
  have hs := doublingDimension_real_ge_two D
  have hs0 : (doublingDimension D : ℝ) ≠ 0 := by linarith
  have hs1 : (doublingDimension D : ℝ) - 1 ≠ 0 := by linarith
  unfold doublingSobolevGain doublingSobolevKappa
  field_simp
  ring


theorem weak_sobolev_of_poincare {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂μ))
    (c : ℂ) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ENNReal.ofReal (L ^ (2 * doublingSobolevKappa D)) * μ
      {x | x ∈ ball c R ∧ L < ‖f x - (⨍ z in ball c R, f z ∂μ)‖} ≤
    ENNReal.ofReal ((doublingHedbergConstant D P * R *
        (doublingLocalEnergy μ c R g) ^ doublingSobolevGain D) ^ (2 * doublingSobolevKappa D)) *
      (ENNReal.ofReal (D ^ 3) *
        ∫⁻ z in ball c (11 * R), ENNReal.ofReal (g z) ∂μ) := by
  by_cases hE : doublingLocalEnergy μ c R g = 0
  · have hzero (x : ℂ) (hx : x ∈ ball c R) :
        ‖f x - (⨍ z in ball c R, f z ∂μ)‖ = 0 := by
      have h := oscillation_le_series hD hμ hP.le f g hf hPI c hR hx
      rw [poincareSeries_zero_of_energy_zero hD hμ hR hx g hg hgn hE, mul_zero] at h
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)) (norm_nonneg _)
    have hs : {x | x ∈ ball c R ∧ L < ‖f x - (⨍ z in ball c R, f z ∂μ)‖} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge hL.le) (by simpa only [hzero x hx.1] using hx.2)
    rw [hs, measure_empty, mul_zero]
    exact bot_le
  have hEp : 0 < doublingLocalEnergy μ c R g :=
    lt_of_le_of_ne (doublingLocalEnergy_nonneg μ c R g hgn) (Ne.symm hE)
  apply generic_weak_distribution_of_power_bound (μ) (ball c R)
    (fun x => ‖f x - (⨍ z in ball c R, f z ∂μ)‖)
    (doublingLocalMaximalEnergy μ c R g)
    (α := (1 / (2 * doublingSobolevKappa D)))
    (mul_pos (mul_pos (doublingHedbergConstant_pos hD.1 hP) hR) (Real.rpow_pos_of_pos hEp _))
    (mul_pos (by norm_num) (lt_trans zero_lt_one (doublingSobolevKappa_gt_one D)))
    ((by have hκ := doublingSobolevKappa_gt_one D; field_simp))
    (fun x _ => (hμ.localMaximalEnergy_lt_top c hR hg x).ne) ?_ ?_ hL
  · intro x hx
    have h := hedberg_oscillation hD hμ hP f g hf hg hgn hPI c hR hx
    convert h using 1
    ring
  · intro t
    exact hD.localMaximalEnergy_weak_bound c hR g t


/-- D-only maximal loss times the actual PI/Hedberg coefficient. -/
def doublingWeakSobolevConstant (D P : ℝ) : ℝ :=
  D ^ 3 * (doublingHedbergConstant D P) ^ (2 * doublingSobolevKappa D)

theorem doublingWeakSobolevConstant_pos {D : ℝ} (hD : 1 ≤ D) {P : ℝ} (hP : 0 < P) :
    0 < doublingWeakSobolevConstant D P :=
  mul_pos (pow_pos (zero_lt_one.trans_le hD) _) (Real.rpow_pos_of_pos (doublingHedbergConstant_pos hD hP) _)


theorem weak_sobolev_normalized {μ : Measure ℂ} {D P : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ) (hP : 0 < P)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂μ)‖ ∂μ) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂μ))
    (c : ℂ) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ENNReal.ofReal (L ^ (2 * doublingSobolevKappa D)) * μ
      {x | x ∈ ball c R ∧ L < ‖f x - (⨍ z in ball c R, f z ∂μ)‖} ≤
    ENNReal.ofReal (doublingWeakSobolevConstant D P * R ^ (2 * doublingSobolevKappa D) *
      (μ).real (ball c R) *
      ((∫ z in ball c (11 * R), g z ∂μ) /
        (μ).real (ball c R)) ^ doublingSobolevKappa D) := by
  have hN : 0 < (μ).real (ball c R) :=
    hμ.real_ball_pos c hR
  have hI : 0 ≤ ∫ z in ball c (11 * R), g z ∂μ := integral_nonneg hgn
  have hi := ofReal_integral_eq_lintegral_ofReal
    (hμ.continuous_ball_integrable hg c (11 * R)) (Eventually.of_forall hgn)
  have h := weak_sobolev_of_poincare hD hμ hP f g hf hg hgn hPI c hR hL
  rw [← hi, ← ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans hD.1) 3),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by
      apply mul_nonneg (mul_nonneg (doublingHedbergConstant_pos hD.1 hP).le hR.le)
      exact Real.rpow_nonneg (doublingLocalEnergy_nonneg μ c R g hgn) _) _)] at h
  have he := generic_sobolev_distribution_coefficient
    (D := D ^ 3) (q := 2 * doublingSobolevKappa D)
    (δ := doublingSobolevGain D) (κ := doublingSobolevKappa D)
    (doublingHedbergConstant_pos hD.1 hP).le (by norm_num : (0 : ℝ) ≤ 1) hR.le hI hN
    (doublingSobolevGain_times_q_add_one D) (lt_trans zero_lt_one (doublingSobolevKappa_gt_one D)).ne'
  simp only [one_mul, Real.one_rpow, mul_one] at he
  unfold doublingLocalEnergy at h
  rwa [he] at h

end RepulsiveCoulomb.PaperRoute
