module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Actual annular derivative energy forced by scalar circle oscillations

The analytic input is a Lipschitz scalar function and genuine zero/one points
on every intermediate circle. Derivatives below are the actual, totalized
real Fréchet derivatives. In particular, almost-everywhere differentiability
in the plane is transported to almost every circle using polar change of
variables and Fubini; no assertion is made for each individual circle.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ENNReal
namespace RepulsiveCoulomb.PaperRoute

/-- The polar inverse and the standard circle parametrization agree. -/
theorem add_polarCoord_symm_eq_circleMap (a : ℂ) (p : ℝ × ℝ) :
    a + Complex.polarCoord.symm p = circleMap a p.1 p.2 := by
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]

/-- A planar almost-everywhere property holds on almost every circle, at almost
all angles. This uses the nonnegative polar formula, not a restriction of a
planar null set to an arbitrary fixed circle. -/
theorem ae_ae_circleMap_of_ae {P : ℂ → Prop} (hP : MeasurableSet {z | P z})
    (hPae : ∀ᵐ z : ℂ, P z) (a : ℂ) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi), P (circleMap a t θ) := by
  let b : ℂ → ℝ≥0∞ := {z | ¬ P z}.indicator (fun _ => 1)
  have hb : Measurable b := measurable_const.indicator hP.compl
  have hb0 : (∫⁻ z : ℂ, b z) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hPae] with z hz
    simp [b, hz]
  have hc : Continuous (fun p : ℝ × ℝ => a + Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * b (a + Complex.polarCoord.symm p)) :=
    measurable_fst.ennreal_ofReal.mul (hb.comp hc.measurable)
  have hz : (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * b (a + Complex.polarCoord.symm p)) = 0 := by
    calc
      _ = ∫⁻ z : ℂ, b (a + z) :=
        Complex.lintegral_comp_polarCoord_symm (fun z => b (a + z))
      _ = ∫⁻ z : ℂ, b z := lintegral_add_left_eq_self b a
      _ = 0 := hb0
  have ha := (lintegral_eq_zero_iff hm).mp hz
  have hpair : ∀ᵐ p ∂volume.restrict polarCoord.target,
      P (circleMap a p.1 p.2) := by
    filter_upwards [ha, ae_restrict_mem polarCoord.open_target.measurableSet] with p hp hpt
    have hp0 : ENNReal.ofReal p.1 ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hpt.1)
    have hbp : b (a + Complex.polarCoord.symm p) = 0 := (mul_eq_zero.mp hp).resolve_left hp0
    by_contra hn
    rw [add_polarCoord_symm_eq_circleMap] at hbp
    simp [b, hn] at hbp
  change ∀ᵐ p ∂volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi),
    P (circleMap a p.1 p.2) at hpair
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hpair
  exact Measure.ae_ae_of_ae_prod hpair

/-- Rademacher and the polar null-set argument supply the actual planar
chain-rule hypothesis at almost every radius and angle. -/
theorem ae_ae_differentiableAt_circleMap {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : ℂ) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
        DifferentiableAt ℝ v (circleMap a t θ) :=
  ae_ae_circleMap_of_ae (measurableSet_of_differentiableAt ℝ v)
    hv.ae_differentiableAt a

/-- The genuine circle-chain-rule bound at an actual planar differentiability point. -/
theorem norm_deriv_comp_circleMap_le {v : ℂ → ℝ} {a : ℂ} {t θ : ℝ}
    (ht : 0 ≤ t) (hv : DifferentiableAt ℝ v (circleMap a t θ)) :
    ‖deriv (v ∘ circleMap a t) θ‖ ≤ t * ‖fderiv ℝ v (circleMap a t θ)‖ := by
  rw [(hv.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap a t θ)).deriv]
  calc
    _ ≤ ‖fderiv ℝ v (circleMap a t θ)‖ * ‖circleMap 0 t θ * Complex.I‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp [norm_circleMap_zero, abs_of_nonneg ht, mul_comm]

/-- A globally Lipschitz scalar has finite actual derivative-square energy on
any bounded planar annulus; no integrability of the scalar itself is needed. -/
theorem integrableOn_sq_norm_fderiv_annulus {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : ℂ) (s r : ℝ) :
    IntegrableOn (fun z : ℂ => ‖fderiv ℝ v z‖ ^ 2)
      {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r} := by
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) ?_ ?_ ?_
  · apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume) (x := a) (r := r)).ne
    apply measure_mono
    intro z hz
    simpa only [mem_ball, dist_eq_norm] using hz.2
  · exact ((measurable_fderiv ℝ v).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hv) 2


/-- A bounded measurable planar integrand has an integrable polar pullback on
a compact annular parameter rectangle. The radial Jacobian is included. -/
theorem integrableOn_radius_mul_circleMap {f : ℂ → ℝ} (hf : Measurable f)
    {M : ℝ} (hf0 : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (a : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (circleMap a p.1 p.2))
      (Ioo s r ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap a p.1 p.2) := by
    simp only [← add_polarCoord_symm_eq_circleMap, Complex.polarCoord_symm_apply]
    fun_prop
  refine Measure.integrableOn_of_bounded (M := r * M) ?_
    (measurable_fst.mul (hf.comp hc.measurable)).aestronglyMeasurable ?_
  · apply ne_top_of_le_ne_top (((isCompact_Icc : IsCompact (Icc s r)).prod
      (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi))).measure_lt_top
      (μ := volume)).ne
    exact measure_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hs.trans hp.1.1).le (hf0 _))]
    exact mul_le_mul (le_of_lt hp.1.2) (hfM _) (hf0 _) (hs.trans hsr).le

/-- Actual polar integration on an annulus, with the same `[-π,π]` angular
period used for the scalar fundamental theorem of calculus (endpoints omitted
only in this Lebesgue set integral). -/
theorem integral_annulus_eq_integral_radius_circleMap {f : ℂ → ℝ}
    (hf : Measurable f) {M : ℝ} (hf0 : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (a : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    (∫ z in {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r}, f z) =
      ∫ t in Ioo s r, ∫ θ in Ioo (-Real.pi) Real.pi, t * f (circleMap a t θ) := by
  let S : Set ℂ := {z | s < ‖z - a‖ ∧ ‖z - a‖ < r}
  let T : Set (ℝ × ℝ) := Ioo s r ×ˢ Ioo (-Real.pi) Real.pi
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  have hT : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : T ⊆ polarCoord.target := fun p hp => ⟨hs.trans hp.1.1, hp.2⟩
  calc
    _ = ∫ z : ℂ, S.indicator f z := (integral_indicator hS).symm
    _ = ∫ z : ℂ, S.indicator f (a + z) := (integral_add_left_eq_self _ a).symm
    _ = ∫ p in polarCoord.target, p.1 • S.indicator f (a + Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in polarCoord.target,
        T.indicator (fun p => p.1 * f (circleMap a p.1 p.2)) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hn : ‖a + Complex.polarCoord.symm p - a‖ = p.1 := by
        rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      by_cases h : s < p.1 ∧ p.1 < r
      · have hmem : a + Complex.polarCoord.symm p ∈ S := by
          simpa only [S, mem_ofPred_eq, hn] using h
        have htmem : p ∈ T := ⟨h, hp.2⟩
        dsimp only
        rw [indicator_of_mem hmem, indicator_of_mem htmem, smul_eq_mul,
          add_polarCoord_symm_eq_circleMap]
      · have hmem : a + Complex.polarCoord.symm p ∉ S := by
          simpa only [S, mem_ofPred_eq, hn] using h
        have htmem : p ∉ T := fun ht => h ht.1
        simp only [indicator_of_notMem hmem, indicator_of_notMem htmem, smul_zero]
    _ = ∫ p in T, p.1 * f (circleMap a p.1 p.2) := by
      rw [setIntegral_indicator hT, inter_eq_self_of_subset_right hsub]
    _ = _ := by
      rw [Measure.volume_eq_prod]
      apply setIntegral_prod
      simpa only [← Measure.volume_eq_prod] using
        integrableOn_radius_mul_circleMap hf hf0 hfM a hs hsr


-- Global Lipschitzness is convenient here: every subinterval is available
-- without an extra interval-subset proof. The circle composition has it.
theorem lipschitz_abs_sub_le_integral_abs_deriv
    {w : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K w)
    {a b : ℝ} (hab : a ≤ b) :
    |w b - w a| ≤ ∫ t in a..b, |deriv w t| := by
  have hAC : AbsolutelyContinuousOnInterval w a b :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  calc
    |w b - w a| = |∫ t in a..b, deriv w t| := by
      rw [hAC.integral_deriv_eq_sub]
    _ ≤ ∫ t in a..b, |deriv w t| :=
      intervalIntegral.abs_integral_le_integral_abs hab

theorem ordered_periodic_variation_ge_two
    {w : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K w)
    {a b u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hcycle : w a = w b) (hgap : |w v - w u| = 1) :
    2 ≤ ∫ t in a..b, |deriv w t| := by
  have hInt (c d : ℝ) : IntervalIntegrable (fun t => |deriv w t|) volume c d := by
    have hAC : AbsolutelyContinuousOnInterval w c d :=
      hLip.lipschitzOnWith.absolutelyContinuousOnInterval
    exact hAC.intervalIntegrable_deriv.abs
  have hleft := lipschitz_abs_sub_le_integral_abs_deriv hLip hau
  have hmid := lipschitz_abs_sub_le_integral_abs_deriv hLip huv
  have hright := lipschitz_abs_sub_le_integral_abs_deriv hLip hvb
  have hout : 1 ≤ (∫ t in a..u, |deriv w t|) +
      (∫ t in v..b, |deriv w t|) := by
    have htri := abs_add_le (w u - w a) (w b - w v)
    have he : (w u - w a) + (w b - w v) = w u - w v := by
      rw [← hcycle]
      ring
    rw [he, abs_sub_comm (w u) (w v), hgap] at htri
    exact htri.trans (add_le_add hleft hright)
  rw [hgap] at hmid
  have htel₁ := intervalIntegral.integral_add_adjacent_intervals
    (hInt a u) (hInt u v)
  have htel₂ := intervalIntegral.integral_add_adjacent_intervals
    (hInt a v) (hInt v b)
  linarith

theorem periodic_zero_one_variation_ge_two
    {w : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K w)
    {a b : ℝ} (hcycle : w a = w b)
    (hzero : ∃ t ∈ Icc a b, w t = 0)
    (hone : ∃ t ∈ Icc a b, w t = 1) :
    2 ≤ ∫ t in a..b, |deriv w t| := by
  obtain ⟨u, hu, hwu⟩ := hzero
  obtain ⟨v, hv, hwv⟩ := hone
  rcases le_total u v with huv | hvu
  · exact ordered_periodic_variation_ge_two hLip hu.1 huv hv.2 hcycle
      (by rw [hwv, hwu]; norm_num)
  · exact ordered_periodic_variation_ge_two hLip hv.1 hvu hu.2 hcycle
      (by rw [hwu, hwv]; norm_num)

-- Constant-function Cauchy–Schwarz, proved directly by completing a square.
-- Instantiate μ=volume.restrict(Ioc(-pi)pi) and u=|deriv w|.
theorem circle_l2_lower_of_integral_ge_two
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (hmass : μ.real univ = 2 * Real.pi)
    (u : α → ℝ) (hu : Integrable u μ)
    (hu2 : Integrable (fun x => u x ^ 2) μ)
    (hU : 2 ≤ ∫ x, u x ∂μ) :
    2 / Real.pi ≤ ∫ x, u x ^ 2 ∂μ := by
  let c : ℝ := Real.pi⁻¹
  have hc : 0 < c := inv_pos.mpr Real.pi_pos
  have hnonneg : 0 ≤ ∫ x, (u x - c) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (u x - c))
  have he : (fun x => (u x - c) ^ 2) =
      (fun x => u x ^ 2 - (2 * c) * u x + c ^ 2) := by
    funext x
    ring
  rw [he, integral_add (f := fun x => u x ^ 2 - (2 * c) * u x)
    (g := fun _ => c ^ 2) (hu2.sub (hu.const_mul (2 * c))) (integrable_const (c ^ 2)),
    integral_sub (f := fun x => u x ^ 2) (g := fun x => (2 * c) * u x)
      hu2 (hu.const_mul (2 * c)), integral_const_mul,
    integral_const, smul_eq_mul, hmass] at hnonneg
  have hconstant : (2 * Real.pi) * c ^ 2 = 2 * c := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  rw [hconstant] at hnonneg
  have hscaled := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * c by positivity)
  have hfinal : 2 * c ≤ ∫ x, u x ^ 2 ∂μ := by linarith
  simpa [c, div_eq_mul_inv] using hfinal



/-- Lipschitzness bounds the actual derivative everywhere, including its
zero value at nondifferentiability points, and yields square integrability. -/
theorem integrableOn_sq_abs_deriv_of_lipschitz {w : ℝ → ℝ} {K : ℝ≥0}
    (hw : LipschitzWith K w) (α β : ℝ) :
    IntegrableOn (fun θ => |deriv w θ| ^ 2) (Ioc α β) := by
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) (by simp)
    (by simpa only [Real.norm_eq_abs] using
      ((measurable_deriv w).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (by simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hw) 2

/-- A genuine Lipschitz closed scalar loop taking both values zero and one
has squared actual derivative integral at least `2/π` over one angular period. -/
theorem periodic_zero_one_sq_deriv_ge {w : ℝ → ℝ} {K : ℝ≥0}
    (hw : LipschitzWith K w) (hcycle : w (-Real.pi) = w Real.pi)
    (hzero : ∃ θ ∈ Icc (-Real.pi) Real.pi, w θ = 0)
    (hone : ∃ θ ∈ Icc (-Real.pi) Real.pi, w θ = 1) :
    2 / Real.pi ≤ ∫ θ in Ioo (-Real.pi) Real.pi, ‖deriv w θ‖ ^ 2 := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi : IntegrableOn (fun θ => |deriv w θ|) (Ioc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      hw.lipschitzOnWith.absolutelyContinuousOnInterval.intervalIntegrable_deriv.abs
  have hvar := periodic_zero_one_variation_ge_two hw hcycle hzero hone
  rw [intervalIntegral.integral_of_le hab] at hvar
  have hmass : (volume.restrict (Ioc (-Real.pi) Real.pi)).real univ = 2 * Real.pi := by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal, Real.pi_pos.le]
    ring
  have h := circle_l2_lower_of_integral_ge_two
    (volume.restrict (Ioc (-Real.pi) Real.pi)) hmass
    (fun θ => |deriv w θ|) hi (integrableOn_sq_abs_deriv_of_lipschitz hw _ _) hvar
  simpa only [Real.norm_eq_abs, integral_Ioc_eq_integral_Ioo] using h

/-- The actual closed interval `[-π,π]` covers each positive-radius sphere. -/
theorem image_circleMap_Icc_neg_pi_pi (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    circleMap a t '' Icc (-Real.pi) Real.pi = sphere a t := by
  have hp : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simpa only [hp, range_circleMap, abs_of_nonneg ht] using
    (periodic_circleMap a t).image_Icc Real.two_pi_pos (-Real.pi)

/-- The two real scalar values on a geometric circle force actual angular
energy, independently of any planar differentiability on that circle. -/
theorem integral_sq_deriv_circleMap_ge {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) {a : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hzero : ∃ z ∈ sphere a t, v z = 0)
    (hone : ∃ z ∈ sphere a t, v z = 1) :
    2 / Real.pi ≤ ∫ θ in Ioo (-Real.pi) Real.pi,
      ‖deriv (v ∘ circleMap a t) θ‖ ^ 2 := by
  have hLip := hv.comp (lipschitzWith_circleMap a t)
  apply periodic_zero_one_sq_deriv_ge hLip
  · have hp : -Real.pi + 2 * Real.pi = Real.pi := by ring
    simpa only [Function.comp_apply, hp] using
      congrArg v ((periodic_circleMap a t) (-Real.pi)).symm
  · obtain ⟨z, hz, hvz⟩ := hzero
    rw [← image_circleMap_Icc_neg_pi_pi a ht] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    exact ⟨θ, hθ, hvz⟩
  · obtain ⟨z, hz, hvz⟩ := hone
    rw [← image_circleMap_Icc_neg_pi_pi a ht] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    exact ⟨θ, hθ, hvz⟩


/-- The derivative energy on each parametrized circle is measurable and finite
by the global Lipschitz bound, without claiming planar differentiability there. -/
theorem integrableOn_sq_norm_fderiv_circleMap {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : ℂ) (t : ℝ) :
    IntegrableOn (fun θ => ‖fderiv ℝ v (circleMap a t θ)‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) (by simp)
    ((((measurable_fderiv ℝ v).comp (measurable_circleMap a t)).norm).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hv) 2

/-- At any radius supplied by the polar null-set argument, the actual planar
energy on the circle dominates the oscillation lower bound with radial weight. -/
theorem integral_radius_sq_norm_fderiv_circleMap_ge {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) {a : ℂ} {t : ℝ} (ht : 0 < t)
    (hzero : ∃ z ∈ sphere a t, v z = 0)
    (hone : ∃ z ∈ sphere a t, v z = 1)
    (hd : ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      DifferentiableAt ℝ v (circleMap a t θ)) :
    (2 / Real.pi) / t ≤ ∫ θ in Ioo (-Real.pi) Real.pi,
      t * ‖fderiv ℝ v (circleMap a t θ)‖ ^ 2 := by
  have hcircle := integral_sq_deriv_circleMap_ge hv ht.le hzero hone
  have hInt := integrableOn_sq_norm_fderiv_circleMap hv a t
  have hIntDeriv : IntegrableOn (fun θ => ‖deriv (v ∘ circleMap a t) θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    apply IntegrableOn.mono_set _ Ioo_subset_Ioc_self
    simpa only [Real.norm_eq_abs] using
      integrableOn_sq_abs_deriv_of_lipschitz (hv.comp (lipschitzWith_circleMap a t))
        (-Real.pi) Real.pi
  have hbound : (∫ θ in Ioo (-Real.pi) Real.pi, ‖deriv (v ∘ circleMap a t) θ‖ ^ 2) ≤
      t * (∫ θ in Ioo (-Real.pi) Real.pi, t * ‖fderiv ℝ v (circleMap a t θ)‖ ^ 2) := by
    calc
      _ ≤ ∫ θ in Ioo (-Real.pi) Real.pi,
          t ^ 2 * ‖fderiv ℝ v (circleMap a t θ)‖ ^ 2 := by
        apply integral_mono_ae hIntDeriv (hInt.const_mul (t ^ 2))
        filter_upwards [hd] with θ hθ
        calc
          _ ≤ (t * ‖fderiv ℝ v (circleMap a t θ)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_deriv_comp_circleMap_le ht.le hθ) 2
          _ = _ := mul_pow _ _ _
      _ = _ := by rw [integral_const_mul, integral_const_mul]; ring
  apply (div_le_iff₀ ht).mpr
  simpa only [mul_comm] using hcircle.trans hbound

/-- Genuine zero/one values on every intermediate sphere force the sharp
annular lower bound for the actual real Fréchet-derivative energy. -/
theorem integral_sq_norm_fderiv_annulus_ge {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r)
    (hosc : ∀ t ∈ Ioo s r,
      (∃ z ∈ sphere a t, v z = 0) ∧ (∃ z ∈ sphere a t, v z = 1)) :
    (2 / Real.pi) * Real.log (r / s) ≤
      ∫ z in {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r}, ‖fderiv ℝ v z‖ ^ 2 := by
  have hf : Measurable (fun z : ℂ => ‖fderiv ℝ v z‖ ^ 2) :=
    (measurable_fderiv ℝ v).norm.pow_const 2
  have hf0 (z : ℂ) : 0 ≤ ‖fderiv ℝ v z‖ ^ 2 := sq_nonneg _
  have hfM (z : ℂ) : ‖fderiv ℝ v z‖ ^ 2 ≤ (K : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hv) 2
  rw [integral_annulus_eq_integral_radius_circleMap hf hf0 hfM a hs hsr]
  have hInt := integrableOn_radius_mul_circleMap hf hf0 hfM a hs hsr
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hInt
  have hrad := hInt.integral_prod_left
  have hinv : IntegrableOn (fun t : ℝ => (2 / Real.pi) / t) (Ioo s r) := by
    have hc : ContinuousOn (fun t : ℝ => (2 / Real.pi) / t) (Icc s r) :=
      continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hs.trans_le ht.1))
    exact hc.integrableOn_compact isCompact_Icc |>.mono_set Ioo_subset_Icc_self
  have heval : (∫ t in Ioo s r, (2 / Real.pi) / t) =
      (2 / Real.pi) * Real.log (r / s) := by
    simp_rw [div_eq_mul_inv]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hsr.le, integral_inv_of_pos hs (hs.trans hsr)]
    rfl
  rw [← heval]
  apply integral_mono_ae hinv hrad
  have hd := ae_restrict_of_ae_restrict_of_subset
    (show Ioo s r ⊆ Ioi (0 : ℝ) from fun t ht => hs.trans ht.1)
    (ae_ae_differentiableAt_circleMap hv a)
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
  exact integral_radius_sq_norm_fderiv_circleMap_ge hv (hs.trans ht.1)
    (hosc t ht).1 (hosc t ht).2 hdt

/-- Finite real annular energy and its oscillation lower bound, with no energy
or modulus assumption among the inputs. -/
theorem planar_annulus_oscillation_energy {v : ℂ → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (a : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r)
    (hosc : ∀ t ∈ Ioo s r,
      (∃ z ∈ sphere a t, v z = 0) ∧ (∃ z ∈ sphere a t, v z = 1)) :
    IntegrableOn (fun z : ℂ => ‖fderiv ℝ v z‖ ^ 2)
      {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r} ∧
    (2 / Real.pi) * Real.log (r / s) ≤
      ∫ z in {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r}, ‖fderiv ℝ v z‖ ^ 2 :=
  ⟨integrableOn_sq_norm_fderiv_annulus hv a s r,
    integral_sq_norm_fderiv_annulus_ge hv a hs hsr hosc⟩


/-- Local version on an honest larger closed ball. A scalar Lipschitz extension
is used only to apply the global theorem. Neighborhood equality on the source
annulus then identifies the actual derivatives. No global energy bound for
the extension, or global regularity of the original function, is asserted. -/
theorem planar_annulus_oscillation_energy_of_lipschitzOn_closedBall
    {v : ℂ → ℝ} {K : ℝ≥0} {a : ℂ} {s r R : ℝ}
    (hv : LipschitzOnWith K v (closedBall a R))
    (hs : 0 < s) (hsr : s < r) (hrR : r < R)
    (hosc : ∀ t ∈ Ioo s r,
      (∃ z ∈ sphere a t, v z = 0) ∧ (∃ z ∈ sphere a t, v z = 1)) :
    IntegrableOn (fun z : ℂ => ‖fderiv ℝ v z‖ ^ 2)
      {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r} ∧
    (2 / Real.pi) * Real.log (r / s) ≤
      ∫ z in {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r}, ‖fderiv ℝ v z‖ ^ 2 := by
  obtain ⟨g, hg, hvg⟩ := hv.extend_real
  have hoscg : ∀ t ∈ Ioo s r,
      (∃ z ∈ sphere a t, g z = 0) ∧ (∃ z ∈ sphere a t, g z = 1) := by
    intro t ht
    have hsub : sphere a t ⊆ closedBall a R := by
      intro z hz
      apply mem_closedBall.mpr
      rw [mem_sphere.mp hz]
      exact (ht.2.trans hrR).le
    obtain ⟨⟨z0, hz0, hv0⟩, ⟨z1, hz1, hv1⟩⟩ := hosc t ht
    exact ⟨⟨z0, hz0, (hvg (hsub hz0)).symm.trans hv0⟩,
      ⟨z1, hz1, (hvg (hsub hz1)).symm.trans hv1⟩⟩
  have hglobal := planar_annulus_oscillation_energy hg a hs hsr hoscg
  have hS : MeasurableSet {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  have hderiv : EqOn (fun z : ℂ => ‖fderiv ℝ g z‖ ^ 2)
      (fun z : ℂ => ‖fderiv ℝ v z‖ ^ 2)
      {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ < r} := by
    intro z hz
    have hzball : z ∈ ball a R := by
      simpa only [mem_ball, dist_eq_norm] using hz.2.trans hrR
    have he : v =ᶠ[𝓝 z] g := by
      filter_upwards [isOpen_ball.eventually_mem hzball] with x hx
      exact hvg (ball_subset_closedBall hx)
    dsimp only
    rw [he.fderiv_eq]
  refine ⟨hglobal.1.congr_fun hderiv hS, ?_⟩
  rw [setIntegral_congr_fun hS hderiv] at hglobal
  exact hglobal.2

end RepulsiveCoulomb.PaperRoute
