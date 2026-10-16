module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Ordinary planar Lipschitz ball Poincaré

The derivative is the actual real Fréchet derivative. The proof uses
Rademacher, affine null-set transport, Fubini and the fundamental theorem of
calculus on the half segment from the midpoint to an endpoint. No weighted
Poincaré or point-grid theorem is used.
-/

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology Pointwise
namespace RepulsiveCoulomb.PaperRoute.EuclideanBall

/-- The real differential norm is precisely the Euclidean gradient norm. -/
theorem norm_gradient_eq_norm_fderiv (g : ℂ → ℝ) (z : ℂ) :
    ‖gradient g z‖ = ‖fderiv ℝ g z‖ :=
  (InnerProductSpace.toDual ℝ ℂ).symm.norm_map _

private theorem integrable_of_measurable_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {q : α → ℝ} {M : ℝ}
    (hq : Measurable q) (hM : ∀ z, ‖q z‖ ≤ M) : Integrable q μ :=
  (integrable_const M).mono' hq.aestronglyMeasurable (Eventually.of_forall hM)

/-- All actual differential norms are integrable on finite measure sets. -/
theorem integrable_norm_fderiv {g : ℂ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (fun z => ‖fderiv ℝ g z‖) μ :=
  integrable_of_measurable_bounded μ (measurable_fderiv ℝ g).norm
    (fun z => by simpa only [norm_norm] using norm_fderiv_le_of_lipschitz ℝ hg)

private theorem continuous_lineMap_pair (x : ℂ) :
    Continuous (fun p : ℝ × ℂ => AffineMap.lineMap x p.2 p.1) := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

/-- An invertible affine dilation transports planar null sets. -/
theorem quasiMeasurePreserving_lineMap_right (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Measure.QuasiMeasurePreserving (fun y : ℂ => AffineMap.lineMap x y t) volume volume := by
  simpa only [Function.comp_def, AffineMap.lineMap_apply_module] using
    (quasiMeasurePreserving_add_left (volume : Measure ℂ) ((1 - t) • x)).comp
      (Measure.quasiMeasurePreserving_smul volume ht)

/-- For every fixed first endpoint, almost every second endpoint has the
actual planar derivative at almost every half-segment parameter. -/
theorem ae_ae_differentiableAt_lineMap {g : ℂ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (x c : ℂ) (r : ℝ) :
    ∀ᵐ y ∂volume.restrict (ball c r),
      ∀ᵐ t ∂volume.restrict (Ioc (1 / 2 : ℝ) 1),
        DifferentiableAt ℝ g (AffineMap.lineMap x y t) := by
  have hm : MeasurableSet {p : ℝ × ℂ |
      DifferentiableAt ℝ g (AffineMap.lineMap x p.2 p.1)} :=
    (measurableSet_of_differentiableAt ℝ g).preimage
      (continuous_lineMap_pair x).measurable
  apply (Measure.ae_ae_comm hm).mp
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ae_restrict_of_ae
    ((quasiMeasurePreserving_lineMap_right x (by linarith [ht.1] : t ≠ 0)).ae hg.ae_differentiableAt)

/-- The half-segment FTC estimate uses the actual chain rule only at the
a.e. differentiability points supplied by affine transport and Fubini. -/
theorem ae_half_segment_estimate {g : ℂ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (x c : ℂ) (r : ℝ) :
    ∀ᵐ y ∂volume.restrict (ball c r),
      |g y - g (AffineMap.lineMap x y (1 / 2 : ℝ))| ≤
        ‖y - x‖ * ∫ t in Ioc (1 / 2 : ℝ) 1,
          ‖fderiv ℝ g (AffineMap.lineMap x y t)‖ := by
  filter_upwards [ae_ae_differentiableAt_lineMap hg x c r] with y hy
  let w : ℝ → ℝ := g ∘ AffineMap.lineMap x y
  have hLip : LipschitzWith (K * nndist x y) w :=
    hg.comp (lipschitzWith_lineMap x y)
  have hAC : AbsolutelyContinuousOnInterval w (1 / 2) 1 :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hq : IntegrableOn (fun t : ℝ =>
      ‖fderiv ℝ g (AffineMap.lineMap x y t)‖) (Ioc (1 / 2 : ℝ) 1) := by
    apply integrable_of_measurable_bounded
    · exact (measurable_fderiv ℝ g).norm.comp
        (lipschitzWith_lineMap x y).continuous.measurable
    · intro t
      simpa only [norm_norm] using norm_fderiv_le_of_lipschitz ℝ hg
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc (1 / 2 : ℝ) 1),
      |deriv w t| ≤ ‖y - x‖ * ‖fderiv ℝ g (AffineMap.lineMap x y t)‖ := by
    filter_upwards [hy] with t ht
    rw [show deriv w t = (fderiv ℝ g (AffineMap.lineMap x y t)) (y - x) from
      (ht.hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap).deriv]
    simpa only [← Real.norm_eq_abs, mul_comm] using
      (ContinuousLinearMap.le_opNorm (fderiv ℝ g (AffineMap.lineMap x y t)) (y - x))
  calc
    |g y - g (AffineMap.lineMap x y (1 / 2 : ℝ))|
        = |∫ t in (1 / 2 : ℝ)..1, deriv w t| := by
          rw [hAC.integral_deriv_eq_sub]
          simp [w]
    _ ≤ ∫ t in (1 / 2 : ℝ)..1, |deriv w t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ = ∫ t in Ioc (1 / 2 : ℝ) 1, |deriv w t| :=
      intervalIntegral.integral_of_le (by norm_num)
    _ ≤ ∫ t in Ioc (1 / 2 : ℝ) 1,
        ‖y - x‖ * ‖fderiv ℝ g (AffineMap.lineMap x y t)‖ :=
      integral_mono_ae
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
          hAC.intervalIntegrable_deriv.abs)
        (hq.const_mul _) hderiv
    _ = _ := integral_const_mul _ _

/-- The inverse affine planar Jacobian on the half segment is at most four. -/
theorem integral_lineMap_right_le {q : ℂ → ℝ} {M : ℝ}
    (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqM : ∀ z, q z ≤ M)
    {x c : ℂ} {r t : ℝ} (hx : x ∈ ball c r) (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    (∫ y in ball c r, q (AffineMap.lineMap x y t)) ≤
      4 * ∫ z in ball c r, q z := by
  let B := ball c r
  let Q := B.indicator q
  have hB : MeasurableSet B := measurableSet_ball
  have : IsFiniteMeasure (volume.restrict B) := ⟨by simpa [B] using (measure_ball_lt_top (μ := volume) (x := c) (r := r))⟩
  have hqi : IntegrableOn q B :=
    integrable_of_measurable_bounded _ hq
      (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hq0 z)]; exact hqM z)
  have hQi : Integrable Q := (integrable_indicator_iff hB).2 hqi
  have ht0 : 0 < t := by linarith [ht.1]
  have hcomp : Integrable (fun y : ℂ => Q (AffineMap.lineMap x y t)) := by
    simpa only [AffineMap.lineMap_apply_module] using
      (hQi.comp_add_left ((1 - t) • x)).comp_smul ht0.ne'
  calc
    (∫ y in B, q (AffineMap.lineMap x y t))
        = ∫ y in B, Q (AffineMap.lineMap x y t) := by
          apply setIntegral_congr_fun hB
          intro y hy
          exact (indicator_of_mem ((convex_ball c r).lineMap_mem hx hy
            ⟨by linarith [ht.1], ht.2⟩) q).symm
    _ ≤ ∫ y : ℂ, Q (AffineMap.lineMap x y t) :=
      setIntegral_le_integral hcomp (Eventually.of_forall (fun y =>
        indicator_nonneg (fun z _ => hq0 z) _))
    _ = (t ^ 2)⁻¹ * ∫ z in B, q z := by
      simp only [AffineMap.lineMap_apply_module]
      change (∫ y : ℂ, (fun z => Q ((1 - t) • x + z)) (t • y)) = _
      have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
        (fun z : ℂ => Q ((1 - t) • x + z)) t (hR := ht0.le)
      simpa only [Complex.finrank_real_complex, smul_eq_mul,
        integral_add_left_eq_self, Q, integral_indicator hB] using hs
    _ ≤ 4 * ∫ z in B, q z := by
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg hq0)
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (sq_pos_of_pos ht0)).2
      nlinarith [ht.1]

private theorem continuous_integrableOn_ball {f : ℂ → ℝ} (hf : Continuous f)
    (c : ℂ) (r : ℝ) : IntegrableOn f (ball c r) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall

private theorem continuous_integrable_ball_product {f : ℂ × ℂ → ℝ}
    (hf : Continuous f) (c : ℂ) (r : ℝ) :
    Integrable f ((volume.restrict (ball c r)).prod (volume.restrict (ball c r))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact
    ((isCompact_closedBall c r).prod (isCompact_closedBall c r))).mono_set
      (prod_mono ball_subset_closedBall ball_subset_closedBall)

private theorem norm_sub_le_two_radius {x y c : ℂ} {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) : ‖y - x‖ ≤ 2 * r := by
  have hx' : dist c x < r := by simpa only [mem_ball, dist_comm] using hx
  have hy' : dist y c < r := hy
  rw [← dist_eq_norm]
  exact (dist_triangle y c x).trans (by linarith)

/-- Integration over the moving endpoint and half-segment parameter produces
an actual endpoint-to-midpoint estimate, with constant four. -/
theorem integral_half_oscillation_le {g : ℂ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {x c : ℂ} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ ball c r) :
    (∫ y in ball c r, |g y - g (AffineMap.lineMap x y (1 / 2 : ℝ))|) ≤
      4 * r * ∫ z in ball c r, ‖fderiv ℝ g z‖ := by
  let ν := volume.restrict (ball c r)
  let τ := volume.restrict (Ioc (1 / 2 : ℝ) 1)
  let q : ℂ → ℝ := fun z => ‖fderiv ℝ g z‖
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using
    (measure_ball_lt_top (μ := volume) (x := c) (r := r))⟩
  have : IsFiniteMeasure τ := by dsimp [τ]; infer_instance
  have hq : Measurable q := (measurable_fderiv ℝ g).norm
  have hprod : Integrable
      (fun p : ℂ × ℝ => q (AffineMap.lineMap x p.1 p.2)) (ν.prod τ) := by
    apply integrable_of_measurable_bounded
    · exact hq.comp ((continuous_lineMap_pair x).comp continuous_swap).measurable
    · intro p
      simpa only [q, norm_norm] using norm_fderiv_le_of_lipschitz ℝ hg
  have hhalf : Integrable
      (fun y => |g y - g (AffineMap.lineMap x y (1 / 2 : ℝ))|) ν := by
    apply continuous_integrableOn_ball _ c r
    apply Continuous.abs
    apply hg.continuous.sub
    apply hg.continuous.comp
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hfirst : (∫ y, |g y - g (AffineMap.lineMap x y (1 / 2 : ℝ))| ∂ν) ≤
      2 * r * ∫ y, ∫ t, q (AffineMap.lineMap x y t) ∂τ ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae hhalf (hprod.integral_prod_left.const_mul _)
    filter_upwards [ae_half_segment_estimate hg x c r,
      ae_restrict_mem measurableSet_ball] with y hy hyB
    exact hy.trans (mul_le_mul_of_nonneg_right (norm_sub_le_two_radius hx hyB)
      (integral_nonneg (fun _ => norm_nonneg _)))
  have hsecond : (∫ t, ∫ y, q (AffineMap.lineMap x y t) ∂ν ∂τ) ≤
      2 * ∫ z in ball c r, q z := by
    calc
      _ ≤ ∫ t, (4 : ℝ) * (∫ z in ball c r, q z) ∂τ := by
        apply integral_mono_ae hprod.integral_prod_right (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact integral_lineMap_right_le hq (fun z => norm_nonneg _)
          (fun z => norm_fderiv_le_of_lipschitz ℝ hg) hx ⟨ht.1.le, ht.2⟩
      _ = _ := by
        rw [integral_const]
        norm_num [τ, smul_eq_mul]
        ring
  calc
    _ ≤ 2 * r * ∫ y, ∫ t, q (AffineMap.lineMap x y t) ∂τ ∂ν := hfirst
    _ = 2 * r * ∫ t, ∫ y, q (AffineMap.lineMap x y t) ∂ν ∂τ := by
      rw [integral_integral_swap hprod]
    _ ≤ 2 * r * (2 * ∫ z in ball c r, q z) :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = _ := by dsimp [q]; ring

private theorem lineMap_half_comm (x y : ℂ) :
    AffineMap.lineMap x y (1 / 2 : ℝ) = AffineMap.lineMap y x (1 / 2 : ℝ) := by
  simp only [AffineMap.lineMap_apply_module]
  norm_num
  exact add_comm _ _

/-- The genuine unnormalized double oscillation estimate. -/
theorem integral_integral_oscillation_le {g : ℂ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball c r, ∫ y in ball c r, |g x - g y|) ≤
      8 * r * volume.real (ball c r) * ∫ z in ball c r, ‖fderiv ℝ g z‖ := by
  let ν := volume.restrict (ball c r)
  let H : ℂ → ℂ → ℝ := fun x y =>
    |g y - g (AffineMap.lineMap x y (1 / 2 : ℝ))|
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using
    (measure_ball_lt_top (μ := volume) (x := c) (r := r))⟩
  have hm : Continuous (fun p : ℂ × ℂ => AffineMap.lineMap p.1 p.2 (1 / 2 : ℝ)) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hHc : Continuous (Function.uncurry H) :=
    ((hg.continuous.comp continuous_snd).sub (hg.continuous.comp hm)).abs
  have hHi : Integrable (Function.uncurry H) (ν.prod ν) :=
    continuous_integrable_ball_product hHc c r
  have hgi : Integrable g ν := continuous_integrableOn_ball hg.continuous c r
  have hdi : Integrable (fun p : ℂ × ℂ => |g p.1 - g p.2|) (ν.prod ν) :=
    ((hgi.comp_fst ν).sub (hgi.comp_snd ν)).abs
  have htri (x y : ℂ) : |g x - g y| ≤ H x y + H y x := by
    have h := abs_sub_le (g x) (g (AffineMap.lineMap x y (1 / 2 : ℝ))) (g y)
    simpa only [H, lineMap_half_comm y x, abs_sub_comm (g y),
      add_comm] using h
  have hpoint (x : ℂ) : (∫ y, |g x - g y| ∂ν) ≤
      (∫ y, H x y ∂ν) + ∫ y, H y x ∂ν := by
    have h1 : Integrable (H x) ν :=
      continuous_integrableOn_ball (hHc.comp (continuous_const.prodMk continuous_id)) c r
    have h2 : Integrable (fun y => H y x) ν :=
      continuous_integrableOn_ball (hHc.comp (continuous_id.prodMk continuous_const)) c r
    rw [← integral_add h1 h2]
    exact integral_mono_ae ((integrable_const _).sub hgi).abs (h1.add h2)
      (Eventually.of_forall (htri x))
  have hhalf : (∫ x, ∫ y, H x y ∂ν ∂ν) ≤
      volume.real (ball c r) * (4 * r * ∫ z in ball c r, ‖fderiv ℝ g z‖) := by
    calc
      _ ≤ ∫ x, (4 * r * ∫ z in ball c r, ‖fderiv ℝ g z‖) ∂ν := by
        apply integral_mono_ae hHi.integral_prod_left (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact integral_half_oscillation_le hg hr hx
      _ = _ := by simp [ν, integral_const, smul_eq_mul]
  calc
    _ ≤ ∫ x, ((∫ y, H x y ∂ν) + ∫ y, H y x ∂ν) ∂ν :=
      integral_mono_ae hdi.integral_prod_left
        (hHi.integral_prod_left.add hHi.integral_prod_right)
        (Eventually.of_forall hpoint)
    _ = 2 * ∫ x, ∫ y, H x y ∂ν ∂ν := by
      rw [integral_add (f := fun x => ∫ y, H x y ∂ν)
        (g := fun x => ∫ y, H y x ∂ν) hHi.integral_prod_left hHi.integral_prod_right,
        ← integral_integral_swap hHi]
      ring
    _ ≤ 2 * (volume.real (ball c r) *
        (4 * r * ∫ z in ball c r, ‖fderiv ℝ g z‖)) :=
      mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = _ := by ring

/-- Ordinary planar ball L1 Poincaré for a genuine globally Lipschitz scalar,
with exact constant eight and the actual Euclidean differential. -/
theorem integral_abs_sub_average_le {g : ℂ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball c r, |g x - (⨍ z in ball c r, g z)|) ≤
      8 * r * ∫ z in ball c r, ‖fderiv ℝ g z‖ := by
  let ν := volume.restrict (ball c r)
  let M := volume.real (ball c r)
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using
    (measure_ball_lt_top (μ := volume) (x := c) (r := r))⟩
  have hM : 0 < M := ENNReal.toReal_pos
    (measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne
  have : NeZero ν := ⟨by
    intro hz
    have hzero : volume (ball c r) = 0 := by
      simpa [ν] using congrArg (fun η : Measure ℂ => η univ) hz
    exact (measure_ball_pos volume c hr).ne' hzero⟩
  have hgi : Integrable g ν := continuous_integrableOn_ball hg.continuous c r
  have hprod : Integrable (fun p : ℂ × ℂ => |g p.1 - g p.2|) (ν.prod ν) :=
    ((hgi.comp_fst ν).sub (hgi.comp_snd ν)).abs
  have hpoint (x : ℂ) : |g x - (⨍ y, g y ∂ν)| ≤
      M⁻¹ * ∫ y, |g x - g y| ∂ν := by
    have h : |g x - (⨍ y, g y ∂ν)| ≤ ⨍ y, |g x - g y| ∂ν := by
      calc
        _ = |⨍ y, g x - g y ∂ν| := by
          rw [average_fun_sub (integrable_const _) hgi, average_const]
        _ ≤ _ := norm_integral_le_integral_norm (fun y => g x - g y)
    simpa only [average_eq, smul_eq_mul, ν, measureReal_restrict_apply_univ, M] using h
  calc
    _ ≤ ∫ x, M⁻¹ * (∫ y, |g x - g y| ∂ν) ∂ν := by
      apply integral_mono_ae ((hgi.sub (integrable_const _)).abs)
        (hprod.integral_prod_left.const_mul _)
      exact Eventually.of_forall hpoint
    _ = M⁻¹ * ∫ x, ∫ y, |g x - g y| ∂ν ∂ν := integral_const_mul _ _
    _ ≤ M⁻¹ * (8 * r * M * ∫ z in ball c r, ‖fderiv ℝ g z‖) :=
      mul_le_mul_of_nonneg_left (integral_integral_oscillation_le hg c hr) (inv_nonneg.mpr hM.le)
    _ = _ := by field_simp

/-- The same estimate for a scalar Lipschitz only on the closed ball. The
extension agrees on the open ball as a germ, so its actual derivatives agree. -/
theorem integral_abs_sub_average_le_of_lipschitzOn_closedBall
    {g : ℂ → ℝ} {K : ℝ≥0} {c : ℂ} {r : ℝ}
    (hg : LipschitzOnWith K g (closedBall c r)) (hr : 0 < r) :
    (∫ x in ball c r, |g x - (⨍ z in ball c r, g z)|) ≤
      8 * r * ∫ z in ball c r, ‖fderiv ℝ g z‖ := by
  obtain ⟨G, hG, hEq⟩ := hg.extend_real
  have hderiv (z : ℂ) (hz : z ∈ ball c r) : fderiv ℝ g z = fderiv ℝ G z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact hEq (ball_subset_closedBall hy)
  have hmean : (⨍ z in ball c r, g z) = ⨍ z in ball c r, G z := by
    simp only [setAverage_eq]
    congr 1
    exact setIntegral_congr_fun measurableSet_ball (hEq.mono ball_subset_closedBall)
  have hleft : (∫ x in ball c r, |g x - (⨍ z in ball c r, g z)|) =
      ∫ x in ball c r, |G x - (⨍ z in ball c r, G z)| := by
    rw [hmean]
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hEq (ball_subset_closedBall hx)]
  have hright : (∫ z in ball c r, ‖fderiv ℝ g z‖) =
      ∫ z in ball c r, ‖fderiv ℝ G z‖ := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [hderiv z hz]
  rw [hleft, hright]
  exact integral_abs_sub_average_le hG c hr

/-- All quantities in the local Poincaré inequality are genuine finite
integrals, even if the scalar is unrestricted outside the closed ball. -/
theorem integrableOn_ball_data_of_lipschitzOn_closedBall
    {g : ℂ → ℝ} {K : ℝ≥0} {c : ℂ} {r : ℝ}
    (hg : LipschitzOnWith K g (closedBall c r)) :
    IntegrableOn g (ball c r) ∧
      IntegrableOn (fun x => |g x - (⨍ z in ball c r, g z)|) (ball c r) ∧
      IntegrableOn (fun z => ‖fderiv ℝ g z‖) (ball c r) := by
  obtain ⟨G, hG, hEq⟩ := hg.extend_real
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by
    simpa using (measure_ball_lt_top (μ := volume) (x := c) (r := r))⟩
  have hgi : IntegrableOn g (ball c r) :=
    (continuous_integrableOn_ball hG.continuous c r).congr_fun
      (hEq.symm.mono ball_subset_closedBall) measurableSet_ball
  refine ⟨hgi, (hgi.sub (integrable_const _)).abs, ?_⟩
  apply (integrable_norm_fderiv hG (volume.restrict (ball c r))).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hlocal : G =ᶠ[𝓝 z] g := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact (hEq (ball_subset_closedBall hy)).symm
  rw [hlocal.fderiv_eq]

/-- Actual physical-gradient form, including every real radius. Nonpositive
radii have empty open balls, so both integrals vanish. -/
theorem integral_abs_sub_average_le_gradient_of_lipschitzOn_closedBall
    {g : ℂ → ℝ} {K : ℝ≥0} {c : ℂ} {r : ℝ}
    (hg : LipschitzOnWith K g (closedBall c r)) :
    (∫ x in ball c r, |g x - (⨍ z in ball c r, g z)|) ≤
      8 * r * ∫ z in ball c r, ‖gradient g z‖ := by
  simp only [norm_gradient_eq_norm_fderiv]
  by_cases hr : 0 < r
  · exact integral_abs_sub_average_le_of_lipschitzOn_closedBall hg hr
  · simp [ball_eq_empty.mpr (le_of_not_gt hr)]

end RepulsiveCoulomb.PaperRoute.EuclideanBall
