module

public import LeanResearch.RepulsiveCoulomb.PointWeightedVitali
public import LeanResearch.RepulsiveCoulomb.PointDyadicAveragingFubini

@[expose] public section

/-! A measurable bounded-radius dyadic maximal operator for the actual point
measure, with a configuration-uniform weak (1,1) estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointKernelAverage {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (r : ℝ) (g : ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (rawPointAveragingKernel a y r x z) * g z ∂rawPointMeasure a y

def rawPointDyadicMaximal {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (R : ℝ) (g : ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, rawPointKernelAverage a y (dyadicBallRadius R n) g x

theorem rawPointKernelAverage_eq {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {r : ℝ} (hr : 0 < r)
    (g : ℂ → ℝ≥0∞) (x : ℂ) :
    rawPointKernelAverage a y r g x = ⨍⁻ z in ball x r, g z ∂rawPointMeasure a y := by
  have hp : 0 < (rawPointMeasure a y).real (ball x r) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y x hr).ne'
      (rawPointMeasure_ball_lt_top ha y x r).ne
  have he : (fun z => ENNReal.ofReal (rawPointAveragingKernel a y r x z) * g z) =
      (ball x r).indicator (fun z =>
        ENNReal.ofReal ((rawPointMeasure a y).real (ball x r))⁻¹ * g z) := by
    ext z
    by_cases hz : z ∈ ball x r
    · simp [rawPointAveragingKernel, mem_ball.mp hz, hz]
    · have hz' : ¬ dist z x < r := hz
      simp [rawPointAveragingKernel, hz', hz]
  unfold rawPointKernelAverage
  rw [he, lintegral_indicator measurableSet_ball,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_inv_of_pos hp]
  rw [Measure.real, ENNReal.ofReal_toReal (rawPointMeasure_ball_lt_top ha y x r).ne,
    setLAverage_eq, div_eq_mul_inv, mul_comm]

theorem measurable_rawPointKernelAverage {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (r : ℝ)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (rawPointKernelAverage a y r g) := by
  letI := rawPointMeasure_locallyFinite ha y
  exact ((measurable_rawPointAveragingKernel ha y r).ennreal_ofReal.mul
    (hg.comp measurable_snd)).lintegral_prod_right'

theorem measurable_rawPointDyadicMaximal {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (R : ℝ)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (rawPointDyadicMaximal a y R g) := by
  exact Measurable.iSup (fun n => measurable_rawPointKernelAverage ha y _ hg)

theorem rawPointDyadicMaximal_weak_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {R : ℝ} (hR : 0 < R) (g : ℂ → ℝ≥0∞) (t : ℝ≥0∞) :
    t * rawPointMeasure a y {x | t < rawPointDyadicMaximal a y R g x} ≤
      ENNReal.ofReal (rawPointFourfoldConstant Q) * ∫⁻ z, g z ∂rawPointMeasure a y := by
  apply rawPointMeasure_vitali_weak_bound ha hQ y (R := R)
  intro x hx
  change t < ⨆ n : ℕ, rawPointKernelAverage a y (dyadicBallRadius R n) g x at hx
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hx
  refine ⟨dyadicBallRadius R n, ⟨dyadicBallRadius_pos hR n, dyadicBallRadius_le hR.le n⟩, ?_⟩
  rw [rawPointKernelAverage_eq ha y (dyadicBallRadius_pos hR n), setLAverage_eq] at hn
  exact (ENNReal.mul_lt_of_lt_div hn).le

theorem rawPointDyadicMaximal_le_of_bound {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ≥0∞} {b : ℝ≥0∞} (hb : ∀ z, g z ≤ b) (x : ℂ) :
    rawPointDyadicMaximal a y R g x ≤ b := by
  apply iSup_le
  intro n
  rw [rawPointKernelAverage_eq ha y (dyadicBallRadius_pos hR n)]
  calc
    _ ≤ ⨍⁻ z in ball x (dyadicBallRadius R n), b ∂rawPointMeasure a y :=
      laverage_mono_ae (Filter.Eventually.of_forall hb)
    _ = b := setLAverage_const
      (rawPointMeasure_ball_pos ha y x (dyadicBallRadius_pos hR n)).ne'
      (rawPointMeasure_ball_lt_top ha y x _).ne b

theorem rawPointDyadicMaximal_lt_top_of_bound {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ≥0∞} {b : ℝ≥0∞} (hb : ∀ z, g z ≤ b) (hbt : b < ⊤) (x : ℂ) :
    rawPointDyadicMaximal a y R g x < ⊤ :=
  (rawPointDyadicMaximal_le_of_bound ha y hR hb x).trans_lt hbt

end RepulsiveCoulomb
