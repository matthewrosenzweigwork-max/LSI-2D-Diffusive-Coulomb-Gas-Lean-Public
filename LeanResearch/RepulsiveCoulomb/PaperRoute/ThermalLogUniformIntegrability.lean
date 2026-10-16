import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! The direct-method negative-log tail producer. All real integrals used in
estimates have separately established integrability. Atoms, including diagonal
atoms, are allowed. This is not a thermal existence or regularity theorem. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology BoundedContinuousFunction
namespace RepulsiveCoulomb.PaperRoute

/-- The magnitude of the negative part of the physical logarithmic interaction. -/
def thermalNegativeLogKernel (p : ℂ × ℂ) : ℝ := Real.log (max 1 (dist p.1 p.2))

def thermalTruncatedLogKernel (L : ℝ) (p : ℂ × ℂ) : ℝ :=
  min (thermalNegativeLogKernel p) L

theorem thermalNegativeLogKernel_nonneg (p : ℂ × ℂ) :
    0 ≤ thermalNegativeLogKernel p :=
  Real.log_nonneg (le_max_left _ _)

theorem thermalNegativeLogKernel_continuous : Continuous thermalNegativeLogKernel := by
  unfold thermalNegativeLogKernel
  apply Continuous.log (continuous_const.max (continuous_fst.dist continuous_snd))
  intro p
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- A scalar estimate with its nonnegativity, before any integration. -/
theorem thermal_log_truncation_scalar {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L) :
    0 ≤ Real.log (max 1 r) - min (Real.log (max 1 r)) L ∧
    Real.log (max 1 r) - min (Real.log (max 1 r)) L ≤ Real.exp (-L) * r ^ 2 := by
  constructor
  · exact sub_nonneg.mpr (min_le_left _ _)
  by_cases h : Real.log (max 1 r) ≤ L
  · rw [min_eq_left h, sub_self]
    positivity
  · have hlog : L < Real.log (max 1 r) := lt_of_not_ge h
    have hr1 : 1 < r := by
      by_contra h1
      have : r ≤ 1 := le_of_not_gt h1
      rw [max_eq_left this, Real.log_one] at hlog
      linarith
    rw [max_eq_right hr1.le] at hlog ⊢
    rw [min_eq_right hlog.le]
    have hexp : Real.exp L ≤ r := ((Real.lt_log_iff_exp_lt (lt_trans zero_lt_one hr1)).mp hlog).le
    have hone : 1 ≤ Real.exp (-L) * r := by
      calc
        1 = Real.exp (-L) * Real.exp L := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp (-L) * r := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    have hm := mul_le_mul_of_nonneg_right hone hr
    have hl := Real.log_le_self hr
    nlinarith

def thermalBoundedLogTruncation (L : ℝ) (hL : 0 ≤ L) : (ℂ × ℂ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (thermalTruncatedLogKernel L)
    (thermalNegativeLogKernel_continuous.min continuous_const) L (fun p => by
      change |min (thermalNegativeLogKernel p) L| ≤ L
      rw [abs_of_nonneg (le_min (thermalNegativeLogKernel_nonneg p) hL)]
      exact min_le_right _ _)

theorem thermalTruncatedLogKernel_integrable (μ : ProbabilityMeasure ℂ)
    {L : ℝ} (hL : 0 ≤ L) :
    Integrable (thermalTruncatedLogKernel L) ((μ : Measure ℂ).prod μ) := by
  apply Integrable.of_bound
    (thermalNegativeLogKernel_continuous.min continuous_const).measurable.aestronglyMeasurable L
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (thermalNegativeLogKernel_nonneg p) hL)]
    exact min_le_right _ _

theorem thermal_dist_sq_le (p : ℂ × ℂ) :
    dist p.1 p.2 ^ 2 ≤ 2 * ‖p.1‖ ^ 2 + 2 * ‖p.2‖ ^ 2 := by
  rw [dist_eq_norm]
  have h := norm_sub_le p.1 p.2
  have h0 := norm_nonneg (p.1 - p.2)
  nlinarith [sq_nonneg (‖p.1‖ - ‖p.2‖)]

theorem thermal_product_dist_sq_integrable (μ : ProbabilityMeasure ℂ)
    (hμ : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    Integrable (fun p : ℂ × ℂ => dist p.1 p.2 ^ 2) ((μ : Measure ℂ).prod μ) := by
  apply ((hμ.comp_fst (μ : Measure ℂ)).const_mul 2 |>.add
    ((hμ.comp_snd (μ : Measure ℂ)).const_mul 2)).mono'
    ((continuous_fst.dist continuous_snd).pow 2).measurable.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact thermal_dist_sq_le p

theorem thermal_product_dist_sq_integral_le (μ : ProbabilityMeasure ℂ)
    (hμ : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) {M : ℝ}
    (hM : (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M) :
    (∫ p : ℂ × ℂ, dist p.1 p.2 ^ 2 ∂((μ : Measure ℂ).prod μ)) ≤ 4 * M := by
  have hi1 := (hμ.comp_fst (μ : Measure ℂ)).const_mul 2
  have hi2 := (hμ.comp_snd (μ : Measure ℂ)).const_mul 2
  calc
    _ ≤ ∫ p : ℂ × ℂ, (2 * ‖p.1‖ ^ 2 + 2 * ‖p.2‖ ^ 2) ∂((μ : Measure ℂ).prod μ) :=
      integral_mono (thermal_product_dist_sq_integrable μ hμ) (hi1.add hi2) thermal_dist_sq_le
    _ = 4 * (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) := by
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
        integral_fun_fst (fun x : ℂ => ‖x‖ ^ 2), integral_fun_snd (fun x : ℂ => ‖x‖ ^ 2)]
      simp
      ring
    _ ≤ 4 * M := by linarith

theorem thermalNegativeLogKernel_integrable (μ : ProbabilityMeasure ℂ)
    (hμ : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    Integrable thermalNegativeLogKernel ((μ : Measure ℂ).prod μ) := by
  apply (thermal_product_dist_sq_integrable μ hμ).mono'
    thermalNegativeLogKernel_continuous.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (thermalNegativeLogKernel_nonneg p)]
    have h := (thermal_log_truncation_scalar (dist_nonneg (x := p.1) (y := p.2)) (le_refl 0)).2
    change thermalNegativeLogKernel p - min (thermalNegativeLogKernel p) 0 ≤ _ at h
    simpa only [min_eq_right (thermalNegativeLogKernel_nonneg p), sub_zero, neg_zero, Real.exp_zero, one_mul] using h

/-- The actual integrated tail, uniform under a genuine second-moment bound. -/
theorem thermal_log_integral_tail_le (μ : ProbabilityMeasure ℂ)
    (hμ : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) {M L : ℝ}
    (hM : (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M) (hL : 0 ≤ L) :
    Integrable (fun p => thermalNegativeLogKernel p - thermalTruncatedLogKernel L p)
      ((μ : Measure ℂ).prod μ) ∧
    (∫ p, thermalNegativeLogKernel p - thermalTruncatedLogKernel L p
      ∂((μ : Measure ℂ).prod μ)) ≤ 4 * M * Real.exp (-L) := by
  have hi := (thermalNegativeLogKernel_integrable μ hμ).sub (thermalTruncatedLogKernel_integrable μ hL)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ p : ℂ × ℂ, Real.exp (-L) * dist p.1 p.2 ^ 2 ∂((μ : Measure ℂ).prod μ) :=
      integral_mono hi ((thermal_product_dist_sq_integrable μ hμ).const_mul _) (fun p =>
        (thermal_log_truncation_scalar dist_nonneg hL).2)
    _ = Real.exp (-L) * (∫ p : ℂ × ℂ, dist p.1 p.2 ^ 2 ∂((μ : Measure ℂ).prod μ)) := integral_const_mul _ _
    _ ≤ Real.exp (-L) * (4 * M) := mul_le_mul_of_nonneg_left
      (thermal_product_dist_sq_integral_le μ hμ hM) (Real.exp_pos _).le
    _ = _ := by ring

/-- Absolute error for the actual Bochner integrals, derived only after both
integrands have been shown integrable. -/
theorem thermal_log_integral_truncation_dist_le (μ : ProbabilityMeasure ℂ)
    (hμ : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) {M L : ℝ}
    (hM : (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M) (hL : 0 ≤ L) :
    dist (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ))
      (∫ p, thermalTruncatedLogKernel L p ∂((μ : Measure ℂ).prod μ)) ≤
        4 * M * Real.exp (-L) := by
  rw [Real.dist_eq, ← integral_sub (thermalNegativeLogKernel_integrable μ hμ)
    (thermalTruncatedLogKernel_integrable μ hL)]
  rw [abs_of_nonneg (integral_nonneg (fun p => sub_nonneg.mpr (min_le_left _ _)))]
  exact (thermal_log_integral_tail_le μ hμ hM hL).2

/-- Genuine weak-product convergence tested against the bounded continuous
logarithmic truncation. -/
theorem thermal_truncated_log_integral_tendsto {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}
    (hweak : Tendsto μs l (𝓝 μ)) {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun i => ∫ p, thermalTruncatedLogKernel L p
        ∂(((μs i) : Measure ℂ).prod (μs i))) l
      (𝓝 (∫ p, thermalTruncatedLogKernel L p ∂((μ : Measure ℂ).prod μ))) := by
  have hp : Tendsto (fun i => (μs i).prod (μs i)) l (𝓝 (μ.prod μ)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hweak.prodMk_nhds hweak)
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (thermalBoundedLogTruncation L hL)).continuousAt.tendsto.comp hp

/-- Negative logarithmic interaction is continuous under weak convergence and
uniform genuine second moments. Here the limit's moment assumptions are explicit;
no convergence or uniform-integrability certificate is assumed. -/
theorem thermal_negative_log_integral_tendsto {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M : ℝ}
    (hweak : Tendsto μs l (𝓝 μ))
    (hμs : ∀ i, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs i))
    (hMs : ∀ i, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs i)) ≤ M)
    (hμ : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ)
    (hM : (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M) :
    Tendsto (fun i => ∫ p, thermalNegativeLogKernel p
        ∂(((μs i) : Measure ℂ).prod (μs i))) l
      (𝓝 (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlim : Tendsto (fun L : ℝ => 4 * M * Real.exp (-L)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (4 * M)
  obtain ⟨L, hL, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by linarith)))).exists
  have ht := Metric.tendsto_nhds.mp (thermal_truncated_log_integral_tendsto hweak hL)
    (ε / 3) (by linarith)
  filter_upwards [ht] with i hi
  have h1 := thermal_log_integral_truncation_dist_le (μs i) (hμs i) (hMs i) hL
  have h2 := thermal_log_integral_truncation_dist_le μ hμ hM hL
  have htri := dist_triangle4
    (∫ p, thermalNegativeLogKernel p ∂(((μs i) : Measure ℂ).prod (μs i)))
    (∫ p, thermalTruncatedLogKernel L p ∂(((μs i) : Measure ℂ).prod (μs i)))
    (∫ p, thermalTruncatedLogKernel L p ∂((μ : Measure ℂ).prod μ))
    (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ))
  rw [dist_comm (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ))] at h2
  linarith

/-- Bounded continuous second-moment truncation used to derive, rather than
postulate, moment integrability at a weak limit. -/
def thermalBoundedMomentTruncation (n : ℕ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (n : ℝ) (‖x‖ ^ 2))
    (continuous_const.min (continuous_norm.pow 2)) (n : ℝ) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg n) (sq_nonneg _))]
      exact min_le_left _ _)

theorem thermalBoundedMomentTruncation_integrable (n : ℕ) (μ : ProbabilityMeasure ℂ) :
    Integrable (thermalBoundedMomentTruncation n) μ := by
  apply Integrable.of_bound (thermalBoundedMomentTruncation n).continuous.measurable.aestronglyMeasurable (n : ℝ)
  exact Eventually.of_forall fun x => by
    change |min (n : ℝ) (‖x‖ ^ 2)| ≤ n
    rw [abs_of_nonneg (le_min (Nat.cast_nonneg n) (sq_nonneg _))]
    exact min_le_left _ _

/-- Weak limits retain the genuine finite second-moment bound. This proof uses
bounded continuous tests and monotone convergence of nonnegative integrals. -/
theorem thermal_secondMoment_of_weak_convergence {ι : Type*} {l : Filter ι} [NeBot l]
    {μs : ι → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M : ℝ}
    (hweak : Tendsto μs l (𝓝 μ))
    (hμs : ∀ i, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs i))
    (hMs : ∀ i, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs i)) ≤ M) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧ (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M := by
  have hb (n : ℕ) : (∫ x, thermalBoundedMomentTruncation n x ∂μ) ≤ M := by
    apply le_of_tendsto' ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (thermalBoundedMomentTruncation n)).continuousAt.tendsto.comp hweak)
    intro i
    exact (integral_mono (thermalBoundedMomentTruncation_integrable n (μs i)) (hμs i)
      (fun x => min_le_right _ _)).trans (hMs i)
  have hn (n : ℕ) (x : ℂ) : 0 ≤ thermalBoundedMomentTruncation n x :=
    le_min (Nat.cast_nonneg n) (sq_nonneg _)
  have hM0 : 0 ≤ M := (integral_nonneg (hn 0)).trans (hb 0)
  have hpoint (x : ℂ) : ENNReal.ofReal (‖x‖ ^ 2) =
      ⨆ n : ℕ, ENNReal.ofReal (thermalBoundedMomentTruncation n x) := by
    apply le_antisymm
    · obtain ⟨n, hnx⟩ := exists_nat_ge (‖x‖ ^ 2)
      have he : thermalBoundedMomentTruncation n x = ‖x‖ ^ 2 := min_eq_right hnx
      rw [← he]
      exact le_iSup (fun m : ℕ => ENNReal.ofReal (thermalBoundedMomentTruncation m x)) n
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hmono : Monotone (fun n : ℕ => fun x : ℂ => ENNReal.ofReal (thermalBoundedMomentTruncation n x)) := by
    intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min (by exact_mod_cast hnm) le_rfl)
  have hlin : (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≤ ENNReal.ofReal M := by
    calc
      _ = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (thermalBoundedMomentTruncation n x) ∂μ := lintegral_congr hpoint
      _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (thermalBoundedMomentTruncation n x) ∂μ :=
        lintegral_iSup (fun n => (thermalBoundedMomentTruncation n).continuous.measurable.ennreal_ofReal) hmono
      _ ≤ _ := by
        apply iSup_le
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (thermalBoundedMomentTruncation_integrable n μ)
          (Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hb n)
  have hi : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (continuous_norm.pow 2).measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => sq_nonneg ‖x‖)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hM0).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg ‖x‖)]
  exact hlin

/-- The direct-method continuity endpoint: the limit moment is derived from weak
convergence and the sequence's genuine uniform second moments. -/
theorem thermal_negative_log_integral_tendsto_of_uniform_secondMoment
    {ι : Type*} {l : Filter ι} [NeBot l]
    {μs : ι → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M : ℝ}
    (hweak : Tendsto μs l (𝓝 μ))
    (hμs : ∀ i, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs i))
    (hMs : ∀ i, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs i)) ≤ M) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
    (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M ∧
    Integrable thermalNegativeLogKernel ((μ : Measure ℂ).prod μ) ∧
    Tendsto (fun i => ∫ p, thermalNegativeLogKernel p
        ∂(((μs i) : Measure ℂ).prod (μs i))) l
      (𝓝 (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ))) := by
  obtain ⟨hμ, hM⟩ := thermal_secondMoment_of_weak_convergence hweak hμs hMs
  exact ⟨hμ, hM, thermalNegativeLogKernel_integrable μ hμ,
    thermal_negative_log_integral_tendsto hweak hμs hMs hμ hM⟩

/-- The same conclusion with the physical negative sign inside the integral. -/
theorem thermal_signed_negative_log_integral_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {μs : ι → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M : ℝ}
    (hweak : Tendsto μs l (𝓝 μ))
    (hμs : ∀ i, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs i))
    (hMs : ∀ i, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs i)) ≤ M) :
    Tendsto (fun i => ∫ p, -thermalNegativeLogKernel p
        ∂(((μs i) : Measure ℂ).prod (μs i))) l
      (𝓝 (∫ p, -thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ))) := by
  simpa only [integral_neg] using
    (thermal_negative_log_integral_tendsto_of_uniform_secondMoment hweak hμs hMs).2.2.2.neg

end RepulsiveCoulomb.PaperRoute
