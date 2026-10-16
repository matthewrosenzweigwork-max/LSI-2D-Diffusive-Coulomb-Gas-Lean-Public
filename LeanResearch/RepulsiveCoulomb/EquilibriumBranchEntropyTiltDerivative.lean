import LeanResearch.PeriodicAttractiveLogGas.Rothaus

/-! Actual differentiation of the bounded multiplicative-tilt entropy at zero.
A uniform positive factor and a constant integrable derivative majorant are
proved before invoking the pinned differentiation-under-integral theorem. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem equilibrium_tilt_factor_bounds {M t u : ℝ} (hM : 0 ≤ M) (hu : |u| ≤ M)
    (ht : t ∈ Ioo (-(1 / (2 * (M + 1)))) (1 / (2 * (M + 1)))) :
    1 + t * u ∈ Icc (1 / 2) (3 / 2) := by
  have hd : 0 < 2 * (M + 1) := by positivity
  have ht' : |t| < 1 / (2 * (M + 1)) := abs_lt.mpr ht
  have htm := (lt_div_iff₀ hd).mp ht'
  have hm := mul_le_mul_of_nonneg_left hu (abs_nonneg t)
  have hb : |t * u| ≤ 1 / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg t]
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  constructor <;> linarith

theorem equilibrium_log_near_one_bound {u : ℝ} (hu : u ∈ Icc (1 / 2) (3 / 2)) :
    |Real.log u| ≤ 1 := by
  have hu0 : 0 < u := by linarith [hu.1]
  have huinv : 0 < u⁻¹ := inv_pos.mpr hu0
  have hmul : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0.ne'
  have hprod := mul_nonneg (sub_nonneg.mpr hu.1) huinv.le
  have hupper := Real.log_le_sub_one_of_pos hu0
  have hlower := Real.log_le_sub_one_of_pos huinv
  rw [Real.log_inv] at hlower
  apply abs_le.mpr
  constructor <;> nlinarith [hu.2]

/-- The entropy of the genuine positive bounded multiplicative factor has
actual derivative integral phi at zero under any finite reference measure. -/
theorem equilibrium_hasDerivAt_tilt_entropy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {φ : α → ℝ} (hφm : Measurable φ)
    {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ x, (1 + t * φ x) * Real.log (1 + t * φ x) ∂μ)
      (∫ x, φ x ∂μ) 0 := by
  let δ : ℝ := 1 / (2 * (M + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let F : ℝ → α → ℝ := fun t x => (1 + t * φ x) * Real.log (1 + t * φ x)
  let D : ℝ → α → ℝ := fun t x => φ x * (Real.log (1 + t * φ x) + 1)
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) μ := by
    dsimp only [F]
    fun_prop
  have hF0 : Integrable (F 0) μ := by
    simpa only [F, zero_mul, add_zero, Real.log_one, mul_zero] using (integrable_const (μ := μ) (0 : ℝ))
  have hD0 : AEStronglyMeasurable (D 0) μ := by
    simpa only [D, zero_mul, add_zero, Real.log_one, zero_add, mul_one] using hφm.aestronglyMeasurable
  have hbound (x : α) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : ‖D t x‖ ≤ 2 * M := by
    have hb := equilibrium_tilt_factor_bounds hM (hφM x) ht
    have hl := equilibrium_log_near_one_bound hb
    have ha : |Real.log (1 + t * φ x) + 1| ≤ 2 := by
      have h := abs_add_le (Real.log (1 + t * φ x)) 1
      norm_num only [abs_one] at h
      linarith
    dsimp only [D]
    rw [Real.norm_eq_abs, abs_mul]
    have h := mul_le_mul (hφM x) ha (abs_nonneg _) hM
    simpa only [mul_comm] using h
  have hderiv (x : α) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : HasDerivAt (fun s => F s x) (D t x) t := by
    have hb := equilibrium_tilt_factor_bounds hM (hφM x) ht
    have hu0 : 0 < 1 + t * φ x := by linarith [hb.1]
    have hu : HasDerivAt (fun s : ℝ => 1 + s * φ x) (φ x) t :=
      (hasDerivAt_mul_const (x := t) (φ x)).const_add 1
    have hc := (Real.hasDerivAt_mul_log hu0.ne').comp t hu
    change HasDerivAt (fun s : ℝ => (1 + s * φ x) * Real.log (1 + s * φ x))
      ((Real.log (1 + t * φ x) + 1) * φ x) t at hc
    exact hc.congr_deriv (mul_comm _ _)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := D) (bound := fun _ => 2 * M) (s := Ioo (-δ) δ)
    (Ioo_mem_nhds (neg_neg_of_pos hδ) hδ) (Eventually.of_forall hFm) hF0 hD0
    (Eventually.of_forall (fun x t ht => hbound x t ht)) (integrable_const _)
    (Eventually.of_forall (fun x t ht => hderiv x t ht))).2
  simpa only [F, D, zero_mul, add_zero, Real.log_one, zero_add, mul_one] using hd

theorem equilibrium_hasDerivAt_zeroMass_tilt_entropy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {φ : α → ℝ} (hφm : Measurable φ)
    {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) (hφ0 : (∫ x, φ x ∂μ) = 0) :
    HasDerivAt (fun t : ℝ => ∫ x, (1 + t * φ x) * Real.log (1 + t * φ x) ∂μ) 0 0 := by
  simpa only [hφ0] using equilibrium_hasDerivAt_tilt_entropy μ hφm hM hφM

end RepulsiveCoulomb
