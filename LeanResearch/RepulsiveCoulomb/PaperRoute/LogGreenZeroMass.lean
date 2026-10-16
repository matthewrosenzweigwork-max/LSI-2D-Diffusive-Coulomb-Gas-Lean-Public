module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.LogGreenCutoff
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LogPotentialDecay
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-! Expanding-cutoff Green identity for the literal logarithmic potential of a
compact zero-mass source. Boundary errors are quantitatively estimated. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set Metric
open scoped Topology ContDiff Convolution
namespace RepulsiveCoulomb.PaperRoute

def logGreenUnitBump : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩

def logGreenBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℂ) :=
  ⟨R, 2 * R, hR, by linarith⟩

theorem logGreenBump_eq_scaled (R : ℝ) (hR : 0 < R) (z : ℂ) :
    logGreenBump R hR z = logGreenUnitBump (R⁻¹ • z) := by
  simp only [ContDiffBump.apply, logGreenBump, logGreenUnitBump,
    mul_div_cancel_right₀ 2 hR.ne', div_one, inv_one, sub_zero, one_smul]

theorem logGreenBump_fderiv_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    fderiv ℝ (logGreenBump R hR : ℂ → ℝ) z = 0 := by
  have he := (logGreenBump R hR).eventuallyEq_one_of_mem_ball
    (show z ∈ ball (0 : ℂ) R by simpa only [mem_ball, dist_zero_right] using hz)
  rw [he.fderiv_eq]
  simp

theorem exists_logGreenBump_fderiv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (R : ℝ) (hR : 0 < R) (z : ℂ),
      ‖fderiv ℝ (logGreenBump R hR : ℂ → ℝ) z‖ ≤ C / R := by
  have hc : Continuous (fderiv ℝ (logGreenUnitBump : ℂ → ℝ)) :=
    (logGreenUnitBump.contDiff (n := ⊤)).continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (logGreenUnitBump.hasCompactSupport.fderiv ℝ)
  let C := |B| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hb (z : ℂ) : ‖fderiv ℝ (logGreenUnitBump : ℂ → ℝ) z‖ ≤ C :=
    (hB z).trans (by dsimp [C]; linarith [le_abs_self B])
  refine ⟨C, hC, ?_⟩
  intro R hR z
  have ht : HasFDerivAt (fun x : ℂ => R⁻¹ • x) (R⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_smul R⁻¹
  have hh := ((logGreenUnitBump.contDiff (n := ⊤)).differentiable (by simp) (R⁻¹ • z)).hasFDerivAt.comp z ht
  have he : (logGreenBump R hR : ℂ → ℝ) = (fun x => logGreenUnitBump (R⁻¹ • x)) :=
    funext (logGreenBump_eq_scaled R hR)
  rw [he]
  have hder := hh.fderiv
  change fderiv ℝ (fun x => logGreenUnitBump (R⁻¹ • x)) z = _ at hder
  rw [hder]
  calc
    _ ≤ ‖fderiv ℝ (logGreenUnitBump : ℂ → ℝ) (R⁻¹ • z)‖ *
        ‖R⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ‖R⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
    _ = C / R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ContinuousLinearMap.norm_id]
      simp [div_eq_mul_inv]

def logGreenBoundary (η : ℂ → ℝ) (R : ℝ) (hR : 0 < R) : ℝ :=
  2 * ∫ x, logGreenBump R hR x * smoothLogPotential η x *
    (fderiv ℝ (logGreenBump R hR : ℂ → ℝ) x 1 * fderiv ℝ (smoothLogPotential η) x 1 +
      fderiv ℝ (logGreenBump R hR : ℂ → ℝ) x Complex.I * fderiv ℝ (smoothLogPotential η) x Complex.I)

/-- The boundary correction has an explicit O(R^-2) bound, derived from actual
zero-mass exterior decay and the scaled bump derivative bound. -/
theorem logGreenBoundary_bound {η : ℂ → ℝ} {R₀ R C : ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0)
    (hsupp : ∀ y ∈ tsupport η, ‖y‖ ≤ R₀) (hR : 0 < R) (hlarge : 2 * R₀ ≤ R)
    (hC : 0 ≤ C)
    (hχD : ∀ x, ‖fderiv ℝ (logGreenBump R hR : ℂ → ℝ) x‖ ≤ C / R) :
    |logGreenBoundary η R hR| ≤ 32 * Real.pi * C * smoothLogFirstMoment η ^ 2 / R ^ 2 := by
  let χ : ℂ → ℝ := logGreenBump R hR
  let h : ℂ → ℝ := smoothLogPotential η
  let M := smoothLogFirstMoment η
  let F : ℂ → ℝ := fun x => χ x * h x *
    (fderiv ℝ χ x 1 * fderiv ℝ h x 1 + fderiv ℝ χ x Complex.I * fderiv ℝ h x Complex.I)
  let K : ℝ := 4 * C * M ^ 2 / R ^ 4
  have hM : 0 ≤ M := smoothLogFirstMoment_nonneg η
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hi : Integrable ((closedBall (0 : ℂ) (2 * R)).indicator (fun _ : ℂ => K)) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (integrableOn_const (isCompact_closedBall (0 : ℂ) (2 * R)).measure_lt_top.ne)
  have hb (x : ℂ) : ‖F x‖ ≤ (closedBall (0 : ℂ) (2 * R)).indicator (fun _ => K) x := by
    by_cases hout : x ∈ closedBall (0 : ℂ) (2 * R)
    · rw [indicator_of_mem hout]
      by_cases hin : ‖x‖ < R
      · have hdz := logGreenBump_fderiv_zero hR hin
        simp only [F, χ, hdz, zero_apply, zero_mul, add_zero, mul_zero, norm_zero]
        exact hK
      · have hrx : R ≤ ‖x‖ := le_of_not_gt hin
        have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hrx)
        have hlargex := hlarge.trans hrx
        have hh0 := smoothLogPotential_zero_mass_bound hη.continuous hηc hmass hsupp hx hlargex
        have hd0 := smoothLogPotential_fderiv_zero_mass_bound (hη.of_le (by norm_num)) hηc hmass hsupp hx hlargex
        have hhb : |h x| ≤ 2 / R * M := hh0.trans
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hR hrx) hM)
        have hdb : ‖fderiv ℝ h x‖ ≤ 2 / R ^ 2 * M := hd0.trans
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hR)
            (pow_le_pow_left₀ hR.le hrx 2)) hM)
        have hχ : |χ x| ≤ 1 := by
          rw [abs_of_nonneg (logGreenBump R hR).nonneg]
          exact (logGreenBump R hR).le_one
        have hdot := planarFunctional_dot_bound (fderiv ℝ χ x) (fderiv ℝ h x)
        calc
          ‖F x‖ = |χ x| * |h x| * |fderiv ℝ χ x 1 * fderiv ℝ h x 1 +
              fderiv ℝ χ x Complex.I * fderiv ℝ h x Complex.I| := by
            simp only [F, Real.norm_eq_abs, abs_mul]
          _ ≤ (1 * (2 / R * M)) * ((C / R) * (2 / R ^ 2 * M)) := by
            gcongr
            exact hdot.trans (mul_le_mul (hχD x) hdb (norm_nonneg _) (by positivity))
          _ = K := by dsimp [K]; ring
    · have hχzero : χ x = 0 := (logGreenBump R hR).zero_of_le_dist (by
        have hn : 2 * R < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hout
        simpa only [logGreenBump, dist_zero_right] using hn.le)
      simp only [F, hχzero, zero_mul, norm_zero, indicator_of_notMem hout, le_refl]
  have hv : volume.real (closedBall (0 : ℂ) (2 * R)) = 4 * Real.pi * R ^ 2 := by
    simp [Measure.real, hR.le]
    ring
  have hiBound := norm_integral_le_of_norm_le hi (Eventually.of_forall hb)
  rw [integral_indicator_const _ isClosed_closedBall.measurableSet, hv, smul_eq_mul] at hiBound
  change |2 * ∫ x, F x| ≤ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ((4 * Real.pi * R ^ 2) * K) := mul_le_mul_of_nonneg_left hiBound (by norm_num)
    _ = _ := by dsimp [K, M]; field_simp; ring

def logGreenRadius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem logGreenRadius_pos (n : ℕ) : 0 < logGreenRadius n := by
  unfold logGreenRadius
  positivity

theorem logGreenRadius_tendsto : Tendsto logGreenRadius atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

theorem logGreenBump_tendsto (x : ℂ) :
    Tendsto (fun n => logGreenBump (logGreenRadius n) (logGreenRadius_pos n) x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [logGreenRadius_tendsto.eventually (eventually_ge_atTop ‖x‖)] with n hn
  symm
  exact (logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).one_of_mem_closedBall
    (show x ∈ closedBall (0 : ℂ) (logGreenRadius n) by simpa only [mem_closedBall, dist_zero_right] using hn)

/-- Quantitative boundary cancellation for the actual expanding cutoffs. -/
theorem logGreenBoundary_tendsto_zero {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) :
    Tendsto (fun n => logGreenBoundary η (logGreenRadius n) (logGreenRadius_pos n)) atTop (𝓝 0) := by
  obtain ⟨R₀, hR₀, hsupp⟩ := hηc.isBounded.exists_pos_norm_lt
  obtain ⟨C, hC, hCD⟩ := exists_logGreenBump_fderiv_bound
  have hbound : ∀ᶠ n in atTop,
      ‖logGreenBoundary η (logGreenRadius n) (logGreenRadius_pos n)‖ ≤
        32 * Real.pi * C * smoothLogFirstMoment η ^ 2 * logRegularizationScale n ^ 2 := by
    filter_upwards [logGreenRadius_tendsto.eventually (eventually_ge_atTop (2 * R₀))] with n hn
    have hb := logGreenBoundary_bound hη hηc hmass (fun y hy => (hsupp y hy).le)
      (logGreenRadius_pos n) hn hC.le (hCD _ _)
    simpa only [Real.norm_eq_abs, logGreenRadius, logRegularizationScale, div_eq_mul_inv,
      inv_pow] using hb
  have hlim : Tendsto (fun n => 32 * Real.pi * C * smoothLogFirstMoment η ^ 2 *
      logRegularizationScale n ^ 2) atTop (𝓝 0) := by
    simpa using (logRegularizationScale_tendsto.pow 2).const_mul
      (32 * Real.pi * C * smoothLogFirstMoment η ^ 2)
  exact squeeze_zero_norm' hbound hlim

theorem logGreen_cutoff_energy_tendsto {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) :
    Tendsto (fun n => ∫ x, logGreenBump (logGreenRadius n) (logGreenRadius_pos n) x ^ 2 *
        ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2)) := by
  have hc : Continuous (fun x => ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) :=
    ((smoothLogPotential_contDiff (n := 2) hη hηc).continuous_fderiv (by norm_num)).norm.pow 2
  apply tendsto_integral_of_dominated_convergence (fun x => ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2)
  · intro n
    exact (((logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).continuous.pow 2).mul hc).aestronglyMeasurable
  · exact smoothLogPotential_energy_integrable hη hηc hmass
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hn := (logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).nonneg (x := x)
    have h1 := (logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).le_one (x := x)
    have hs : logGreenBump (logGreenRadius n) (logGreenRadius_pos n) x ^ 2 ≤ 1 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg ‖fderiv ℝ (smoothLogPotential η) x‖)
  · filter_upwards [] with x
    simpa only [one_pow, one_mul] using (logGreenBump_tendsto x).pow 2 |>.mul_const
      (‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2)

/-- The actual unbounded Green energy identity after the proved boundary limit. -/
theorem smoothLogPotential_green_identity {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) :
    (∫ x, ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) =
      (2 * Real.pi) * ∫ x, smoothLogPotential η x * η x := by
  obtain ⟨R₀, hR₀, hsupp⟩ := hηc.isBounded.exists_pos_norm_lt
  have heq : ∀ᶠ n in atTop,
      (∫ x, logGreenBump (logGreenRadius n) (logGreenRadius_pos n) x ^ 2 *
        ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) =
      (2 * Real.pi) * (∫ x, smoothLogPotential η x * η x) -
        logGreenBoundary η (logGreenRadius n) (logGreenRadius_pos n) := by
    filter_upwards [logGreenRadius_tendsto.eventually (eventually_ge_atTop R₀)] with n hn
    rw [smoothLogPotential_green_cutoff hη hηc
      ((logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).contDiff (n := 2))
      (logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).hasCompactSupport]
    change (2 * Real.pi) * _ - logGreenBoundary η _ _ = _
    congr 2
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : η x = 0
    · simp [hx]
    · have hxR := (hsupp x (subset_tsupport η hx)).le.trans hn
      have hone := (logGreenBump (logGreenRadius n) (logGreenRadius_pos n)).one_of_mem_closedBall
        (show x ∈ closedBall (0 : ℂ) (logGreenRadius n) by simpa only [mem_closedBall, dist_zero_right] using hxR)
      rw [hone, one_pow, one_mul]
  have hlim : Tendsto (fun n => (2 * Real.pi) * (∫ x, smoothLogPotential η x * η x) -
      logGreenBoundary η (logGreenRadius n) (logGreenRadius_pos n)) atTop
      (𝓝 ((2 * Real.pi) * (∫ x, smoothLogPotential η x * η x))) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (logGreenBoundary_tendsto_zero hη hηc hmass)
  exact tendsto_nhds_unique (logGreen_cutoff_energy_tendsto hη hηc hmass) (hlim.congr' (heq.mono (fun _ hn => hn.symm)))

/-- Genuine product integrability for two compact continuous signed densities.
The local logarithmic singularity is handled before Fubini is invoked. -/
theorem compactLogInteraction_integrable {η θ : ℂ → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    Integrable (fun p : ℂ × ℂ => planarLogKernel (p.1 - p.2) * η p.1 * θ p.2)
      (volume.prod volume) := by
  have hg : Measurable planarLogKernel := by
    unfold planarLogKernel
    fun_prop
  have hm : AEStronglyMeasurable
      (fun p : ℂ × ℂ => planarLogKernel (p.1 - p.2) * η p.1 * θ p.2)
      (volume.prod volume) :=
    ((hg.comp (measurable_fst.sub measurable_snd)).mul (hη.measurable.comp measurable_fst)
      |>.mul (hθ.measurable.comp measurable_snd)).aestronglyMeasurable
  have hgn : LocallyIntegrable (fun z => ‖planarLogKernel z‖) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact (planarLogKernel_locallyIntegrable.integrableOn_isCompact hK).norm
  let P : ℂ → ℝ := (fun z => ‖planarLogKernel z‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun z => ‖θ z‖)
  have hP : Continuous P := hθc.norm.continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hgn hθ.norm
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [] with x
    have hi := (smoothLogPotential_integrable_swap hθ hθc x).const_mul (η x)
    convert! hi using 1
    ext y
    ring
  · have hi : Integrable (fun x => ‖η x‖ * P x) :=
      (hη.norm.mul hP).integrable_of_hasCompactSupport hηc.norm.mul_right
    have he : (fun x => ∫ y, ‖planarLogKernel (x - y) * η x * θ y‖) =
        (fun x => ‖η x‖ * P x) := by
      funext x
      dsimp only [P]
      rw [convolution_eq_swap, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [norm_mul, ContinuousLinearMap.mul_apply']
      ring
    rw [he]
    exact hi

/-- Fubini identifies the actual product interaction with the literal potential pairing. -/
theorem compactLogInteraction_eq_potential {η θ : ℂ → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    (∫ p : ℂ × ℂ, planarLogKernel (p.1 - p.2) * η p.1 * θ p.2 ∂(volume.prod volume)) =
      ∫ x, smoothLogPotential θ x * η x := by
  rw [integral_prod _ (compactLogInteraction_integrable hη hηc hθ hθc)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smoothLogPotential_eq_swap, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- The signed logarithmic Green identity, with actual product and energy
integrability and the exact physical 1/(2π) normalization. -/
theorem log_green_zero_mass {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) :
    Integrable (fun p : ℂ × ℂ => (-Real.log ‖p.1 - p.2‖) * η p.1 * η p.2)
      (volume.prod volume) ∧
    Integrable (fun x => ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) ∧
    (∫ p : ℂ × ℂ, (-Real.log ‖p.1 - p.2‖) * η p.1 * η p.2 ∂(volume.prod volume)) =
      (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2 := by
  refine ⟨compactLogInteraction_integrable hη.continuous hηc hη.continuous hηc,
    smoothLogPotential_energy_integrable hη hηc hmass, ?_⟩
  change (∫ p : ℂ × ℂ, planarLogKernel (p.1 - p.2) * η p.1 * η p.2 ∂(volume.prod volume)) = _
  rw [compactLogInteraction_eq_potential hη.continuous hηc hη.continuous hηc,
    smoothLogPotential_green_identity hη hηc hmass]
  field_simp

/-- Nonnegativity is a consequence of the proved Green identity, not an input. -/
theorem log_interaction_zero_mass_nonneg {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) :
    0 ≤ ∫ p : ℂ × ℂ, (-Real.log ‖p.1 - p.2‖) * η p.1 * η p.2 ∂(volume.prod volume) := by
  rw [(log_green_zero_mass hη hηc hmass).2.2]
  exact mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))

end RepulsiveCoulomb.PaperRoute
