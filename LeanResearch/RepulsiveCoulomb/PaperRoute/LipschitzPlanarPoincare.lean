module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.PlanarDSPoincare
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# Measurable-gradient DS consumer and the full local Lipschitz test class

The same Cauchy--Schwarz normalization applies to measurable bounded actual
derivatives. Real Lipschitz extension transfers the estimate to closed double
balls with exact equality of means, oscillations, and open-double-ball
Fréchet derivatives. No smooth approximation is used.
-/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb.PaperRoute.PlanarDS

/-- Planar DS for every globally Lipschitz scalar, with the actual derivative. -/
def PlanarDSLipschitz (w : ℂ → ℝ) (L : ℝ) : Prop :=
  ∀ f : ℂ → ℝ, ∀ Lf : ℝ≥0, LipschitzWith Lf f → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    doubleOscillation (weightMeasure w) f c r ≤
      L / Real.sqrt ((weightMeasure w).real (ball c r)) *
        ∫ z in ball c (2 * r), ‖fderiv ℝ f z‖ * Real.sqrt (w z)

/-- Weak Poincaré for the global Lipschitz test class. -/
def WeakOneTwoLipschitz (μ : Measure ℂ) (P Λ : ℝ) : Prop :=
  ∀ f : ℂ → ℝ, ∀ Lf : ℝ≥0, LipschitzWith Lf f → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ) ≤
      P * r * Real.sqrt (⨍ z in ball c (Λ * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ)

/-- Weak Poincaré for every globally locally-Lipschitz scalar. -/
def WeakOneTwoLocallyLipschitz (μ : Measure ℂ) (P Λ : ℝ) : Prop :=
  ∀ f : ℂ → ℝ, LocallyLipschitz f → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ) ≤
      P * r * Real.sqrt (⨍ z in ball c (Λ * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ)

/-- The actual derivative is measurable and bounded even at points where the
scalar is not differentiable. Its square is integrable on each finite ball. -/
theorem integrableOn_sq_norm_fderiv_ball_of_lipschitz {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {f : ℂ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzWith Lf f) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball c r) μ := by
  have : IsFiniteMeasure (μ.restrict (ball c r)) := ⟨by simpa using (hμ c r hr).2⟩
  apply (integrable_const ((Lf : ℝ) ^ 2)).mono' ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    change ‖‖fderiv ℝ f z‖ ^ 2‖ ≤ (Lf : ℝ) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2)

/-- Genuine Cauchy--Schwarz for measurable nonnegative data of finite energy. -/
theorem mixedIntegral_le_sqrt_area_energy_measurable {w g : ℂ → ℝ}
    (hw : Measurable w) (hwn : ∀ᵐ z ∂volume, 0 ≤ w z)
    (hg : Measurable g)
    (hgn : ∀ z, 0 ≤ g z) (c : ℂ) (r : ℝ)
    (henergy : IntegrableOn (fun z => g z ^ 2) (ball c r) (weightMeasure w)) :
    (∫ z in ball c r, g z * Real.sqrt (w z)) ≤
      Real.sqrt (volume.real (ball c r)) *
        Real.sqrt (∫ z in ball c r, g z ^ 2 ∂weightMeasure w) := by
  let ν := volume.restrict (ball c r)
  have : IsFiniteMeasure ν := ⟨by simp [ν]; finiteness⟩
  have hweighted : Integrable (fun z => w z * g z ^ 2) ν := by
    have h := (integrable_withDensity_iff_integrable_smul₀'
      (hw.ennreal_ofReal.aemeasurable.restrict)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).1
      (show Integrable (fun z => g z ^ 2)
        (ν.withDensity (fun z => ENNReal.ofReal (w z))) from by
          simpa [ν, weightMeasure, IntegrableOn, restrict_withDensity measurableSet_ball] using henergy)
    apply h.congr
    filter_upwards [ae_restrict_of_ae hwn] with z hz
    simp [ENNReal.toReal_ofReal hz]
  have hsq : Integrable (fun z => (g z * Real.sqrt (w z)) ^ 2) ν := by
    apply hweighted.congr
    filter_upwards [ae_restrict_of_ae hwn] with z hz
    rw [mul_pow, Real.sq_sqrt hz, mul_comm]
  have hm : MemLp (fun z => g z * Real.sqrt (w z)) 2 ν :=
    (memLp_two_iff_integrable_sq
      ((hg.mul hw.sqrt).aestronglyMeasurable)).2 hsq
  have hone : MemLp (fun _ : ℂ => (1 : ℝ)) 2 ν := memLp_const 1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun _ : ℂ => (by norm_num : (0 : ℝ) ≤ 1)))
    (Filter.Eventually.of_forall (fun z => mul_nonneg (hgn z) (Real.sqrt_nonneg _)))
    (by simpa using hone) (by simpa using hm)
  have hsqeq : (∫ z, (g z * Real.sqrt (w z)) ^ 2 ∂ν) =
      ∫ z in ball c r, g z ^ 2 ∂weightMeasure w := by
    rw [integral_weightMeasure hw hwn measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hwn] with z hz
    rw [mul_pow, Real.sq_sqrt hz, mul_comm]
  simpa only [one_mul, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    ← Real.sqrt_eq_rpow, hsqeq, ν, measureReal_restrict_apply_univ] using hcs

/-- Exact normalization for the full globally Lipschitz test class. -/
theorem weakOneTwoLipschitz_of_planarDS {D L : ℝ} {w : ℂ → ℝ}
    (hw : Measurable w) (hwn : ∀ᵐ z ∂volume, 0 ≤ w z)
    (hμ : PositiveFiniteBalls (weightMeasure w))
    (hD : GlobalDoublingWith (weightMeasure w) D) (hL : 0 < L)
    (hDS : PlanarDSLipschitz w L) :
    WeakOneTwoLipschitz (weightMeasure w) (2 * L * Real.sqrt (Real.pi * D)) 2 := by
  intro f Lf hf c r hr
  let μ := weightMeasure w
  let M := μ.real (ball c r)
  let N := μ.real (ball c (2 * r))
  let E := ∫ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ
  have hM : 0 < M := ballMass_pos hμ c hr
  have hN : 0 < N := ballMass_pos hμ c (by positivity)
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hDn : 0 ≤ D := le_trans zero_le_one hD.1
  have hmass : N ≤ D * M := doubling_real hμ hD c hr
  have havg : (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) = E / N := by
    rw [setAverage_eq]; simp only [smul_eq_mul]; exact (div_eq_inv_mul _ _).symm
  have hcs := mixedIntegral_le_sqrt_area_energy_measurable hw hwn
    (measurable_fderiv ℝ f).norm (fun _ => norm_nonneg _) c (2 * r)
    (integrableOn_sq_norm_fderiv_ball_of_lipschitz hμ hf c (by positivity))
  rw [sqrt_volume_ball c (by positivity)] at hcs
  have hnorm := Real.sqrt_le_sqrt (normalize_energy hE hM hN hmass)
  calc
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ)
        ≤ doubleOscillation μ f c r := meanOscillation_le_doubleOscillation hμ hf.continuous c hr
    _ ≤ L / Real.sqrt M * ∫ z in ball c (2 * r), ‖fderiv ℝ f z‖ * Real.sqrt (w z) :=
      hDS f Lf hf c r hr
    _ ≤ L / Real.sqrt M * ((2 * r * Real.sqrt Real.pi) * Real.sqrt E) :=
      mul_le_mul_of_nonneg_left hcs (div_nonneg hL.le (Real.sqrt_nonneg _))
    _ = (2 * L * Real.sqrt Real.pi * r) * Real.sqrt (E / M) := by
      rw [Real.sqrt_div hE]; ring
    _ ≤ (2 * L * Real.sqrt Real.pi * r) * Real.sqrt (D * (E / N)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (2 * L * Real.sqrt (Real.pi * D)) * r *
        Real.sqrt (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) := by
      rw [havg, Real.sqrt_mul hDn, Real.sqrt_mul Real.pi_pos.le]
      ring

/-- A scalar Lipschitz only on the closed double ball satisfies the same
weak inequality. Agreement of extension germs identifies actual derivatives. -/
theorem weakOneTwo_of_lipschitzOn_closedDoubleBall {μ : Measure ℂ} {P : ℝ}
    (hPI : WeakOneTwoLipschitz μ P 2) {f : ℂ → ℝ} {Lf : ℝ≥0}
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hf : LipschitzOnWith Lf f (closedBall c (2 * r))) :
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ) ≤
      P * r * Real.sqrt (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) := by
  obtain ⟨G, hG, hEq⟩ := hf.extend_real
  have hsub : ball c r ⊆ closedBall c (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hderiv (z : ℂ) (hz : z ∈ ball c (2 * r)) : fderiv ℝ f z = fderiv ℝ G z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact hEq (ball_subset_closedBall hy)
  have hmean : (⨍ z in ball c r, f z ∂μ) = ⨍ z in ball c r, G z ∂μ := by
    simp only [setAverage_eq]
    congr 1
    exact setIntegral_congr_fun measurableSet_ball (hEq.mono hsub)
  have hleft : (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ) =
      ⨍ x in ball c r, |G x - (⨍ z in ball c r, G z ∂μ)| ∂μ := by
    rw [hmean]
    simp only [setAverage_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hEq (hsub hx)]
  have hright : (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) =
      ⨍ z in ball c (2 * r), ‖fderiv ℝ G z‖ ^ 2 ∂μ := by
    simp only [setAverage_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [hderiv z hz]
  rw [hleft, hright]
  exact hPI G Lf hG c r hr

/-- The local test interface has genuinely finite mean, oscillation and
energy integrals, even when the scalar is arbitrary outside closed 2B. -/
theorem integrableOn_data_of_lipschitzOn_closedDoubleBall {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {f : ℂ → ℝ} {Lf : ℝ≥0}
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hf : LipschitzOnWith Lf f (closedBall c (2 * r))) :
    IntegrableOn f (ball c r) μ ∧
    IntegrableOn (fun x => |f x - (⨍ z in ball c r, f z ∂μ)|) (ball c r) μ ∧
    IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball c (2 * r)) μ := by
  obtain ⟨G, hG, hEq⟩ := hf.extend_real
  have hsub : ball c r ⊆ closedBall c (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have : IsFiniteMeasure (μ.restrict (ball c r)) := ⟨by simpa using (hμ c r hr).2⟩
  have hfi : IntegrableOn f (ball c r) μ :=
    (continuous_integrableOn_ball hμ hG.continuous c hr).congr_fun
      (hEq.symm.mono hsub) measurableSet_ball
  refine ⟨hfi, (hfi.sub (integrable_const _)).abs, ?_⟩
  apply (integrableOn_sq_norm_fderiv_ball_of_lipschitz hμ hG c (by positivity)).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hlocal : G =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact (hEq (ball_subset_closedBall hy)).symm
  rw [hlocal.fderiv_eq]

/-- Compact local Lipschitzness gives the closed-double-ball test hypothesis;
its auxiliary bound disappears from the exact quantitative conclusion. -/
theorem weakOneTwoLocallyLipschitz_of_lipschitz {μ : Measure ℂ} {P : ℝ}
    (hPI : WeakOneTwoLipschitz μ P 2) : WeakOneTwoLocallyLipschitz μ P 2 := by
  intro f hf c r hr
  obtain ⟨Lf, hLf⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall c (2 * r)) hf.locallyLipschitzOn
  exact weakOneTwo_of_lipschitzOn_closedDoubleBall hPI c hr hLf

end RepulsiveCoulomb.PaperRoute.PlanarDS
