import LeanResearch.RepulsiveCoulomb.PaperRoute.MetricDoublingComparison
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Conditional planar David–Semmes to weak (1,2) Poincaré transfer

This module proves only a conditional analytic bridge. `PlanarDSC1` is an
explicit premise, not a proved consequence of metric doubling or quasiconformal
geometry. In particular, nothing here proves Bonk–Lang, Semmes, or the complete
Björn Corollary 8, and the missing DS producer must not be assumed in a final
unconditional paper-route endpoint.

All oscillations and energies are actual measure integrals. The differential is
`fderiv ℝ f`, whose operator norm for a real-valued function on the Euclidean
plane is the norm of its physical real gradient. No independent gradient field
or arbitrary numerical energy is substituted. The test class is global C1,
not the full locally Lipschitz class of standard weighted admissibility.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RepulsiveCoulomb.PaperRoute.PlanarDS

/-- The differential energy used below is literally physical-gradient energy.
This is the isometric Riesz identification on the real Euclidean plane. -/
theorem norm_gradient_eq_norm_fderiv (f : ℂ → ℝ) (z : ℂ) :
    ‖gradient f z‖ = ‖fderiv ℝ f z‖ :=
  (InnerProductSpace.toDual ℝ ℂ).symm.norm_map _

/-- The normalized double oscillation for the same weighted measure in both variables. -/
def doubleOscillation (μ : Measure ℂ) (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ⨍ x in ball c r, ⨍ y in ball c r, |f x - f y| ∂μ ∂μ

/-- The genuine planar DS input: oscillation weight `w`, gradient weight `sqrt w`.
This is a conditional hypothesis awaiting a geometric producer. -/
def PlanarDSC1 (w : ℂ → ℝ) (L : ℝ) : Prop :=
  ∀ f : ℂ → ℝ, ContDiff ℝ 1 f → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    doubleOscillation (weightMeasure w) f c r ≤
      L / Real.sqrt ((weightMeasure w).real (ball c r)) *
        ∫ z in ball c (2 * r), ‖fderiv ℝ f z‖ * Real.sqrt (w z)

/-- Weak (1,2) Poincaré with an explicit dilation and real differential energy. -/
def WeakOneTwoC1 (μ : Measure ℂ) (P Λ : ℝ) : Prop :=
  ∀ f : ℂ → ℝ, ContDiff ℝ 1 f → ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ) ≤
      P * r * Real.sqrt (⨍ z in ball c (Λ * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ)

/-- Every denominator used below is a strictly positive finite real ball mass. -/
theorem ballMass_pos {μ : Measure ℂ} (hμ : PositiveFiniteBalls μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) : 0 < μ.real (ball c r) :=
  ENNReal.toReal_pos (hμ c r hr).1.ne' (hμ c r hr).2.ne

/-- Compactness and finite ball mass give integrability without any hidden
local-finiteness typeclass on the weighted measure. -/
theorem continuous_integrableOn_ball {μ : Measure ℂ} (hμ : PositiveFiniteBalls μ)
    {g : ℂ → ℝ} (hg : Continuous g) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn g (ball c r) μ :=
  hg.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall c r)
    measurableSet_ball ball_subset_closedBall (hμ c r hr).2.ne

/-- Jensen's elementary integral triangle inequality, with the exact factor one. -/
theorem meanOscillation_le_doubleOscillation {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {f : ℂ → ℝ} (hf : Continuous f)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (⨍ x in ball c r, |f x - (⨍ y in ball c r, f y ∂μ)| ∂μ) ≤
      doubleOscillation μ f c r := by
  let ν := μ.restrict (ball c r)
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using (hμ c r hr).2⟩
  have : NeZero ν := ⟨by
    intro hz
    have : μ (ball c r) = 0 := by simpa [ν] using congrArg (fun η : Measure ℂ => η univ) hz
    exact (hμ c r hr).1.ne' this⟩
  have hfi : Integrable f ν := continuous_integrableOn_ball hμ hf c hr
  have hprod : Integrable (fun p : ℂ × ℂ => |f p.1 - f p.2|) (ν.prod ν) :=
    ((hfi.comp_fst ν).sub (hfi.comp_snd ν)).abs
  have houter : Integrable (fun x => ⨍ y, |f x - f y| ∂ν) ν := by
    simpa only [average_eq, smul_eq_mul] using
      hprod.integral_prod_left.const_mul (ν.real univ)⁻¹
  have hpoint (x : ℂ) : |f x - (⨍ y, f y ∂ν)| ≤ ⨍ y, |f x - f y| ∂ν := by
    calc
      |f x - (⨍ y, f y ∂ν)| = |⨍ y, f x - f y ∂ν| := by
        rw [average_fun_sub (integrable_const _) hfi, average_const]
      _ ≤ ⨍ y, |f x - f y| ∂ν :=
        norm_integral_le_integral_norm (fun y => f x - f y)
  change (⨍ x, |f x - (⨍ y, f y ∂ν)| ∂ν) ≤ ⨍ x, ⨍ y, |f x - f y| ∂ν ∂ν
  simp only [average_eq, smul_eq_mul] at houter hpoint ⊢
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    houter (Filter.Eventually.of_forall hpoint)

/-- The weighted energy is exactly the Lebesgue integral with density `w`. -/
theorem integral_weightMeasure {w g : ℂ → ℝ} (hw : Measurable w)
    (hwn : ∀ᵐ z ∂volume, 0 ≤ w z) {s : Set ℂ} (hs : MeasurableSet s) :
    (∫ z in s, g z ∂weightMeasure w) = ∫ z in s, w z * g z := by
  rw [weightMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul
    hw.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hwn] with z hz
  simp [ENNReal.toReal_ofReal hz]

/-- Cauchy–Schwarz over a Euclidean ball for the actual mixed gradient density. -/
theorem mixedIntegral_le_sqrt_area_energy {w g : ℂ → ℝ}
    (hw : Measurable w) (hwn : ∀ᵐ z ∂volume, 0 ≤ w z)
    (hμ : PositiveFiniteBalls (weightMeasure w)) (hg : Continuous g)
    (hgn : ∀ z, 0 ≤ g z) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z in ball c r, g z * Real.sqrt (w z)) ≤
      Real.sqrt (volume.real (ball c r)) *
        Real.sqrt (∫ z in ball c r, g z ^ 2 ∂weightMeasure w) := by
  let ν := volume.restrict (ball c r)
  have : IsFiniteMeasure ν := ⟨by simp [ν]; finiteness⟩
  have henergy : IntegrableOn (fun z => g z ^ 2) (ball c r) (weightMeasure w) :=
    continuous_integrableOn_ball hμ (hg.pow 2) c hr
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
      ((hg.measurable.mul hw.sqrt).aestronglyMeasurable)).2 hsq
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

/-- Exact planar volume normalization, with the sign of the radius checked. -/
theorem sqrt_volume_ball (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (volume.real (ball c r)) = r * Real.sqrt Real.pi := by
  simp only [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

/-- Doubling for real masses is valid because the upper mass is finite. -/
theorem doubling_real {μ : Measure ℂ} {D : ℝ}
    (hμ : PositiveFiniteBalls μ) (hD : GlobalDoublingWith μ D)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    μ.real (ball c (2 * r)) ≤ D * μ.real (ball c r) := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hμ c r hr).2.ne) (hD.2 c r hr)
  simpa [Measure.real, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_trans zero_le_one hD.1)] using h

/-- Elementary normalization used only after the masses have been proved positive. -/
theorem normalize_energy {E M N D : ℝ} (hE : 0 ≤ E) (hM : 0 < M)
    (hN : 0 < N) (hNM : N ≤ D * M) : E / M ≤ D * (E / N) := by
  calc
    E / M = (N / M) * (E / N) := by field_simp
    _ ≤ D * (E / N) := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ hM).2 hNM) (div_nonneg hE hN.le)

/-- The conditional planar DS consequence needed for the paper's C1 test class.
The DS premise is used directly, and remains a visible unresolved producer. -/
theorem weakOneTwoC1_of_planarDS {D L : ℝ} {w : ℂ → ℝ}
    (hw : Measurable w) (hwn : ∀ᵐ z ∂volume, 0 ≤ w z)
    (hμ : PositiveFiniteBalls (weightMeasure w))
    (hD : GlobalDoublingWith (weightMeasure w) D) (hL : 0 < L)
    (hDS : PlanarDSC1 w L) :
    WeakOneTwoC1 (weightMeasure w) (2 * L * Real.sqrt (Real.pi * D)) 2 := by
  intro f hf c r hr
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
  have hcs := mixedIntegral_le_sqrt_area_energy hw hwn hμ
    (hf.continuous_fderiv one_ne_zero).norm (fun _ => norm_nonneg _) c
    (show 0 < 2 * r by positivity)
  rw [sqrt_volume_ball c (by positivity)] at hcs
  have hnorm := Real.sqrt_le_sqrt (normalize_energy hE hM hN hmass)
  calc
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂μ)| ∂μ)
        ≤ doubleOscillation μ f c r := meanOscillation_le_doubleOscillation hμ hf.continuous c hr
    _ ≤ L / Real.sqrt M * ∫ z in ball c (2 * r), ‖fderiv ℝ f z‖ * Real.sqrt (w z) :=
      hDS f hf c r hr
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

/-- Two doublings beyond `2B`, and `5B ⊆ 8B`, control the larger mass. -/
theorem fiveBallMass_le {μ : Measure ℂ} {D : ℝ}
    (hμ : PositiveFiniteBalls μ) (hD : GlobalDoublingWith μ D)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    μ.real (ball c (5 * r)) ≤ D ^ 2 * μ.real (ball c (2 * r)) := by
  have hDn : 0 ≤ D := le_trans zero_le_one hD.1
  have hmono : μ.real (ball c (5 * r)) ≤ μ.real (ball c (2 * (2 * (2 * r)))) :=
    ENNReal.toReal_mono (hμ c _ (by positivity)).2.ne
      (measure_mono (ball_subset_ball (by linarith)))
  calc
    μ.real (ball c (5 * r)) ≤ μ.real (ball c (2 * (2 * (2 * r)))) := hmono
    _ ≤ D * μ.real (ball c (2 * (2 * r))) := doubling_real hμ hD c (by positivity)
    _ ≤ D * (D * μ.real (ball c (2 * r))) :=
      mul_le_mul_of_nonneg_left (doubling_real hμ hD c (by positivity)) hDn
    _ = D ^ 2 * μ.real (ball c (2 * r)) := by ring

/-- The normalized physical energy at dilation 2 is bounded by `D²` times the
energy average at dilation 5; this is a real integral monotonicity statement. -/
theorem average_energy_two_le_five {μ : Measure ℂ} {D : ℝ}
    (hμ : PositiveFiniteBalls μ) (hD : GlobalDoublingWith μ D)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) ≤
      D ^ 2 * (⨍ z in ball c (5 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) := by
  let E₂ := ∫ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ
  let E₅ := ∫ z in ball c (5 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ
  have h₂ : 0 < μ.real (ball c (2 * r)) := ballMass_pos hμ c (by positivity)
  have h₅ : 0 < μ.real (ball c (5 * r)) := ballMass_pos hμ c (by positivity)
  have hE₅ : 0 ≤ E₅ := integral_nonneg (fun _ => sq_nonneg _)
  have hE : E₂ ≤ E₅ := integral_mono_measure
    (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (continuous_integrableOn_ball hμ ((hf.continuous_fderiv one_ne_zero).norm.pow 2) c
      (by positivity))
  simp only [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul]
  calc
    E₂ / μ.real (ball c (2 * r)) ≤ E₅ / μ.real (ball c (2 * r)) :=
      div_le_div_of_nonneg_right hE h₂.le
    _ ≤ D ^ 2 * (E₅ / μ.real (ball c (5 * r))) :=
      normalize_energy hE₅ h₂ h₅ (fiveBallMass_le hμ hD c hr)

/-- Dilation conversion with the explicit loss `P₅ = P₂ D`. -/
theorem weakOneTwoC1_two_to_five {μ : Measure ℂ} {D P : ℝ}
    (hμ : PositiveFiniteBalls μ) (hD : GlobalDoublingWith μ D) (hP : 0 ≤ P)
    (hPI : WeakOneTwoC1 μ P 2) : WeakOneTwoC1 μ (P * D) 5 := by
  intro f hf c r hr
  have hDn : 0 ≤ D := le_trans zero_le_one hD.1
  have hE := Real.sqrt_le_sqrt (average_energy_two_le_five hμ hD hf c hr)
  rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hDn] at hE
  calc
    _ ≤ P * r * Real.sqrt (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) := hPI f hf c r hr
    _ ≤ P * r * (D * Real.sqrt (⨍ z in ball c (5 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hP hr.le)
    _ = (P * D) * r * Real.sqrt (⨍ z in ball c (5 * r), ‖fderiv ℝ f z‖ ^ 2 ∂μ) := by ring

/-- Combined conditional output with the fixed dilation used by downstream
conditional analytic consumers. This does not discharge `hDS`. -/
theorem weakOneTwoC1_five_of_planarDS {D L : ℝ} {w : ℂ → ℝ}
    (hw : Measurable w) (hwn : ∀ᵐ z ∂volume, 0 ≤ w z)
    (hμ : PositiveFiniteBalls (weightMeasure w))
    (hD : GlobalDoublingWith (weightMeasure w) D) (hL : 0 < L)
    (hDS : PlanarDSC1 w L) :
    WeakOneTwoC1 (weightMeasure w) (2 * L * Real.sqrt (Real.pi * D) * D) 5 :=
  weakOneTwoC1_two_to_five hμ hD (by positivity)
    (weakOneTwoC1_of_planarDS hw hwn hμ hD hL hDS)

/-- Explicit physical-gradient presentation of the conditional dilation-5 result. -/
theorem physicalGradient_poincare_five_of_planarDS {D L : ℝ} {w : ℂ → ℝ}
    (hw : Measurable w) (hwn : ∀ᵐ z ∂volume, 0 ≤ w z)
    (hμ : PositiveFiniteBalls (weightMeasure w))
    (hD : GlobalDoublingWith (weightMeasure w) D) (hL : 0 < L)
    (hDS : PlanarDSC1 w L) (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (⨍ x in ball c r, |f x - (⨍ z in ball c r, f z ∂weightMeasure w)| ∂weightMeasure w) ≤
      (2 * L * Real.sqrt (Real.pi * D) * D) * r *
        Real.sqrt (⨍ z in ball c (5 * r), ‖gradient f z‖ ^ 2 ∂weightMeasure w) := by
  simpa only [norm_gradient_eq_norm_fderiv] using
    weakOneTwoC1_five_of_planarDS hw hwn hμ hD hL hDS f hf c r hr

end RepulsiveCoulomb.PaperRoute.PlanarDS
