import LeanResearch.RepulsiveCoulomb.PointCutoffBump
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Configuration-dependent point-puncture estimates for the literal normalized
weighted planar Gaussian. No separation is assumed. A selected positive exponent
is retained; all other factors, including coincident ones, are bounded on a compact ball.
This is development work toward the manuscript's capacity and common-core step. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

/-- Local power-law upper bound, retaining any chosen point exponent. -/
theorem pointDensity_le_local_power {m : ℕ} {γ : ℝ} (_hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (j : Fin m) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ closedBall (y j) R,
      pointDensity γ a y z ≤ C * ‖z - y j‖ ^ a j := by
  classical
  let F : ℂ → ℝ := fun z ↦ (∫ x : ℂ, pointWeight γ a y x)⁻¹ *
    Real.exp (-γ * ‖z‖ ^ 2 / 2) * ∏ k ∈ Finset.univ.erase j, ‖z - y k‖ ^ a k
  have hF : Continuous F := by
    apply Continuous.mul
    · fun_prop
    · apply continuous_finsetProd
      intro k _
      exact (Real.continuous_rpow_const (ha k)).comp (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (y j) R).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro z hz
  have hfactor : pointDensity γ a y z = F z * ‖z - y j‖ ^ a j := by
    dsimp [pointDensity, pointWeight, F]
    have hp := Finset.prod_erase_mul (Finset.univ : Finset (Fin m)) (fun k ↦ ‖z - y k‖ ^ a k) (Finset.mem_univ j)
    rw [← hp]
    ring
  rw [hfactor]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
  have h := hC z hz
  have hle : F z ≤ |C| + 1 := by
    have := le_abs_self (F z)
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self C]
  exact hle

theorem pointDensity_nonneg {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    0 ≤ pointDensity γ a y z :=
  mul_nonneg (inv_nonneg.mpr (pointWeight_integral_pos hγ ha y).le)
    (pointWeight_nonneg γ a y z)

theorem pointCutoff_energy_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun z ↦ ‖gradient (pointCutoffBump c ε hε) z‖ ^ 2)
      (pointMeasure γ a y) := by
  let _ := pointMeasure_isProbability hγ ha y
  have hc := TauCeti.continuous_gradient_testFunction (pointCutoffTestFunction c ε hε)
  have hs := TauCeti.hasCompactSupport_gradient_testFunction (pointCutoffTestFunction c ε hε)
  change Continuous (fun z ↦ gradient (pointCutoffBump c ε hε) z) at hc
  change HasCompactSupport (fun z ↦ gradient (pointCutoffBump c ε hε) z) at hs
  have hs2 : HasCompactSupport (fun z ↦ ‖gradient (pointCutoffBump c ε hε) z‖ ^ 2) :=
    hs.comp_left (g := fun v : ℂ ↦ ‖v‖ ^ 2) (by simp)
  exact (hc.norm.pow 2).integrable_of_hasCompactSupport hs2

theorem pointCutoff_energy_density_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    (∫ z, ‖gradient (pointCutoffBump c ε hε) z‖ ^ 2 ∂pointMeasure γ a y) =
    ∫ z : ℂ, pointDensity γ a y z * ‖gradient (pointCutoffBump c ε hε) z‖ ^ 2 := by
  rw [pointMeasure_eq_withDensity hγ ha y,
    integral_withDensity_eq_integral_toReal_smul
      (pointDensity_continuous γ ha y).measurable.ennreal_ofReal (by simp)]
  congr 1
  funext z
  simp only [ENNReal.toReal_ofReal (pointDensity_nonneg hγ ha y z), smul_eq_mul]

/-- Energy bound at a selected puncture; the constant is configuration-dependent. -/
theorem pointCutoff_energy_bound {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (j : Fin m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      (∫ z, ‖gradient (pointCutoffBump (y j) ε hε) z‖ ^ 2 ∂pointMeasure γ a y)
        ≤ K * ε ^ a j := by
  obtain ⟨C, hC, hlocal⟩ := pointDensity_le_local_power hγ ha y j 2
  obtain ⟨B, hB, hgrad⟩ := exists_pointCutoffBump_gradient_bound
  refine ⟨C * B ^ 2 * 2 ^ a j * 4 * Real.pi, by positivity, ?_⟩
  intro ε hε hε1
  let f : ℂ → ℝ := fun z ↦ pointDensity γ a y z *
    ‖gradient (pointCutoffBump (y j) ε hε) z‖ ^ 2
  have hn : ∀ z, 0 ≤ f z := fun z ↦
    mul_nonneg (pointDensity_nonneg hγ ha y z) (sq_nonneg _)
  have hbound : ∀ z ∈ closedBall (y j) (2 * ε),
      ‖f z‖ ≤ C * (2 * ε) ^ a j * (B / ε) ^ 2 := by
    intro z hz
    have hz2 : z ∈ closedBall (y j) 2 :=
      closedBall_subset_closedBall (by linarith) hz
    have hdist : ‖z - y j‖ ≤ 2 * ε := by simpa [mem_closedBall, dist_eq_norm] using hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hn z)]
    dsimp [f]
    apply mul_le_mul
    · exact (hlocal z hz2).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hdist (ha j)) hC.le)
    · exact pow_le_pow_left₀ (norm_nonneg _) (hgrad (y j) ε hε z) 2
    · positivity
    · positivity
  have hs : (∫ z in closedBall (y j) (2 * ε), f z) = ∫ z, f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    dsimp [f]
    rw [pointCutoffBump_gradient_zero (y j) ε hε hz]
    simp
  rw [pointCutoff_energy_density_integral hγ ha y]
  change (∫ z, f z) ≤ _
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℂ)) (isCompact_closedBall (y j) (2 * ε)).measure_lt_top hbound
  rw [hs] at hb
  have hv : volume.real (closedBall (y j) (2 * ε)) = (2 * ε) ^ 2 * Real.pi := by
    simp [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]
  rw [hv] at hb
  calc
    (∫ z, f z) ≤ ‖∫ z, f z‖ := le_abs_self _
    _ ≤ (C * (2 * ε) ^ a j * (B / ε) ^ 2) * ((2 * ε) ^ 2 * Real.pi) := hb
    _ = (C * B ^ 2 * 2 ^ a j * 4 * Real.pi) * ε ^ a j := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hε.le]
      field_simp
      ring

/-- For every positive scale family tending to zero, the weighted cutoff energy
vanishes at a location carrying a positive exponent. -/
theorem pointCutoff_energy_tendsto_zero {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (j : Fin m) (hj : 0 < a j) {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ t, 0 < ε t) (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun t ↦ ∫ z, ‖gradient (pointCutoffBump (y j) (ε t) (hε t)) z‖ ^ 2
      ∂pointMeasure γ a y) l (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := pointCutoff_energy_bound hγ ha y j
  apply squeeze_zero'
  · exact Eventually.of_forall fun t ↦ integral_nonneg (fun z ↦ sq_nonneg _)
  · filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hb (ε t) (hε t) ht
  · have hp := ((Real.continuous_rpow_const hj.le).tendsto 0).comp hlim
    simpa only [Real.zero_rpow hj.ne', mul_zero, Function.comp_apply] using hp.const_mul K

end RepulsiveCoulomb
