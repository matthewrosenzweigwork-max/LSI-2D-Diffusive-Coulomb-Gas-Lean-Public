import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffDerivative
import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual bounded cutoff operators and their strong convergence in the
original weighted L2 space. This is a value-space statement, not joint graph
approximation for the variable-metric adjoint and exterior derivative. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombMetricCutoffLp {N : ℕ} {β R : ℝ} (hR : 0 < R) : Lp ℝ ⊤ (coulombMeasure N β) :=
  ((coulombMetricCutoffTest (N := N) hR).memLp_top (μ := coulombMeasure N β)).toLp
    (coulombMetricCutoff R)

theorem coulombMetricCutoffLp_coe {N : ℕ} {β R : ℝ} (hR : 0 < R) :
    coulombMetricCutoffLp (N := N) (β := β) hR =ᵐ[coulombMeasure N β] coulombMetricCutoff R :=
  MemLp.coeFn_toLp _

def coulombMetricCutoffL2L {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 (coulombMeasure N β) →L[ℝ] Lp F 2 (coulombMeasure N β) :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).holderL
    (coulombMeasure N β) ⊤ 2 2 (coulombMetricCutoffLp hR)

theorem coulombMetricCutoffL2L_coe {N : ℕ} {β R : ℝ} (hR : 0 < R)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Lp F 2 (coulombMeasure N β)) :
    coulombMetricCutoffL2L hR F f =ᵐ[coulombMeasure N β] fun z => coulombMetricCutoff R z • f z := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).coeFn_holder
    (r := 2) (coulombMetricCutoffLp (N := N) (β := β) hR) f,
    coulombMetricCutoffLp_coe (N := N) (β := β) hR]
    with z hz hθ
  change ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).holder 2
    (coulombMetricCutoffLp hR) f) z = _
  rw [hz, hθ]
  rfl

theorem coulombMetricCutoffL2L_contraction {N : ℕ} {β R : ℝ} (hR : 0 < R)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Lp F 2 (coulombMeasure N β)) :
    ‖coulombMetricCutoffL2L hR F f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coulombMetricCutoffL2L_coe hR f] with z hz
  rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (coulombMetricCutoff_nonneg R z)]
  exact mul_le_of_le_one_left (norm_nonneg _) (coulombMetricCutoff_le_one R z)

theorem dbarRealHilbertLp_norm_sq {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {μ : Measure X} (f : Lp F 2 μ) :
    ‖f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => real_inner_self_eq_norm_sq (f z)

theorem coulombMetricCutoffL2L_tendsto {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f : Lp F 2 (coulombMeasure N β)) :
    Tendsto (fun n : ℕ => coulombMetricCutoffL2L (N := N) (β := β)
      (by positivity : 0 < (n : ℝ) + 1) F f) atTop (𝓝 f) := by
  let R : ℕ → ℝ := fun n => (n : ℝ) + 1
  let u : ℕ → Lp F 2 (coulombMeasure N β) := fun n => coulombMetricCutoffL2L (by dsimp [R]; positivity : 0 < R n) F f
  let e : ℕ → CoulombConfig N → ℝ := fun n z => ‖(coulombMetricCutoff (R n) z - 1) • f z‖ ^ 2
  have heq (n : ℕ) : ‖u n - f‖ ^ 2 = ∫ z, e n z ∂coulombMeasure N β := by
    rw [dbarRealHilbertLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) f,
      coulombMetricCutoffL2L_coe (by dsimp [R]; positivity : 0 < R n) f] with z hsub hu
    change u n z = coulombMetricCutoff (R n) z • f z at hu
    simp only [e, hsub, Pi.sub_apply, hu, sub_smul, one_smul]
  have hem (n : ℕ) : AEStronglyMeasurable (e n) (coulombMeasure N β) := by
    have hθ : AEStronglyMeasurable (coulombMetricCutoff (N := N) (R n)) (coulombMeasure N β) :=
      (coulombMetricCutoff_contDiff (N := N) (by dsimp [R]; positivity : 0 < R n)).continuous.aestronglyMeasurable
    exact (((hθ.sub aestronglyMeasurable_const).smul (Lp.aestronglyMeasurable f)).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have heb (n : ℕ) : ∀ᵐ z ∂coulombMeasure N β, ‖e n z‖ ≤ ‖f z‖ ^ 2 := by
    apply Eventually.of_forall
    intro z
    have hθ : |coulombMetricCutoff (R n) z - 1| ≤ 1 :=
      abs_le.mpr ⟨by linarith [coulombMetricCutoff_nonneg (R n) z],
        by linarith [coulombMetricCutoff_le_one (R n) z]⟩
    have hn : ‖(coulombMetricCutoff (R n) z - 1) • f z‖ ≤ ‖f z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hθ
    change |‖(coulombMetricCutoff (R n) z - 1) • f z‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hel : ∀ᵐ z ∂coulombMeasure N β, Tendsto (fun n => e n z) atTop (𝓝 0) := by
    filter_upwards [(coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz
    have hR : Tendsto R atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hθ : Tendsto (fun n => coulombMetricCutoff (R n) z) atTop (𝓝 1) := by
      simpa only [Function.comp_def] using (coulombMetricCutoff_tendsto_one hz).comp hR
    have h := ((hθ.sub_const 1).smul_const (f z)).norm.pow 2
    simpa only [e, sub_self, zero_smul, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h
  have hbound : Integrable (fun z => ‖f z‖ ^ 2) (coulombMeasure N β) :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hint : Tendsto (fun n => ∫ z, e n z ∂coulombMeasure N β) atTop
      (𝓝 (∫ _z : CoulombConfig N, (0 : ℝ) ∂coulombMeasure N β)) :=
    tendsto_integral_of_dominated_convergence (μ := coulombMeasure N β)
      (F := e) (f := fun _ => (0 : ℝ)) (fun z => ‖f z‖ ^ 2) hem hbound heb hel
  have hsq : Tendsto (fun n => ‖u n - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq, integral_zero] using hint
  change Tendsto u atTop (𝓝 f)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end RepulsiveCoulomb
