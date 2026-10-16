module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterChart
public import LeanResearch.RepulsiveCoulomb.PointMeasureParametric

@[expose] public section

/-! Actual normalized all-particle center/relative product measure. All
normalization and probability assertions are proved from the literal density;
there is no measure-factorization or integrability premise. The chart parameter
is an algebraic isometry with diagonal inverse first axis. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterGaussianWeight (β : ℝ) (c : ℂ) : ℝ :=
  Real.exp (-β * ‖c‖ ^ 2 / 2)

def coulombCenterGaussianPartition (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ c : ℂ, ENNReal.ofReal (coulombCenterGaussianWeight β c)

def coulombCenterGaussian (β : ℝ) : Measure ℂ :=
  (coulombCenterGaussianPartition β)⁻¹ •
    volume.withDensity (fun c => ENNReal.ofReal (coulombCenterGaussianWeight β c))

def coulombCenterRelativeWeight (e : CoulombCenterRotation n) (β : ℝ)
    (r : CoulombConfig n) : ℝ := coulombWeight β (coulombCenterInsert e 0 r)

def coulombCenterRelativePartition (e : CoulombCenterRotation n) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : CoulombConfig n, ENNReal.ofReal (coulombCenterRelativeWeight e β r)

def coulombCenterRelativeMeasure (e : CoulombCenterRotation n) (β : ℝ) :
    Measure (CoulombConfig n) :=
  (coulombCenterRelativePartition e β)⁻¹ •
    volume.withDensity (fun r => ENNReal.ofReal (coulombCenterRelativeWeight e β r))

theorem coulombCenterGaussianWeight_measurable (β : ℝ) :
    Measurable (coulombCenterGaussianWeight β) := by
  unfold coulombCenterGaussianWeight
  fun_prop

theorem coulombCenterRelativeWeight_measurable (e : CoulombCenterRotation n)
    {β : ℝ} (hβ : 0 ≤ β) : Measurable (coulombCenterRelativeWeight e β) := by
  have hi : Measurable (fun r : CoulombConfig n => coulombCenterInsert e 0 r) := by
    have h : Measurable (fun r : CoulombConfig n => (coulombCenterChart e).symm ((0 : ℂ), r)) :=
      (coulombCenterChart e).symm.measurable.comp
        (measurable_const.prodMk measurable_id)
    simpa only [coulombCenterChart_symm_apply] using h
  exact (coulombWeight_continuous hβ).measurable.comp hi

theorem coulombCenterGaussian_eq_pointMeasure (β : ℝ) :
    coulombCenterGaussian β =
      pointMeasure β (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : ℂ)) := by
  simp only [coulombCenterGaussian, coulombCenterGaussianPartition,
    coulombCenterGaussianWeight, pointMeasure, pointPartition, pointWeight_empty]

theorem coulombCenterGaussianPartition_eq_pointPartition (β : ℝ) :
    coulombCenterGaussianPartition β =
      pointPartition β (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : ℂ)) := by
  simp only [coulombCenterGaussianPartition, coulombCenterGaussianWeight,
    pointPartition, pointWeight_empty]

theorem coulombCenterGaussianPartition_pos (β : ℝ) :
    0 < coulombCenterGaussianPartition β := by
  rw [coulombCenterGaussianPartition_eq_pointPartition]
  exact pointPartition_pos _ _ _

theorem coulombCenterGaussianPartition_lt_top {β : ℝ} (hβ : 0 < β) :
    coulombCenterGaussianPartition β < ∞ := by
  rw [coulombCenterGaussianPartition_eq_pointPartition]
  exact pointPartition_lt_top hβ (fun _ => le_rfl) _

theorem coulombCenterGaussian_isProbability {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (coulombCenterGaussian β) := by
  rw [coulombCenterGaussian_eq_pointMeasure]
  exact pointMeasure_isProbability hβ (fun _ => le_rfl) _

/-- Tonelli change of variables, with the unchanged β/(n+1) interaction. -/
theorem coulombCenter_raw_lintegral (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 ≤ β)
    {F : CoulombConfig (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, ENNReal.ofReal (coulombWeight β z) * F z) =
      ∫⁻ c : ℂ, ENNReal.ofReal (coulombCenterGaussianWeight β c) *
        ∫⁻ r : CoulombConfig n, ENNReal.ofReal (coulombCenterRelativeWeight e β r) *
          F (coulombCenterInsert e c r) := by
  have hw := (coulombWeight_continuous (N := n + 1) hβ).measurable.ennreal_ofReal.mul hF
  have hpull := (coulombCenterChart_measurePreserving e).symm.lintegral_comp hw
  have hs : ((coulombCenterChart e).symm : ℂ × CoulombConfig n → CoulombConfig (n + 1)) =
      fun p => coulombCenterInsert e p.1 p.2 := by
    funext p
    exact coulombCenterChart_symm_apply e p.1 p.2
  rw [hs] at hpull
  dsimp only [Pi.mul_apply] at hpull
  rw [← hpull]
  have hprod : Measurable (fun p : ℂ × CoulombConfig n =>
      ENNReal.ofReal (coulombWeight β (coulombCenterInsert e p.1 p.2)) *
        F (coulombCenterInsert e p.1 p.2)) := by
    have h := hw.comp (coulombCenterChart e).symm.measurable
    rw [hs] at h
    exact h
  rw [Measure.volume_eq_prod ℂ (CoulombConfig n),
    lintegral_prod (μ := volume) (ν := volume) _ hprod.aemeasurable]
  apply lintegral_congr
  intro c
  change (∫⁻ r : CoulombConfig n,
    ENNReal.ofReal (coulombWeight β (coulombCenterInsert e c r)) *
      F (coulombCenterInsert e c r)) = _
  have hfactor (r : CoulombConfig n) :
      coulombWeight β (coulombCenterInsert e c r) =
        coulombCenterGaussianWeight β c * coulombCenterRelativeWeight e β r :=
    coulombCenterInsert_weight e he β c r
  have hg0 : 0 ≤ coulombCenterGaussianWeight β c := (Real.exp_pos _).le
  simp_rw [hfactor, ENNReal.ofReal_mul hg0, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The full normalizer is the product of the two raw normalizers. -/
theorem coulombCenter_partition (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 ≤ β) :
    coulombPartition (n + 1) β =
      coulombCenterGaussianPartition β * coulombCenterRelativePartition e β := by
  have h := coulombCenter_raw_lintegral e he hβ (F := fun _ => 1) measurable_const
  simp only [mul_one] at h
  change coulombPartition (n + 1) β = _ at h
  rw [h]
  exact lintegral_mul_const _ (coulombCenterGaussianWeight_measurable β).ennreal_ofReal

theorem coulombCenterRelativePartition_pos (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    0 < coulombCenterRelativePartition e β := by
  have h := coulombPartition_pos (N := n + 1) hβ
  rw [coulombCenter_partition e he hβ.le] at h
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at h
  exact (lt_irrefl _ h)

theorem coulombCenterRelativePartition_lt_top (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    coulombCenterRelativePartition e β < ∞ := by
  have h := (coulombPartition_lt_top (N := n + 1) hβ).ne
  rw [coulombCenter_partition e he hβ.le] at h
  exact ENNReal.lt_top_of_mul_ne_top_right h (coulombCenterGaussianPartition_pos β).ne'

theorem coulombCenterRelativeMeasure_isProbability (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (coulombCenterRelativeMeasure e β) := by
  constructor
  simp only [coulombCenterRelativeMeasure, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (coulombCenterRelativePartition_pos e he hβ).ne'
    (coulombCenterRelativePartition_lt_top e he hβ).ne

/-- Exact normalized factorization against arbitrary nonnegative measurable tests. -/
theorem coulombCenter_lintegral (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    {F : ℂ × CoulombConfig n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F (coulombCenterChart e z) ∂coulombMeasure (n + 1) β) =
      ∫⁻ p, F p ∂(coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β) := by
  have hgc := (coulombCenterGaussianWeight_measurable β).ennreal_ofReal
  have hrc := (coulombCenterRelativeWeight_measurable e hβ.le).ennreal_ofReal
  have hFc : Measurable (fun z => F (coulombCenterChart e z)) :=
    hF.comp (coulombCenterChart e).measurable
  rw [coulombMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume
      (coulombWeight_continuous hβ.le).measurable.ennreal_ofReal
      hFc]
  dsimp only [Pi.mul_apply]
  rw [coulombCenter_raw_lintegral e he hβ.le
    hFc]
  simp only [coulombCenterChart_insert]
  have hwprod : Measurable (fun p : ℂ × CoulombConfig n =>
      ENNReal.ofReal (coulombCenterGaussianWeight β p.1) *
        ENNReal.ofReal (coulombCenterRelativeWeight e β p.2)) :=
    (hgc.comp measurable_fst).mul (hrc.comp measurable_snd)
  have hwpF : Measurable (fun p : ℂ × CoulombConfig n =>
      (ENNReal.ofReal (coulombCenterGaussianWeight β p.1) *
        ENNReal.ofReal (coulombCenterRelativeWeight e β p.2)) * F p) := hwprod.mul hF
  rw [coulombCenterGaussian, coulombCenterRelativeMeasure,
    Measure.prod_smul_left, Measure.prod_smul_right,
    lintegral_smul_measure, lintegral_smul_measure,
    prod_withDensity hgc hrc,
    lintegral_withDensity_eq_lintegral_mul _ hwprod hF]
  dsimp only [Pi.mul_apply]
  rw [lintegral_prod (μ := volume) (ν := volume) _ hwpF.aemeasurable]
  rw [coulombCenter_partition e he hβ.le,
    ENNReal.mul_inv (Or.inl (coulombCenterGaussianPartition_pos β).ne')
      (Or.inl (coulombCenterGaussianPartition_lt_top hβ).ne)]
  simp_rw [mul_assoc, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [smul_eq_mul, mul_assoc]

/-- Product law on the actual center and relative coordinate spaces. -/
theorem coulombCenter_joint_law (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    Measure.map (coulombCenterChart e) (coulombMeasure (n + 1) β) =
      (coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (coulombCenterChart e).measurable]
  exact coulombCenter_lintegral e he hβ hF

end RepulsiveCoulomb
