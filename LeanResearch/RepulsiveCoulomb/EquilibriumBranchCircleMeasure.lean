import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircularRegularization
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Actual circular probability measures for the forthcoming double-smearing
construction. They are nonatomic and supported on a Lebesgue-null circle;
they are not asserted to have a planar density. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def equilibriumAngleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ioc 0 (2 * Real.pi))

instance equilibriumAngleMeasure_probability : IsProbabilityMeasure equilibriumAngleMeasure := by
  constructor
  simp only [equilibriumAngleMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
    ENNReal.ofReal_ne_top

def equilibriumCircleMeasure (c : ℂ) (ε : ℝ) : Measure ℂ :=
  Measure.map (circleMap c ε) equilibriumAngleMeasure

instance equilibriumCircleMeasure_probability (c : ℂ) (ε : ℝ) :
    IsProbabilityMeasure (equilibriumCircleMeasure c ε) := by
  unfold equilibriumCircleMeasure
  infer_instance

theorem integral_equilibriumCircleMeasure (c : ℂ) (ε : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂equilibriumCircleMeasure c ε) = Real.circleAverage f c ε := by
  unfold equilibriumCircleMeasure
  rw [integral_map (measurable_circleMap c ε).aemeasurable hf.aestronglyMeasurable]
  unfold equilibriumAngleMeasure
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal Real.two_pi_pos.le, smul_eq_mul,
    Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]

theorem equilibriumCircleMeasure_supported (c : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    equilibriumCircleMeasure c ε (sphere c ε)ᶜ = 0 := by
  have he : circleMap c ε ⁻¹' (sphere c ε)ᶜ = ∅ := by
    ext θ
    constructor
    · intro h
      exact (h (circleMap_mem_sphere c hε θ)).elim
    · simp
  rw [equilibriumCircleMeasure,
    Measure.map_apply (measurable_circleMap c ε) isClosed_sphere.measurableSet.compl, he,
    measure_empty]

/-- Circular smearing is nonatomic at every strictly positive radius. -/
theorem equilibriumCircleMeasure_singleton (c z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    equilibriumCircleMeasure c ε {z} = 0 := by
  have hinj : (Ioc (0 : ℝ) (2 * Real.pi)).InjOn (circleMap c ε) := by
    have h := injOn_circleMap_of_abs_sub_le (c := c) (a := 0) (b := 2 * Real.pi) hε.ne'
      (show |(0 : ℝ) - 2 * Real.pi| ≤ 2 * Real.pi by
        simp only [zero_sub, abs_neg, abs_of_pos Real.two_pi_pos, le_refl])
    simpa only [Set.uIoc_of_le Real.two_pi_pos.le] using h
  let E : Set ℝ := (circleMap c ε ⁻¹' {z}) ∩ Ioc 0 (2 * Real.pi)
  have hE : E.Subsingleton := by
    intro a ha b hb
    apply hinj ha.2 hb.2
    exact ha.1.trans hb.1.symm
  have hE0 : volume E = 0 := hE.countable.measure_zero volume
  have hm : MeasurableSet (circleMap c ε ⁻¹' {z}) :=
    (measurableSet_singleton z).preimage (measurable_circleMap c ε)
  rw [equilibriumCircleMeasure, Measure.map_apply (measurable_circleMap c ε) (measurableSet_singleton z),
    equilibriumAngleMeasure, Measure.smul_apply, Measure.restrict_apply hm]
  change (ENNReal.ofReal (2 * Real.pi))⁻¹ * volume E = 0
  rw [hE0, mul_zero]

theorem equilibriumCircleMeasure_nullSingleton (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    NullSingletonClass (equilibriumCircleMeasure c ε) :=
  ⟨fun z => equilibriumCircleMeasure_singleton c z hε⟩

/-- The supporting circle has zero planar volume, regardless of center or radius. -/
theorem equilibriumCircle_support_volume_zero (c : ℂ) (ε : ℝ) :
    (volume : Measure ℂ) (sphere c ε) = 0 := Measure.addHaar_sphere volume c ε

/-- Smearing an absolutely continuous reference retains absolute continuity;
this does not claim absolute continuity for the circle measure itself. -/
theorem equilibriumCircle_convolution_absolutelyContinuous (c : ℂ) (ε : ℝ)
    {μ : Measure ℂ} [SFinite μ] (hμ : μ ≪ volume) :
    (equilibriumCircleMeasure c ε).conv μ ≪ volume :=
  Measure.conv_absolutelyContinuous hμ

end RepulsiveCoulomb
