import LeanResearch.RepulsiveCoulomb.PointWeightBounds

/-! Local comparison for the literal normalized weighted Gaussian.
These compact-set constants may depend on the configuration and the set.
They provide a local input to closability, not the configuration-uniform
weighted Sobolev estimate or closability itself. Positive-exponent points
are the only punctures; no artificial puncture is imposed at zero exponents.
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb

theorem pointWeight_integral_pos {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    0 < ∫ z : ℂ, pointWeight γ a y z := by
  have h := pointPartition_pos γ a y
  rw [pointPartition_eq_ofReal_integral hγ ha y] at h
  exact ENNReal.ofReal_pos.mp h

/-- Real normalized density; admissible uses below establish its denominator. -/
def pointDensity {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  (∫ x : ℂ, pointWeight γ a y x)⁻¹ * pointWeight γ a y z

theorem pointDensity_continuous {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : Continuous (pointDensity γ a y) :=
  (pointWeight_continuous γ ha y).const_mul _

theorem pointDensity_pos_off_punctures {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {z : ℂ} (hz : z ∉ pointPunctures a y) : 0 < pointDensity γ a y z :=
  mul_pos (inv_pos.mpr (pointWeight_integral_pos hγ ha y))
    (pointWeight_pos_off_punctures γ ha y hz)

theorem pointDensity_pos_ae {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∀ᵐ z : ℂ, 0 < pointDensity γ a y z := by
  filter_upwards [pointWeight_pos_ae γ a y] with z hz
  exact mul_pos (inv_pos.mpr (pointWeight_integral_pos hγ ha y)) hz

theorem pointMeasure_eq_withDensity {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointMeasure γ a y = volume.withDensity (fun z ↦ ENNReal.ofReal (pointDensity γ a y z)) := by
  have hZ := pointWeight_integral_pos hγ ha y
  rw [pointMeasure, pointPartition_eq_ofReal_integral hγ ha y,
    ← withDensity_smul _ (pointWeight_measurable γ a y).ennreal_ofReal]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, pointDensity,
    ENNReal.ofReal_mul (inv_pos.mpr hZ).le, ENNReal.ofReal_inv_of_pos hZ]

theorem pointMeasure_ae_iff {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : ℂ → Prop} :
    (∀ᵐ z ∂pointMeasure γ a y, P z) ↔ ∀ᵐ z : ℂ, P z := by
  rw [pointMeasure_eq_withDensity hγ ha y,
    ae_withDensity_iff (pointDensity_continuous γ ha y).measurable.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, pointDensity_pos_ae hγ ha y] with z hz hp
    exact hz (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
  · intro h
    filter_upwards [h] with z hz
    exact fun _ ↦ hz

theorem pointDensity_bounds_on_compact {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ K, c ≤ pointDensity γ a y z ∧ pointDensity γ a y z ≤ C := by
  by_cases hne : K.Nonempty
  · obtain ⟨zmin, hzmin, hmin⟩ := hK.exists_isMinOn hne (pointDensity_continuous γ ha y).continuousOn
    obtain ⟨zmax, hzmax, hmax⟩ := hK.exists_isMaxOn hne (pointDensity_continuous γ ha y).continuousOn
    refine ⟨pointDensity γ a y zmin, pointDensity γ a y zmax,
      pointDensity_pos_off_punctures hγ ha y (havoid hzmin),
      pointDensity_pos_off_punctures hγ ha y (havoid hzmax), ?_⟩
    intro z hz
    exact ⟨hmin hz, hmax hz⟩
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

/-- Two-sided local comparison with Lebesgue measure. The constants are local,
not uniform in the point configuration. -/
theorem pointMeasure_restrict_comparison {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ENNReal.ofReal c • volume.restrict K ≤ (pointMeasure γ a y).restrict K ∧
      (pointMeasure γ a y).restrict K ≤ ENNReal.ofReal C • volume.restrict K := by
  obtain ⟨c, C, hc, hC, hb⟩ := pointDensity_bounds_on_compact hγ ha y hK havoid
  refine ⟨c, C, hc, hC, ?_, ?_⟩
  · rw [pointMeasure_eq_withDensity hγ ha y, restrict_withDensity hK.isClosed.measurableSet,
      ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact ENNReal.ofReal_le_ofReal (hb z hz).1
  · rw [pointMeasure_eq_withDensity hγ ha y, restrict_withDensity hK.isClosed.measurableSet,
      ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact ENNReal.ofReal_le_ofReal (hb z hz).2

end RepulsiveCoulomb
