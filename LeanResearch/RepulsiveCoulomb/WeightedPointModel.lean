module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Elab.Command

@[expose] public section

/-!
Concrete unnormalized point-weighted Gaussian of Theorem 1.2 (eq. 1.11).
Source SHA256: 334c42429035ed3f994e16ec801ccb5568c43ca85c4750ecb89ef68a7c1f5e42.
The functions use genuine positive real powers of distances. Their Gaussian
normalization, Sobolev domain and uniform functional inequalities remain
separate obligations, not fields assumed by this model.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace RepulsiveCoulomb

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Literal density before normalization, with a finite indexed point family. -/
def pointWeight {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  Real.exp (-γ * ‖z‖ ^ 2 / 2) * ∏ j, ‖z - y j‖ ^ a j

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The removed points are precisely those carrying a positive exponent. -/
def pointPunctures {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Set ℂ :=
  {z | ∃ j, 0 < a j ∧ z = y j}

/-- No separation or cardinality hypothesis is imposed on the point family. -/
def pointWeightAdmissible {m : ℕ} (γ Q : ℝ) (a : Fin m → ℝ) : Prop :=
  0 < γ ∧ (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ Q

theorem pointWeight_nonneg {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) (z : ℂ) : 0 ≤ pointWeight γ a y z := by
  unfold pointWeight
  exact mul_nonneg (le_of_lt (Real.exp_pos _))
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (norm_nonneg _) _)

theorem pointWeight_pos_of_avoids {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) {z : ℂ} (hz : ∀ j, z ≠ y j) : 0 < pointWeight γ a y z := by
  unfold pointWeight
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro j _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hz j))) _

theorem pointWeight_zero_exponents {m : ℕ} (γ : ℝ) (y : Fin m → ℂ) (z : ℂ) :
    pointWeight γ (fun _ ↦ 0) y z = Real.exp (-γ * ‖z‖ ^ 2 / 2) := by
  simp [pointWeight]

theorem pointWeight_empty (γ : ℝ) (a : Fin 0 → ℝ) (y : Fin 0 → ℂ) (z : ℂ) :
    pointWeight γ a y z = Real.exp (-γ * ‖z‖ ^ 2 / 2) := by
  simp [pointWeight]

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Extended normalization avoids assuming the Gaussian-polynomial integral
is already finite. Proving that it is finite and positive is still required. -/
def pointPartition {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) : ℝ≥0∞ :=
  ∫⁻ z : ℂ, ENNReal.ofReal (pointWeight γ a y z)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def pointMeasure {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) : Measure ℂ :=
  (pointPartition γ a y)⁻¹ •
    volume.withDensity (fun z ↦ ENNReal.ofReal (pointWeight γ a y z))


/-- Zero exponents create no artificial punctures or zeros of the weight. -/
theorem pointWeight_pos_off_punctures {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) : 0 < pointWeight γ a y z := by
  unfold pointWeight
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro j _
  by_cases hj : a j = 0
  · simp [hj]
  · have hjpos : 0 < a j := lt_of_le_of_ne (ha j) (Ne.symm hj)
    have hzy : z ≠ y j := by
      intro heq
      exact hz ⟨j, hjpos, heq⟩
    exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzy)) _

/-- The singular repulsive density actually vanishes at each positive point. -/
theorem pointWeight_eq_zero_at_puncture {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) {z : ℂ} (hz : z ∈ pointPunctures a y) :
    pointWeight γ a y z = 0 := by
  obtain ⟨j, hj, rfl⟩ := hz
  have hzero : ∏ k : Fin m, ‖y j - y k‖ ^ a k = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Real.zero_rpow (ne_of_gt hj)]
  simp [pointWeight, hzero]

theorem pointWeight_measurable {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) : Measurable (pointWeight γ a y) := by
  have hg : Continuous (fun z : ℂ ↦ Real.exp (-γ * ‖z‖ ^ 2 / 2)) := by
    fun_prop
  have hp : Measurable (fun z : ℂ ↦ ∏ j, ‖z - y j‖ ^ a j) := by
    exact Finset.univ.measurable_fun_prod (fun j _ ↦
      (continuous_norm.comp (continuous_id.sub continuous_const)).measurable.pow_const (a j))
  exact hg.measurable.mul hp

/-- This is only normalization conditional on its explicit finite-positive
integral hypotheses; those hypotheses are not the weighted theorem. -/
theorem pointMeasure_isProbability_of_partition {m : ℕ} (γ : ℝ)
    (a : Fin m → ℝ) (y : Fin m → ℂ)
    (hpos : pointPartition γ a y ≠ 0) (hfinite : pointPartition γ a y ≠ ⊤) :
    IsProbabilityMeasure (pointMeasure γ a y) := by
  constructor
  simp only [pointMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos hfinite

end RepulsiveCoulomb
