module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Quantitative comparison for the original paper's diameter-ball gauge

This independent module formalizes the measure-comparison step in the original
Bonk–Lang / Semmes route. The ball is exactly the Euclidean ball with diameter
`[x,y]`. A metric-doubling witness contains an actual `MetricSpace ℂ`; it is not
an arbitrary real-valued function or an assumed downstream inequality.

The comparison theorem preserves that same metric, multiplying the measure
doubling constant by `C^2` and the gauge-comparison constant by `sqrt C`.
Positive, finite mass of every positive-radius Euclidean ball is explicit.
This module does not prove the quasiconformal-Jacobian producer, comparison
with a weighted path metric, or a Poincaré / Sobolev inequality.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb.PaperRoute

/-- The original manuscript's open Euclidean diameter ball. -/
def euclideanDiameterBall (x y : ℂ) : Set ℂ :=
  Metric.ball ((x + y) / 2) (dist x y / 2)

/-- The genuine extended nonnegative mass underlying the diameter gauge. -/
def diameterBallMass (μ : Measure ℂ) (x y : ℂ) : ℝ≥0∞ :=
  μ (euclideanDiameterBall x y)

/-- The planar weighted-volume gauge. Finiteness is required separately. -/
def diameterGauge (μ : Measure ℂ) (x y : ℂ) : ℝ :=
  Real.sqrt (diameterBallMass μ x y).toReal

/-- Nonzero and finite mass is required on every positive-radius ambient ball. -/
def PositiveFiniteBalls (μ : Measure ℂ) : Prop :=
  ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    0 < μ (Metric.ball c r) ∧ μ (Metric.ball c r) < ⊤

/-- Quantitative doubling uses ambient Euclidean balls, not the witness metric. -/
def GlobalDoublingWith (μ : Measure ℂ) (D : ℝ) : Prop :=
  1 ≤ D ∧ ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    μ (Metric.ball c (2 * r)) ≤ ENNReal.ofReal D * μ (Metric.ball c r)

/-- Quantitative equivalence of the diameter gauge and a genuine metric.
The metric instance is never installed globally: all balls stay Euclidean. -/
def GaugeComparable (μ : Measure ℂ) (M : MetricSpace ℂ) (A : ℝ) : Prop :=
  0 < A ∧ ∀ x y : ℂ,
    diameterGauge μ x y / A ≤ @dist ℂ M.toDist x y ∧
    @dist ℂ M.toDist x y ≤ A * diameterGauge μ x y

/-- Metric doubling, with all nondegeneracy assumptions and constants visible. -/
def MetricDoublingWith (μ : Measure ℂ) (D A : ℝ) : Prop :=
  PositiveFiniteBalls μ ∧ GlobalDoublingWith μ D ∧
    ∃ M : MetricSpace ℂ, GaugeComparable μ M A

/-- Symmetric formulation of `C⁻¹ μ(B) ≤ ν(B) ≤ C μ(B)`.
Only positive-radius ambient balls are required. -/
def SymmetricBallMassComparison (μ ν : Measure ℂ) (C : ℝ) : Prop :=
  1 ≤ C ∧ ∀ c : ℂ, ∀ r : ℝ, 0 < r →
    μ (Metric.ball c r) ≤ ENNReal.ofReal C * ν (Metric.ball c r) ∧
    ν (Metric.ball c r) ≤ ENNReal.ofReal C * μ (Metric.ball c r)

/-- Usual two-sided measure bounds imply the symmetric ball formulation.
The lower inequality is literally the inverse scalar bound. -/
theorem SymmetricBallMassComparison.of_measureBounds {μ ν : Measure ℂ} {C : ℝ}
    (hC : 1 ≤ C) (hlower : (ENNReal.ofReal C)⁻¹ • μ ≤ ν)
    (hupper : ν ≤ ENNReal.ofReal C • μ) :
    SymmetricBallMassComparison μ ν C := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCne : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 hCpos).ne'
  refine ⟨hC, ?_⟩
  intro c r _
  have hlo := Measure.le_iff'.1 hlower (Metric.ball c r)
  have hup := Measure.le_iff'.1 hupper (Metric.ball c r)
  simp only [Measure.smul_apply, smul_eq_mul] at hlo hup
  refine ⟨?_, hup⟩
  have hm := mul_le_mul_right hlo (ENNReal.ofReal C)
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hCne ENNReal.ofReal_ne_top,
    one_mul] using hm

/-- A real density defines an actual measure by `withDensity`, not a proxy. -/
def weightMeasure (w : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (w z))

/-- Almost-everywhere domination of real densities gives measure domination.
No measurability is silently inferred; `withDensity` monotonicity is valid
without it, and positive finite ball masses are separate hypotheses. -/
theorem withDensity_ofReal_le_smul {α : Type*} [MeasurableSpace α]
    (σ : Measure α) {w v : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ z ∂σ, w z ≤ C * v z) :
    σ.withDensity (fun z => ENNReal.ofReal (w z)) ≤
      ENNReal.ofReal C • σ.withDensity (fun z => ENNReal.ofReal (v z)) := by
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards [h] with z hz
  simpa only [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hC] using
    ENNReal.ofReal_le_ofReal hz

/-- Concrete a.e. real-weight comparison adapter, with no old-route import. -/
theorem weightMeasure_comparison {w v : ℂ → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (h : ∀ᵐ z ∂volume, w z ≤ C * v z ∧ v z ≤ C * w z) :
    SymmetricBallMassComparison (weightMeasure w) (weightMeasure v) C := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have h₁ := withDensity_ofReal_le_smul volume hC0 (h.mono fun _ hz => hz.1)
  have h₂ := withDensity_ofReal_le_smul volume hC0 (h.mono fun _ hz => hz.2)
  refine ⟨hC, ?_⟩
  intro c r _
  constructor
  · simpa only [weightMeasure, Measure.smul_apply, smul_eq_mul] using
      Measure.le_iff'.1 h₁ (Metric.ball c r)
  · simpa only [weightMeasure, Measure.smul_apply, smul_eq_mul] using
      Measure.le_iff'.1 h₂ (Metric.ball c r)

/-- Adapter matching the paper's displayed `C⁻¹ w ≤ v ≤ C w` bounds. -/
theorem weightMeasure_comparison_of_inverse {w v : ℂ → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (h : ∀ᵐ z ∂volume, C⁻¹ * w z ≤ v z ∧ v z ≤ C * w z) :
    SymmetricBallMassComparison (weightMeasure w) (weightMeasure v) C := by
  apply weightMeasure_comparison hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  filter_upwards [h] with z hz
  refine ⟨?_, hz.2⟩
  have hl : w z / C ≤ v z := by simpa [div_eq_mul_inv, mul_comm] using hz.1
  simpa [mul_comm] using (div_le_iff₀ hCpos).1 hl

@[simp] theorem euclideanDiameterBall_self (x : ℂ) :
    euclideanDiameterBall x x = ∅ := by
  simp [euclideanDiameterBall]

@[simp] theorem diameterBallMass_self (μ : Measure ℂ) (x : ℂ) :
    diameterBallMass μ x x = 0 := by
  simp [diameterBallMass]

@[simp] theorem diameterGauge_self (μ : Measure ℂ) (x : ℂ) :
    diameterGauge μ x x = 0 := by
  simp [diameterGauge]

theorem diameterGauge_nonneg (μ : Measure ℂ) (x y : ℂ) :
    0 ≤ diameterGauge μ x y := Real.sqrt_nonneg _

theorem PositiveFiniteBalls.diameterBallMass_ne_top {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (x y : ℂ) : diameterBallMass μ x y ≠ ⊤ := by
  by_cases hxy : x = y
  · subst y; simp
  · exact (hμ ((x + y) / 2) (dist x y / 2)
      (div_pos (dist_pos.mpr hxy) (by norm_num))).2.ne

/-- The diameter gauge is genuinely positive away from the diagonal. -/
theorem PositiveFiniteBalls.diameterGauge_pos {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {x y : ℂ} (hxy : x ≠ y) :
    0 < diameterGauge μ x y := by
  apply Real.sqrt_pos.2
  apply ENNReal.toReal_pos
  · exact (hμ ((x + y) / 2) (dist x y / 2)
      (div_pos (dist_pos.mpr hxy) (by norm_num))).1.ne'
  · exact hμ.diameterBallMass_ne_top x y

theorem SymmetricBallMassComparison.symm {μ ν : Measure ℂ} {C : ℝ}
    (h : SymmetricBallMassComparison μ ν C) : SymmetricBallMassComparison ν μ C :=
  ⟨h.1, fun c r hr => (h.2 c r hr).symm⟩

/-- Finite positive ball masses transfer without any hidden local-finiteness instance. -/
theorem PositiveFiniteBalls.transfer {μ ν : Measure ℂ} {C : ℝ}
    (hμ : PositiveFiniteBalls μ) (h : SymmetricBallMassComparison μ ν C) :
    PositiveFiniteBalls ν := by
  intro c r hr
  have hfin : ENNReal.ofReal C * μ (Metric.ball c r) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμ c r hr).2
  refine ⟨?_, (h.2 c r hr).2.trans_lt hfin⟩
  by_contra hnot
  have hz : ν (Metric.ball c r) = 0 := le_antisymm (le_of_not_gt hnot) bot_le
  have hμzero : μ (Metric.ball c r) ≤ 0 := by simpa [hz] using (h.2 c r hr).1
  exact (not_le_of_gt (hμ c r hr).1) hμzero

/-- Doubling comparison has the explicit constant `C² D`. -/
theorem GlobalDoublingWith.transfer {μ ν : Measure ℂ} {D C : ℝ}
    (hμ : GlobalDoublingWith μ D) (h : SymmetricBallMassComparison μ ν C) :
    GlobalDoublingWith ν (C ^ 2 * D) := by
  have hC : 0 ≤ C := le_trans zero_le_one h.1
  have hD : 0 ≤ D := le_trans zero_le_one hμ.1
  refine ⟨?_, ?_⟩
  · have hC2 : 1 ≤ C ^ 2 := by nlinarith [h.1]
    nlinarith [hμ.1]
  · intro c r hr
    calc
      ν (Metric.ball c (2 * r))
          ≤ ENNReal.ofReal C * μ (Metric.ball c (2 * r)) :=
        (h.2 c (2 * r) (by linarith)).2
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal D * μ (Metric.ball c r)) :=
        mul_le_mul_right (hμ.2 c r hr) _
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal D *
          (ENNReal.ofReal C * ν (Metric.ball c r))) :=
        mul_le_mul_right (mul_le_mul_right (h.2 c r hr).1 _) _
      _ = ENNReal.ofReal (C ^ 2 * D) * ν (Metric.ball c r) := by
        rw [ENNReal.ofReal_mul (sq_nonneg C), ENNReal.ofReal_pow hC]
        ring

/-- Both gauge bounds use the exact square-root loss. The diagonal is handled
using the empty diameter ball, rather than a positive-radius assumption. -/
theorem diameterGauge_comparison {μ ν : Measure ℂ} {C : ℝ}
    (hμ : PositiveFiniteBalls μ) (h : SymmetricBallMassComparison μ ν C)
    (x y : ℂ) :
    diameterGauge μ x y ≤ Real.sqrt C * diameterGauge ν x y ∧
    diameterGauge ν x y ≤ Real.sqrt C * diameterGauge μ x y := by
  have hC : 0 ≤ C := le_trans zero_le_one h.1
  have hν := hμ.transfer h
  by_cases hxy : x = y
  · subst y; simp
  · have hr : 0 < dist x y / 2 := div_pos (dist_pos.mpr hxy) (by norm_num)
    have hm := h.2 ((x + y) / 2) (dist x y / 2) hr
    have hμfin := hμ.diameterBallMass_ne_top x y
    have hνfin := hν.diameterBallMass_ne_top x y
    have hreal₁ : (diameterBallMass μ x y).toReal ≤ C * (diameterBallMass ν x y).toReal := by
      have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνfin) hm.1
      simpa [diameterBallMass, euclideanDiameterBall, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hC] using hb
    have hreal₂ : (diameterBallMass ν x y).toReal ≤ C * (diameterBallMass μ x y).toReal := by
      have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin) hm.2
      simpa [diameterBallMass, euclideanDiameterBall, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hC] using hb
    constructor
    · simpa [diameterGauge, Real.sqrt_mul hC] using Real.sqrt_le_sqrt hreal₁
    · simpa [diameterGauge, Real.sqrt_mul hC] using Real.sqrt_le_sqrt hreal₂

/-- The same metric witness survives the weight comparison. -/
theorem GaugeComparable.transfer {μ ν : Measure ℂ} {M : MetricSpace ℂ} {A C : ℝ}
    (hμ : PositiveFiniteBalls μ) (hg : GaugeComparable μ M A)
    (h : SymmetricBallMassComparison μ ν C) :
    GaugeComparable ν M (Real.sqrt C * A) := by
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one h.1
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  refine ⟨mul_pos hs hg.1, ?_⟩
  intro x y
  have hc := diameterGauge_comparison hμ h x y
  have hm := hg.2 x y
  constructor
  · apply (div_le_iff₀ (mul_pos hs hg.1)).2
    have hold : diameterGauge μ x y ≤ @dist ℂ M.toDist x y * A :=
      (div_le_iff₀ hg.1).1 hm.1
    calc
      diameterGauge ν x y ≤ Real.sqrt C * diameterGauge μ x y := hc.2
      _ ≤ Real.sqrt C * (@dist ℂ M.toDist x y * A) := mul_le_mul_of_nonneg_left hold hs.le
      _ = @dist ℂ M.toDist x y * (Real.sqrt C * A) := by ring
  · calc
      @dist ℂ M.toDist x y ≤ A * diameterGauge μ x y := hm.2
      _ ≤ A * (Real.sqrt C * diameterGauge ν x y) := mul_le_mul_of_nonneg_left hc.1 hg.1.le
      _ = (Real.sqrt C * A) * diameterGauge ν x y := by ring

/-- Main generic comparison theorem: genuine metric doubling is stable under
bounded change of measure, with constants displayed in the conclusion. -/
theorem MetricDoublingWith.transfer {μ ν : Measure ℂ} {D A C : ℝ}
    (hμ : MetricDoublingWith μ D A) (h : SymmetricBallMassComparison μ ν C) :
    MetricDoublingWith ν (C ^ 2 * D) (Real.sqrt C * A) := by
  rcases hμ with ⟨hballs, hd, M, hg⟩
  exact ⟨hballs.transfer h, hd.transfer h, M, hg.transfer hballs h⟩

/-- Direct transfer from the usual lower/upper measure inequalities. -/
theorem MetricDoublingWith.transfer_of_measureBounds {μ ν : Measure ℂ} {D A C : ℝ}
    (hμ : MetricDoublingWith μ D A) (hC : 1 ≤ C)
    (hlower : (ENNReal.ofReal C)⁻¹ • μ ≤ ν)
    (hupper : ν ≤ ENNReal.ofReal C • μ) :
    MetricDoublingWith ν (C ^ 2 * D) (Real.sqrt C * A) :=
  hμ.transfer (SymmetricBallMassComparison.of_measureBounds hC hlower hupper)

/-- Concrete form of the paper's statement that pointwise-comparable weights
change only the quantitative metric-doubling constants. A.e. bounds suffice. -/
theorem MetricDoublingWith.transfer_of_weightComparison {w v : ℂ → ℝ} {D A C : ℝ}
    (hw : MetricDoublingWith (weightMeasure w) D A) (hC : 1 ≤ C)
    (h : ∀ᵐ z ∂volume, C⁻¹ * w z ≤ v z ∧ v z ≤ C * w z) :
    MetricDoublingWith (weightMeasure v) (C ^ 2 * D) (Real.sqrt C * A) :=
  hw.transfer (weightMeasure_comparison_of_inverse hC h)

/-- A homeomorphism induces a genuine metric on the source plane. -/
@[instance_reducible] def pullbackMetric (F : ℂ ≃ₜ ℂ) : MetricSpace ℂ :=
  MetricSpace.induced F F.injective inferInstance

@[simp] theorem pullbackMetric_dist (F : ℂ ≃ₜ ℂ) (x y : ℂ) :
    @dist ℂ (pullbackMetric F).toDist x y = ‖F x - F y‖ := by
  change dist (F x) (F y) = _
  exact dist_eq_norm _ _

end RepulsiveCoulomb.PaperRoute
