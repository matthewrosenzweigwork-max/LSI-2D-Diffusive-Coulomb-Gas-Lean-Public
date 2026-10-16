import LeanResearch.RepulsiveCoulomb.PointWeightClosedForm
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! Approximation and the closed physical-gradient graph. The ordinary
product L2 topology below is used only to express closedness; the form norm
and the energy remain the Euclidean graph norm and the squared physical
gradient from PointWeightClosedForm.
-/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def pointFormCore {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) : PointFormDomain hγ ha y :=
  ⟨pointCoreJet hγ ha y φ, by
    change pointCoreJet hγ ha y φ ∈ (pointFormSubmodule hγ ha y : Set _)
    rw [coe_pointFormSubmodule]
    exact subset_closure ⟨φ, rfl⟩⟩

theorem pointFormCore_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointFormValueL hγ ha y (pointFormCore hγ ha y φ) =ᵐ[pointMeasure γ a y] φ :=
  pointCoreJet_value hγ ha y φ

theorem pointFormCore_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointFormGradientL hγ ha y (pointFormCore hγ ha y φ) =ᵐ[pointMeasure γ a y]
      (fun z ↦ gradient (φ : ℂ → ℝ) z) :=
  pointCoreJet_gradient hγ ha y φ

/-- Every closed-domain element has smooth puncture-avoiding approximants
in the actual Hilbert form norm, not only convergence of their values. -/
theorem pointFormCore_approximation {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    ∃ φ : ℕ → TestFunction (pointDomain a y) ℝ ⊤,
      Tendsto (fun n ↦ pointFormCore hγ ha y (φ n)) atTop (𝓝 u) := by
  classical
  have hu : (u : PointJetL2 γ a y) ∈ closure (range (pointCoreJet hγ ha y)) := by
    change (u : PointJetL2 γ a y) ∈ pointCoreGraph hγ ha y
    rw [← coe_pointFormSubmodule]
    exact u.property
  obtain ⟨J, hJ, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using hJ
  refine ⟨φ, ?_⟩
  apply tendsto_subtype_rng.mpr
  simpa only [pointFormCore, hφ] using hlim

/-- Convergence in the form norm gives the two required physical L2 limits. -/
theorem pointFormCore_approximation_components {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    ∃ φ : ℕ → TestFunction (pointDomain a y) ℝ ⊤,
      Tendsto (fun n ↦ pointFormValueL hγ ha y (pointFormCore hγ ha y (φ n))) atTop
        (𝓝 (pointFormValueL hγ ha y u)) ∧
      Tendsto (fun n ↦ pointFormGradientL hγ ha y (pointFormCore hγ ha y (φ n))) atTop
        (𝓝 (pointFormGradientL hγ ha y u)) := by
  obtain ⟨φ, hφ⟩ := pointFormCore_approximation hγ ha y u
  exact ⟨φ, ((pointFormValueL hγ ha y).continuous.tendsto u).comp hφ,
    ((pointFormGradientL hγ ha y).continuous.tendsto u).comp hφ⟩

def pointFormGraphL {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    PointFormDomain hγ ha y →L[ℝ]
      (Lp ℝ 2 (pointMeasure γ a y) × Lp ℂ 2 (pointMeasure γ a y)) :=
  (pointFormValueL hγ ha y).prod (pointFormGradientL hγ ha y)

theorem pointForm_norm_le_graph {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) : ‖u‖ ≤ 2 * ‖pointFormGraphL hγ ha y u‖ := by
  have hv : ‖pointFormValueL hγ ha y u‖ ≤ ‖pointFormGraphL hγ ha y u‖ :=
    norm_fst_le (pointFormGraphL hγ ha y u)
  have hg : ‖pointFormGradientL hγ ha y u‖ ≤ ‖pointFormGraphL hγ ha y u‖ :=
    norm_snd_le (pointFormGraphL hγ ha y u)
  have h := pointForm_norm_sq hγ ha y u
  unfold pointFormEnergy at h
  nlinarith [norm_nonneg u, norm_nonneg (pointFormGraphL hγ ha y u),
    norm_nonneg (pointFormValueL hγ ha y u), norm_nonneg (pointFormGradientL hγ ha y u)]

theorem pointFormGraphL_antilipschitz {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    AntilipschitzWith 2 (pointFormGraphL hγ ha y) := by
  apply antilipschitzWith_iff_le_mul_dist.mpr
  intro u v
  simpa only [dist_eq_norm, map_sub, NNReal.coe_ofNat] using
    pointForm_norm_le_graph hγ ha y (u - v)

/-- The physical-gradient graph is closed in the product of the actual
weighted L2 spaces, including for general unbounded form-domain elements. -/
theorem pointFormGraphL_closed_range {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    IsClosed (range (pointFormGraphL hγ ha y)) :=
  (pointFormGraphL_antilipschitz hγ ha y).isClosed_range
    (pointFormGraphL hγ ha y).uniformContinuous

/-- Sequential closability: no nonzero limiting physical gradient can be
produced by core functions whose values converge to zero. -/
theorem pointGradient_closable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : ℕ → TestFunction (pointDomain a y) ℝ ⊤)
    (g : Lp ℂ 2 (pointMeasure γ a y))
    (hv : Tendsto (fun n ↦ pointFormValueL hγ ha y (pointFormCore hγ ha y (φ n)))
      atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ pointFormGradientL hγ ha y (pointFormCore hγ ha y (φ n)))
      atTop (𝓝 g)) : g = 0 := by
  have hlim : Tendsto (fun n ↦ pointFormGraphL hγ ha y (pointFormCore hγ ha y (φ n)))
      atTop (𝓝 (0, g)) := hv.prodMk_nhds hg
  have hmem := (pointFormGraphL_closed_range hγ ha y).mem_of_tendsto hlim
    (Eventually.of_forall (fun n ↦ mem_range_self (pointFormCore hγ ha y (φ n))))
  obtain ⟨u, hu⟩ := hmem
  have hvu : pointFormValueL hγ ha y u = 0 := congrArg Prod.fst hu
  have hgu : pointFormGradientL hγ ha y u = g := congrArg Prod.snd hu
  have hu0 := (pointFormValueL_eq_zero_iff hγ ha y u).mp hvu
  simpa only [hu0, map_zero] using hgu.symm

end RepulsiveCoulomb
