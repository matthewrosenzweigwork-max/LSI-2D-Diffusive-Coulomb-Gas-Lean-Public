module

public import LeanResearch.RepulsiveCoulomb.CoulombClosedForm
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Antilipschitz

@[expose] public section

/-! Original-core approximation and the closed full physical-gradient graph.
The product topology is used only for closedness; form energy is Euclidean. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def coulombFormCore {N : ℕ} {β : ℝ} (hβ : 0 < β) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    CoulombFormDomain N hβ :=
  ⟨coulombCoreJet hβ φ, by
    change coulombCoreJet hβ φ ∈ (coulombFormSubmodule N hβ : Set _)
    rw [coe_coulombFormSubmodule]
    exact subset_closure ⟨φ, rfl⟩⟩

theorem coulombFormCore_value {N : ℕ} {β : ℝ} (hβ : 0 < β) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormValueL N hβ (coulombFormCore hβ φ) =ᵐ[coulombMeasure N β] φ := coulombCoreJet_value hβ φ

theorem coulombFormCore_gradient {N : ℕ} {β : ℝ} (hβ : 0 < β) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormGradientL N hβ (coulombFormCore hβ φ) =ᵐ[coulombMeasure N β]
      fun z => gradient (φ : CoulombConfig N → ℝ) z := coulombCoreJet_gradient hβ φ

theorem coulombFormCore_approximation (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ∃ φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤,
      Tendsto (fun n => coulombFormCore hβ (φ n)) atTop (𝓝 u) := by
  classical
  have hu : (u : CoulombJetL2 N β) ∈ closure (range (coulombCoreJet (N := N) hβ)) := by
    change (u : CoulombJetL2 N β) ∈ coulombCoreGraph N hβ
    rw [← coe_coulombFormSubmodule]
    exact u.property
  obtain ⟨J, hJ, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using hJ
  refine ⟨φ, ?_⟩
  apply tendsto_subtype_rng.mpr
  simpa only [coulombFormCore, hφ] using hlim

theorem coulombFormCore_approximation_components (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ∃ φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤,
      Tendsto (fun n => coulombFormValueL N hβ (coulombFormCore hβ (φ n))) atTop (𝓝 (coulombFormValueL N hβ u)) ∧
      Tendsto (fun n => coulombFormGradientL N hβ (coulombFormCore hβ (φ n))) atTop (𝓝 (coulombFormGradientL N hβ u)) := by
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation N hβ u
  exact ⟨φ, ((coulombFormValueL N hβ).continuous.tendsto u).comp hφ,
    ((coulombFormGradientL N hβ).continuous.tendsto u).comp hφ⟩

def coulombFormGraphL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] (Lp ℝ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β)) :=
  (coulombFormValueL N hβ).prod (coulombFormGradientL N hβ)

theorem coulombForm_norm_le_graph (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ‖u‖ ≤ 2 * ‖coulombFormGraphL N hβ u‖ := by
  have hv : ‖coulombFormValueL N hβ u‖ ≤ ‖coulombFormGraphL N hβ u‖ := norm_fst_le (coulombFormGraphL N hβ u)
  have hg : ‖coulombFormGradientL N hβ u‖ ≤ ‖coulombFormGraphL N hβ u‖ := norm_snd_le (coulombFormGraphL N hβ u)
  have h := coulombForm_norm_sq N hβ u
  unfold coulombFormEnergy at h
  nlinarith [norm_nonneg u, norm_nonneg (coulombFormGraphL N hβ u),
    norm_nonneg (coulombFormValueL N hβ u), norm_nonneg (coulombFormGradientL N hβ u)]

theorem coulombFormGraphL_antilipschitz (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    AntilipschitzWith 2 (coulombFormGraphL N hβ) := by
  apply antilipschitzWith_iff_le_mul_dist.mpr
  intro u v
  simpa only [dist_eq_norm, map_sub, NNReal.coe_ofNat] using coulombForm_norm_le_graph N hβ (u - v)

theorem coulombFormGraphL_closed_range (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsClosed (range (coulombFormGraphL N hβ)) :=
  (coulombFormGraphL_antilipschitz N hβ).isClosed_range (coulombFormGraphL N hβ).uniformContinuous

theorem coulombGradient_closable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤) (g : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hv : Tendsto (fun n => coulombFormValueL N hβ (coulombFormCore hβ (φ n))) atTop (𝓝 0))
    (hg : Tendsto (fun n => coulombFormGradientL N hβ (coulombFormCore hβ (φ n))) atTop (𝓝 g)) : g = 0 := by
  have hlim : Tendsto (fun n => coulombFormGraphL N hβ (coulombFormCore hβ (φ n))) atTop (𝓝 (0, g)) :=
    hv.prodMk_nhds hg
  have hmem := (coulombFormGraphL_closed_range N hβ).mem_of_tendsto hlim
    (Eventually.of_forall (fun n => mem_range_self (coulombFormCore hβ (φ n))))
  obtain ⟨u, hu⟩ := hmem
  have hvu : coulombFormValueL N hβ u = 0 := congrArg Prod.fst hu
  have hgu : coulombFormGradientL N hβ u = g := congrArg Prod.snd hu
  have hu0 := (coulombFormValueL_eq_zero_iff N hβ u).mp hvu
  simpa only [hu0, map_zero] using hgu.symm

end RepulsiveCoulomb
