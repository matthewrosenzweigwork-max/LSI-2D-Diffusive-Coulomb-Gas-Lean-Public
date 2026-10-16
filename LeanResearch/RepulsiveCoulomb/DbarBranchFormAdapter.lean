module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCoreCompatibility
public import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelProjection
public import LeanResearch.RepulsiveCoulomb.CoulombFormApproximation

@[expose] public section

/-! The actual full physical form embeds in the maximal weak dbar graph.
Closedness and original-core approximation extend the literal one-half
Wirtinger identity to every form-domain observable, with energy factor one-quarter. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombFormComplexValueL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] Lp ℂ 2 (coulombMeasure N β) :=
  (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β)).comp (coulombFormValueL N hβ)

def coulombFormDbarL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (1 / 2 : ℂ) • coulombFormGradientL N hβ

def coulombFormDbarGraphL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] CoulombDbarL2Pair N β :=
  (coulombFormComplexValueL N hβ).prod (coulombFormDbarL N hβ)

theorem coulombFormComplexValueL_coe {N : ℕ} {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    coulombFormComplexValueL N hβ u =ᵐ[coulombMeasure N β]
      fun z => (coulombFormValueL N hβ u z : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL (coulombFormValueL N hβ u)

theorem coulombFormDbarGraphL_core {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormDbarGraphL N hβ (coulombFormCore hβ φ) ∈ coulombMaxDbarGraph hβ := by
  let ψ : TestFunction (coulombDomain N) ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
  have hv : coulombFormComplexValueL N hβ (coulombFormCore hβ φ) = coulombComplexCoreValue hβ ψ := by
    apply Lp.ext
    filter_upwards [coulombFormComplexValueL_coe hβ (coulombFormCore hβ φ),
      coulombFormCore_value hβ φ, coulombComplexCoreValue_coe hβ ψ] with z hvc hφ hψ
    rw [hvc, hφ, hψ]
    rfl
  have hg : coulombFormDbarL N hβ (coulombFormCore hβ φ) = coulombComplexCoreDbar hβ ψ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (coulombFormGradientL N hβ (coulombFormCore hβ φ)),
      coulombFormCore_gradient hβ φ, coulombComplexCoreDbar_coe hβ ψ] with z hsm hφ hψ
    change ((1 / 2 : ℂ) • coulombFormGradientL N hβ (coulombFormCore hβ φ)) z = _
    rw [hsm, Pi.smul_apply, hφ, hψ]
    have he : (ψ : CoulombConfig N → ℂ) = fun x => (φ x : ℂ) := rfl
    rw [he, coulombDbar_real (φ.contDiff.differentiable (by simp) z)]
  change (coulombFormComplexValueL N hβ (coulombFormCore hβ φ),
    coulombFormDbarL N hβ (coulombFormCore hβ φ)) ∈ _
  rw [hv, hg]
  exact coulombComplexCore_mem_maxDbarGraph hβ ψ

theorem coulombForm_mem_maxDbarGraph {N : ℕ} {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    (coulombFormComplexValueL N hβ u, coulombFormDbarL N hβ u) ∈ coulombMaxDbarGraph hβ := by
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation N hβ u
  have hlim := ((coulombFormDbarGraphL N hβ).continuous.tendsto u).comp hφ
  exact (coulombMaxDbarGraph_isClosed hβ).mem_of_tendsto hlim
    (Eventually.of_forall fun n => coulombFormDbarGraphL_core hβ (φ n))

theorem coulombFormDbarL_norm_sq {N : ℕ} {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ‖coulombFormDbarL N hβ u‖ ^ 2 = (1 / 4 : ℝ) * coulombFormEnergy N hβ u := by
  change ‖(1 / 2 : ℂ) • coulombFormGradientL N hβ u‖ ^ 2 = _
  rw [norm_smul, mul_pow]
  norm_num [coulombFormEnergy]

theorem coulombForm_zero_gradient_mem_weakKernel {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (hu : coulombFormGradientL N hβ u = 0) :
    coulombFormComplexValueL N hβ u ∈ coulombDbarWeakKernel N hβ := by
  rw [coulombDbarWeakKernel_mem_iff]
  have h := coulombForm_mem_maxDbarGraph hβ u
  simpa only [coulombFormDbarL, ContinuousLinearMap.smul_apply, hu, smul_zero] using h

end RepulsiveCoulomb
