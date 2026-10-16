import LeanResearch.RepulsiveCoulomb.DbarBranchCutoffAdjointError
import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreIBP

/-! Literal product identities for the auxiliary core and a proper real
cutoff. These identify the exact scalar error used in the genuine adjoint
product rule, before any joint graph approximation argument. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombMetricCutoffCore {N : ℕ} {R : ℝ} (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombComplexCoreMulLocal (fun z => (coulombMetricCutoff R z : ℂ))
    (fun z _ => Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (coulombMetricCutoff_contDiff hR).contDiffAt) φ

theorem coulombMetricCutoffCore_value {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexCoreValue hβ (coulombMetricCutoffCore hR φ) =
      coulombMetricCutoffL2L hR ℂ (coulombComplexCoreValue hβ φ) := by
  apply Lp.ext
  filter_upwards [coulombComplexCoreValue_coe hβ (coulombMetricCutoffCore hR φ),
    coulombMetricCutoffL2L_coe hR (coulombComplexCoreValue hβ φ), coulombComplexCoreValue_coe hβ φ]
    with z hp hθ hφ
  rw [hp, hθ, hφ]
  rfl

theorem coulombMetricCutoffCore_dbar {N : ℕ} {R : ℝ} (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombDbar (coulombMetricCutoffCore hR φ) z =
      (coulombMetricCutoff R z : ℂ) • coulombDbar φ z +
        φ z • coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z := by
  ext i
  rw [coulombDbar_apply]
  change coulombDbarCoordinate (fun x => (coulombMetricCutoff R x : ℂ) * φ x) z i = _
  have hθ : DifferentiableAt ℝ (fun x : CoulombConfig N => (coulombMetricCutoff R x : ℂ)) z := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.differentiableAt.comp z
        ((coulombMetricCutoff_contDiff hR).differentiable (by simp) z))
  rw [coulombDbarCoordinate_mul hθ (φ.contDiff.differentiable (by simp) z)]
  rfl

def coulombAuxiliaryCutoffErrorCore {N : ℕ} {R : ℝ} (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombComplexCoreMulLocal φ (fun z _ => φ.contDiff.contDiffAt) (coulombMetricCutoffSymbolCore hR i)

theorem coulombAuxiliaryCutoffErrorCore_vector {N : ℕ} {R : ℝ} (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    dbarCoreVector (coulombAuxiliaryCutoffErrorCore hR φ) z =
      φ z • dbarCoreVector (coulombMetricCutoffSymbolCore hR) z := by
  ext i
  rfl

theorem coulombAuxiliaryCutoffCore_product {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombAuxiliaryCoreDerivativeL N hβ (coulombMetricCutoffCore hR φ) =
      coulombMetricCutoffL2L hR (CoulombConfig N) (coulombAuxiliaryCoreDerivativeL N hβ φ) +
        coulombComplexVectorCoreValue hβ (coulombAuxiliaryCutoffErrorCore hR φ) := by
  have haux (ψ : TestFunction (coulombDomain N) ℂ ⊤) :
      coulombAuxiliaryCoreDerivativeL N hβ ψ =ᵐ[coulombMeasure N β]
        fun z => dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (coulombDbar ψ z) := by
    change coulombInverseRootL2L N β (coulombComplexDbarCoreLinear N hβ ψ) =ᵐ[_] _
    rw [coulombComplexDbarCoreLinear_apply]
    filter_upwards [coulombInverseRootL2_coe β (coulombComplexCoreDbar hβ ψ),
      coulombComplexCoreDbar_coe hβ ψ] with z hR hψ
    change coulombInverseRootL2 β (coulombComplexCoreDbar hβ ψ) z = _
    rw [hR, hψ]
  apply Lp.ext
  filter_upwards [haux (coulombMetricCutoffCore hR φ), haux φ,
    coulombMetricCutoffL2L_coe hR (coulombAuxiliaryCoreDerivativeL N hβ φ),
    coulombComplexVectorCoreValue_coe hβ (coulombAuxiliaryCutoffErrorCore hR φ),
    Lp.coeFn_add
      (coulombMetricCutoffL2L hR (CoulombConfig N) (coulombAuxiliaryCoreDerivativeL N hβ φ))
      (coulombComplexVectorCoreValue hβ (coulombAuxiliaryCutoffErrorCore hR φ))]
    with z hl hφ hθ he hsum
  rw [hl, hsum, Pi.add_apply, hθ, hφ, he, coulombAuxiliaryCutoffErrorCore_vector,
    coulombMetricCutoffSymbolCore_vector, coulombMetricCutoffCore_dbar, map_add, map_smul, map_smul]
  rfl

theorem coulombMetricCutoffL2L_inner {N : ℕ} {β R : ℝ} (hR : 0 < R)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (f g : Lp F 2 (coulombMeasure N β)) :
    inner ℂ f (coulombMetricCutoffL2L hR F g) = inner ℂ (coulombMetricCutoffL2L hR F f) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombMetricCutoffL2L_coe hR f, coulombMetricCutoffL2L_coe hR g] with z hf hg
  rw [hf, hg, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

theorem coulombAuxiliaryCutoffErrorCore_inner {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (φ : TestFunction (coulombDomain N) ℂ ⊤)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    inner ℂ (coulombComplexVectorCoreValue hβ (coulombAuxiliaryCutoffErrorCore hR φ)) u =
      inner ℂ (coulombComplexCoreValue hβ φ) (coulombCutoffAdjointErrorL β hR u) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombComplexVectorCoreValue_coe hβ (coulombAuxiliaryCutoffErrorCore hR φ),
    coulombComplexCoreValue_coe hβ φ, coulombCutoffAdjointErrorL_coe β hR u] with z he hφ hZ
  rw [he, hφ, hZ, coulombAuxiliaryCutoffErrorCore_vector, inner_smul_left, RCLike.inner_apply']

end RepulsiveCoulomb
