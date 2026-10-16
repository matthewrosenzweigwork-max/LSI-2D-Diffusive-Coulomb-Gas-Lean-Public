module

public import LeanResearch.RepulsiveCoulomb.DbarBranchMaximalGraph
public import LeanResearch.RepulsiveCoulomb.CoulombDbarCore

@[expose] public section

/-! The closed maximal weak graph contains the literal complex smooth core,
with precisely the already checked Wirtinger derivative. This is interior
integration by parts, not density in the adjoint graph norm. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombComplexCoreValue_distribution_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombL2Distribution hβ (coulombComplexCoreValue hβ ψ) φ = ∫ z, φ z • ψ z := by
  rw [coulombL2Distribution_apply]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombComplexCoreValue_coe hβ ψ)] with z hz
  rw [hz]

theorem coulombComplexCoreDbar_distribution_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (i : Fin N) :
    coulombL2Distribution hβ
      ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) (coulombComplexCoreDbar hβ ψ)) φ =
        ∫ z, φ z • coulombDbarCoordinate ψ z i := by
  rw [coulombL2Distribution_apply]
  apply integral_congr_ae
  have hcoord := (coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β)
    (coulombComplexCoreDbar hβ ψ)
  filter_upwards [(coulombMeasure_ae_iff hβ).mp hcoord,
    (coulombMeasure_ae_iff hβ).mp (coulombComplexCoreDbar_coe hβ ψ)] with z hz hg
  rw [hz, hg]
  rfl

theorem coulombComplexCore_lineDeriv_pairing {N : ℕ}
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (v : CoulombConfig N) :
    (∫ z, φ z • fderiv ℝ (ψ : CoulombConfig N → ℂ) z v) =
      -(∫ z, (TestFunction.lineDerivCLM ℝ v φ : TestFunction (coulombDomain N) ℝ ⊤) z • ψ z) := by
  have hw := TauCeti.hasWeakFDerivOn_of_differentiableOn (μ := volume) (Ω := coulombDomain N)
    (ψ.continuous.locallyIntegrable.locallyIntegrableOn _)
    ((ψ.contDiff.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _)
    (fun z _ => ψ.contDiff.differentiable (by simp) z)
  have h := (hw v).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hn := congrArg Neg.neg h
  simpa only [neg_neg, TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true] using hn.symm

theorem coulombComplexCore_dbar_pairing {N : ℕ}
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (i : Fin N) :
    (∫ z, φ z • coulombDbarCoordinate ψ z i) + (1 / 2 : ℝ) •
      ((∫ z, (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ :
          TestFunction (coulombDomain N) ℝ ⊤) z • ψ z) +
        Complex.I * (∫ z, (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ :
          TestFunction (coulombDomain N) ℝ ⊤) z • ψ z)) = 0 := by
  let dx : CoulombConfig N → ℂ := fun z => fderiv ℝ (ψ : CoulombConfig N → ℂ) z
    (coulombCoordinateInjection N i 1)
  let dy : CoulombConfig N → ℂ := fun z => fderiv ℝ (ψ : CoulombConfig N → ℂ) z
    (coulombCoordinateInjection N i Complex.I)
  have hxloc : LocallyIntegrableOn dx (coulombDomain N) volume :=
    (((ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable).locallyIntegrableOn _
  have hyloc : LocallyIntegrableOn dy (coulombDomain N) volume :=
    (((ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable).locallyIntegrableOn _
  have hxint : Integrable (fun z => φ z • dx z) := φ.integrable_smul hxloc
  have hyint : Integrable (fun z => φ z • dy z) := φ.integrable_smul hyloc
  have hsplit : (∫ z, φ z • coulombDbarCoordinate ψ z i) =
      (1 / 2 : ℂ) * ((∫ z, φ z • dx z) + Complex.I * (∫ z, φ z • dy z)) := by
    calc
      _ = ∫ z, (1 / 2 : ℂ) * ((φ z • dx z) + Complex.I * (φ z • dy z)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [coulombDbarCoordinate, dx, dy, Complex.real_smul]
          ring
      _ = _ := by
        rw [integral_const_mul, integral_add hxint (hyint.const_mul Complex.I), integral_const_mul]
  rw [hsplit]
  have hx := coulombComplexCore_lineDeriv_pairing ψ φ (coulombCoordinateInjection N i 1)
  have hy := coulombComplexCore_lineDeriv_pairing ψ φ (coulombCoordinateInjection N i Complex.I)
  change (∫ z, φ z • dx z) = _ at hx
  change (∫ z, φ z • dy z) = _ at hy
  rw [hx, hy]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem coulombComplexCore_mem_maxDbarGraph {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    (coulombComplexCoreValue hβ ψ, coulombComplexCoreDbar hβ ψ) ∈ coulombMaxDbarGraph hβ := by
  intro i φ
  rw [coulombWeakDbarConstraintL_apply, coulombComplexCoreDbar_distribution_apply,
    coulombComplexCoreValue_distribution_apply, coulombComplexCoreValue_distribution_apply]
  exact coulombComplexCore_dbar_pairing ψ φ i

def coulombMaxDbarCore {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) : CoulombMaxDbarDomain N hβ :=
  ⟨(coulombComplexCoreValue hβ ψ, coulombComplexCoreDbar hβ ψ), coulombComplexCore_mem_maxDbarGraph hβ ψ⟩

end RepulsiveCoulomb
