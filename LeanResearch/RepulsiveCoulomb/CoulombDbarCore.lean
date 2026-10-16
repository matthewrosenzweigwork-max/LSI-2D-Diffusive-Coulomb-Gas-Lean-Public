module

public import LeanResearch.RepulsiveCoulomb.CoulombWirtinger
public import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-! Actual compact smooth dbar core and weighted L2 realizations. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

def coulombDbarCoreCoordinateL (N : ℕ) (i : Fin N) :
    TestFunction (coulombDomain N) ℂ ⊤ →L[ℂ] TestFunction (coulombDomain N) ℂ ⊤ :=
  let dx : TestFunction (coulombDomain N) ℂ ⊤ →L[ℂ] TestFunction (coulombDomain N) ℂ ⊤ :=
    TestFunction.lineDerivCLM ℂ (coulombCoordinateInjection N i 1)
  let dy : TestFunction (coulombDomain N) ℂ ⊤ →L[ℂ] TestFunction (coulombDomain N) ℂ ⊤ :=
    TestFunction.lineDerivCLM ℂ (coulombCoordinateInjection N i Complex.I)
  (TestFunction.postcompCLM ((1 / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ)).comp
    (dx + (TestFunction.postcompCLM (Complex.I • ContinuousLinearMap.id ℂ ℂ)).comp dy)

theorem coulombDbarCoreCoordinateL_apply (N : ℕ) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombDbarCoreCoordinateL N i φ z = coulombDbarCoordinate φ z i := by
  change (1 / 2 : ℂ) * ((TestFunction.lineDerivCLM ℂ (coulombCoordinateInjection N i 1) φ :
      TestFunction (coulombDomain N) ℂ ⊤) z + Complex.I *
      (TestFunction.lineDerivCLM ℂ (coulombCoordinateInjection N i Complex.I) φ :
        TestFunction (coulombDomain N) ℂ ⊤) z) = _
  simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true]
  rw [(φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv]
  unfold coulombDbarCoordinate
  ring

theorem coulombComplexCore_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : MemLp (φ : CoulombConfig N → ℂ) 2 (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

theorem coulombDbarCore_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : MemLp (coulombDbar φ) 2 (coulombMeasure N β) := by
  apply memLp_piLp_iff.mpr
  intro i
  have h := coulombComplexCore_memLp hβ (coulombDbarCoreCoordinateL N i φ)
  change MemLp (fun z => coulombDbarCoreCoordinateL N i φ z) 2 (coulombMeasure N β) at h
  simpa only [coulombDbarCoreCoordinateL_apply, coulombDbar_apply] using h

def coulombComplexCoreValue {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : Lp ℂ 2 (coulombMeasure N β) :=
  (coulombComplexCore_memLp hβ φ).toLp φ

def coulombComplexCoreDbar {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombDbarCore_memLp hβ φ).toLp (coulombDbar φ)

theorem coulombComplexCoreValue_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexCoreValue hβ φ =ᵐ[coulombMeasure N β] φ :=
  (coulombComplexCore_memLp hβ φ).coeFn_toLp

theorem coulombComplexCoreDbar_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexCoreDbar hβ φ =ᵐ[coulombMeasure N β] coulombDbar φ :=
  (coulombDbarCore_memLp hβ φ).coeFn_toLp

theorem coulombDbar_real_core_energy {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, ‖coulombDbar (fun x => (φ x : ℂ)) z‖ ^ 2 ∂coulombMeasure N β) =
      (1 / 4 : ℝ) * coulombFormEnergy N hβ (coulombFormCore hβ φ) := by
  rw [coulombFormCore_energy_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => coulombDbar_real_norm_sq (φ.contDiff.differentiable (by simp) z)

end RepulsiveCoulomb
