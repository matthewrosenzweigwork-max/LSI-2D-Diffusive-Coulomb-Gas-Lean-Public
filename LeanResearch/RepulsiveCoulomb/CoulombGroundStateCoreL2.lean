import LeanResearch.RepulsiveCoulomb.CoulombGroundStateL2
import LeanResearch.RepulsiveCoulomb.CoulombFormApproximation

/-! Identification of the actual original-core ground state with the global
volume-L2 image of its Gibbs-L2 class. No measure-dependent cast is used. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

def coulombGroundStateCoreLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : Lp ℝ 2 (volume : Measure (CoulombConfig N)) :=
  ((coulombGroundStateCore hβ φ).continuous.memLp_of_hasCompactSupport
    (coulombGroundStateCore hβ φ).hasCompactSupport).toLp (coulombGroundStateCore hβ φ)

theorem coulombGroundStateCoreLp_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombGroundStateCoreLp hβ φ =ᵐ[volume] (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) :=
  MemLp.coeFn_toLp _

theorem coulombGroundStateL2_core {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombGroundStateL2 hβ (coulombFormValueL N hβ (coulombFormCore hβ φ)) =
      coulombGroundStateCoreLp hβ φ := by
  apply Lp.ext
  filter_upwards [coulombGroundStateL2_coe hβ (coulombFormValueL N hβ (coulombFormCore hβ φ)),
    (coulombMeasure_ae_iff hβ).mp (coulombFormCore_value hβ φ),
    coulombGroundStateCoreLp_coe hβ φ] with z hg hv hc
  rw [hg, hv, hc, coulombGroundStateCore_apply]
  exact mul_comm _ _

end RepulsiveCoulomb
