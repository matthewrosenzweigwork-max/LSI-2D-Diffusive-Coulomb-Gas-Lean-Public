import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoreL2
import LeanResearch.RepulsiveCoulomb.CoulombGroundStateInverseCore
import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals
import LeanResearch.RepulsiveCoulomb.CoulombSqrtDensityLp
import LeanResearch.RepulsiveCoulomb.PoleBranchRealLpMean

/-! RECORDS-ONLY UNCHECKED DRAFT. Literal norm/mean identities for normalized
core ground states and passage of mean zero across varying temperatures. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombGroundStateCoreLp_norm_sq {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ‖coulombGroundStateCoreLp hβ φ‖ ^ 2 = ∫ z, φ z ^ 2 ∂coulombMeasure N β := by
  rw [← coulombGroundStateL2_core, (coulombGroundStateL2 hβ).norm_map,
    coulombFormValue_norm_sq_eq_integral, coulombFormCore_mass_eq_integral]

theorem coulombGroundStateCoreLp_mean_pairing {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    inner ℝ (coulombGroundStateCoreLp hβ φ) (coulombSqrtDensityLp N β) =
      poleBranchRealMean N hβ (coulombFormValueL N hβ (coulombFormCore hβ φ)) := by
  rw [← coulombGroundStateL2_core, coulombGroundStateL2_mean_pairing,
    poleBranchRealMean_eq_integral]

theorem coulombGroundStateCoreLp_limit_mean_zero {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (γ : ℕ → ℝ) (hγ : ∀ n, 0 < γ n)
    (φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤)
    (ψ : Lp ℝ 2 (volume : Measure (CoulombConfig N)))
    (ht : Tendsto γ atTop (𝓝 β))
    (hv : Tendsto (fun n => coulombGroundStateCoreLp (hγ n) (φ n)) atTop (𝓝 ψ))
    (hm : Tendsto (fun n => poleBranchRealMean N (hγ n)
      (coulombFormValueL N (hγ n) (coulombFormCore (hγ n) (φ n)))) atTop (𝓝 0)) :
    inner ℝ ψ (coulombSqrtDensityLp N β) = 0 := by
  have hroot := (coulombSqrtDensityLp_continuousAt (N := N) hβ).tendsto.comp ht
  have hp := hv.inner (𝕜 := ℝ) hroot
  have hzero : Tendsto (fun n => inner ℝ (coulombGroundStateCoreLp (hγ n) (φ n))
      (coulombSqrtDensityLp N (γ n))) atTop (𝓝 0) := by
    simpa only [coulombGroundStateCoreLp_mean_pairing] using hm
  exact tendsto_nhds_unique hp hzero

theorem coulombGroundStateCoreLp_inverse_temperature {N : ℕ} {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombGroundStateCoreLp hβ
      (coulombInverseGroundStateCore hβ (coulombGroundStateCore hγ φ)) =
      coulombGroundStateCoreLp hγ φ := by
  apply Lp.ext
  filter_upwards [coulombGroundStateCoreLp_coe hβ
    (coulombInverseGroundStateCore hβ (coulombGroundStateCore hγ φ)),
    coulombGroundStateCoreLp_coe hγ φ] with z h1 h2
  rw [h1, h2, coulombGroundState_inverse_core]

end RepulsiveCoulomb
