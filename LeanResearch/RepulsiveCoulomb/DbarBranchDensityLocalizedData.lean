import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryAdjointDensity
import LeanResearch.RepulsiveCoulomb.DbarBranchCompactLocalMultiplier
import LeanResearch.RepulsiveCoulomb.DbarBranchCutoffDataSupport

/-! The actual density-scaled compact data used by the local combined weak
system. Every input component and scalar output is proved in Lebesgue L2;
the inverse density appears only in locally smooth coefficients on Omega. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators LinearPMap
namespace RepulsiveCoulomb

theorem coulombComplexDensity_contDiffAt {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (coulombDensity N β x : ℂ)) z :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z ((coulombDensity_contDiffAt β hz).of_le le_top)

def coulombDensityRootMatrix {N : ℕ} (β : ℝ) (z : CoulombConfig N) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => coulombRootMatrix z i j / (coulombDensity N β z : ℂ)

theorem coulombDensityRootMatrix_entry_contDiffAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i j : Fin N) {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => coulombDensityRootMatrix β x i j) z := by
  change ContDiffAt ℝ (⊤ : ℕ∞)
    ((fun x : CoulombConfig N => coulombRootMatrix x i j) /
      (fun x : CoulombConfig N => (coulombDensity N β x : ℂ))) z
  have hd : (coulombDensity N β z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
  simpa only [div_eq_mul_inv] using!
    (coulombRootMatrix_entry_contDiffAt i j hz).mul
      ((coulombComplexDensity_contDiffAt β hz).inv hd)

theorem coulombDensityRootMatrix_density_action {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) (v : CoulombConfig N) (i : Fin N) :
    (∑ j, coulombDensityRootMatrix β z i j * ((coulombDensity N β z : ℂ) * v j)) =
      (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) v) i := by
  have hd : (coulombDensity N β z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
  rw [dbarCLMMatrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  change (coulombRootMatrix z i j / (coulombDensity N β z : ℂ)) *
    ((coulombDensity N β z : ℂ) * v j) = coulombRootMatrix z i j * v j
  field_simp [hd]

theorem coulombAuxiliaryAdjoint_density_flux_weak {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, φ z • ((coulombDensity N β z : ℂ) * h z)) =
      ∑ j, ∫ z, coulombDCoordinate (fun x => (φ x : ℂ)) z j *
        (dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
          ((coulombDensity N β z : ℂ) • u z)) j := by
  rw [coulombAuxiliaryDbarAdjoint_density_weak hβ huh φ]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [map_smul]
    rfl

theorem coulombCutoffDensityInput_memLp_volume {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (i : Fin N) :
    MemLp (fun z => (coulombDensity N β z : ℂ) *
      (coulombMetricCutoffL2L hR (CoulombConfig N) u z) i) 2 volume := by
  apply coulombCompactLocalCoefficient_memLp_volume
    (coulombMetricCutoffSupport_isCompact N hR) (coulombMetricCutoffSupport_subset N hR)
    (fun z => (coulombDensity N β z : ℂ)) (fun z hz => coulombComplexDensity_contDiffAt β hz)
  · exact ((coulombCutoffData_memLp_volume hβ hR u 0).1).eval_piLp i
  · filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombMetricCutoffL2L_supported hR u)] with z hz
    intro hK
    rw [hz hK]
    rfl

theorem coulombCutoffDensityOutput_memLp_volume {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    MemLp (fun z => (coulombDensity N β z : ℂ) *
      (coulombMetricCutoffL2L hR ℂ h - coulombCutoffAdjointErrorL β hR u) z) 2 volume := by
  apply coulombCompactLocalCoefficient_memLp_volume
    (coulombMetricCutoffSupport_isCompact N hR) (coulombMetricCutoffSupport_subset N hR)
    (fun z => (coulombDensity N β z : ℂ)) (fun z hz => coulombComplexDensity_contDiffAt β hz)
  · exact coulombCompactL2_memLp_volume hβ
      (coulombMetricCutoffSupport_isCompact N hR) (coulombMetricCutoffSupport_subset N hR)
      _ (coulombCutoffAdjointOutput_supported hR u h)
  · exact (coulombMeasure_ae_iff hβ).mp (coulombCutoffAdjointOutput_supported hR u h)

end RepulsiveCoulomb
