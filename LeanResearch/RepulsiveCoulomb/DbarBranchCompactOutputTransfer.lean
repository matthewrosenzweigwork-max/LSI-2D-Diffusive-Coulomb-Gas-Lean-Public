module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactCoreTransfer
public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCompactData

@[expose] public section

/-! The local output classes return to the genuine scalar adjoint cutoff
and exterior error classes. The finite-coordinate maps are literal L2
projections, preserving the fixed Euclidean-fiber norms. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombAuxiliaryCutoffJointValue {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    CoulombAuxiliaryJointIndex N → Lp ℂ 2 (coulombMeasure N β)
  | none => coulombAuxiliaryCutoffScalar hR u h
  | some p => (EuclideanSpace.proj (𝕜 := ℂ) p).compLpL 2 (coulombMeasure N β)
      (coulombCutoffExteriorError β hR u)

theorem coulombAuxiliaryCutoffJointValue_coe {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    (coulombAuxiliaryCutoffJointValue hR u h q : CoulombConfig N → ℂ) =ᵐ[volume]
      coulombAuxiliaryCutoffJointOutput hR u h q := by
  cases q with
  | none => exact ae_eq_rfl
  | some p =>
      exact (coulombMeasure_ae_iff hβ).mp
        ((EuclideanSpace.proj (𝕜 := ℂ) p).coeFn_compLpL (p := 2) (μ := coulombMeasure N β)
          (coulombCutoffExteriorError β hR u))

theorem coulombCompactOutput_volume_transfer {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {L : Set (CoulombConfig N)} (hL : IsCompact L) (hLΩ : L ⊆ coulombDomain N)
    (hKL : coulombMetricCutoffSupport N R ⊆ L)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    dbarVolumeToCoulombCompactL hβ hL hLΩ ℂ (coulombAuxiliaryCompactOutputVolume hβ hR u h q) =
      coulombAuxiliaryCutoffJointValue hR u h q := by
  apply dbarVolumeToCoulombCompactL_eq_of_supported hβ hL hLΩ
  · exact ((coulombAuxiliaryCompactOutputVolume_coe hβ hR u h q).trans
      (dbarIndicator_eq_of_ae_supported (coulombAuxiliaryCutoffJointOutput_supported hβ hR u h q))).trans
        (coulombAuxiliaryCutoffJointValue_coe hβ hR u h q).symm
  · filter_upwards [coulombAuxiliaryCompactOutputVolume_supported hβ hR u h q] with z hz
    exact fun hzL => hz (fun hzK => hzL (hKL hzK))

theorem coulombComplexVectorCoreValue_coordinate {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (b : Fin N) :
    (EuclideanSpace.proj (𝕜 := ℂ) b).compLpL 2 (coulombMeasure N β)
      (coulombComplexVectorCoreValue hβ ψ) = coulombComplexCoreValue hβ (ψ b) := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) b).coeFn_compLpL (p := 2) (μ := coulombMeasure N β)
    (coulombComplexVectorCoreValue hβ ψ), coulombComplexVectorCoreValue_coe hβ ψ,
    coulombComplexCoreValue_coe hβ (ψ b)] with z hp hψ hb
  rw [hp, hψ, hb]
  rfl

end RepulsiveCoulomb
