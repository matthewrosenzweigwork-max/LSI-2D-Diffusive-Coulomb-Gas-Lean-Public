import LeanResearch.RepulsiveCoulomb.DbarBranchExtendedCoreOutput
import LeanResearch.RepulsiveCoulomb.DbarBranchCompactDensityReturn
import LeanResearch.RepulsiveCoulomb.DbarBranchCompactOutputTransfer
import LeanResearch.RepulsiveCoulomb.DbarBranchFiniteL2Convergence

/-! One genuine compact-core sequence approximates a fixed cutoff value,
its actual Hilbert-adjoint output and its transformed exterior error in
the original Gibbs norms. All local equations, margins, representative
changes and coefficient extensions are supplied by the preceding proofs. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped Topology Pointwise LinearPMap
namespace RepulsiveCoulomb

theorem coulombAuxiliaryCutoff_joint_core_approximation {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    ∃ ψ : ℕ → Fin N → TestFunction (coulombDomain N) ℂ ⊤,
      Tendsto (fun n => coulombComplexVectorCoreValue hβ (ψ n)) atTop
        (𝓝 (coulombMetricCutoffL2L hR (CoulombConfig N) u)) ∧
      Tendsto (fun n => coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ (ψ n))) atTop
        (𝓝 (coulombAuxiliaryCutoffScalar hR u h)) ∧
      Tendsto (fun n => coulombAuxiliaryCoreCurlValue hβ (ψ n)) atTop
        (𝓝 (coulombCutoffExteriorError β hR u)) := by
  obtain ⟨S, r, hS, hr, hmargin, φ, hφ, hout, hconv⟩ :=
    coulombAuxiliaryCutoff_local_joint_mollification hβ hR huh hu
  let L : Set (CoulombConfig N) := closedBall 0 r + coulombMetricCutoffSupport N R
  have hL : IsCompact L := (isCompact_closedBall _ _).add (coulombMetricCutoffSupport_isCompact N hR)
  have hLS : L ⊆ coulombGraphRadiusSublevel N S := hmargin
  have hLΩ : L ⊆ coulombDomain N := fun z hz => (hLS hz).1
  have hKL : coulombMetricCutoffSupport N R ⊆ L := by
    intro z hz
    exact ⟨0, by simpa only [mem_closedBall, dist_self] using hr.le, z, hz, zero_add z⟩
  let ψ : ℕ → Fin N → TestFunction (coulombDomain N) ℂ ⊤ := fun n b =>
    coulombComplexCoreDensityDiv hβ
      (coulombRestrictGlobalCore (φ n b) (fun z hz => (hLS (hφ n b hz)).1))
  have hin (b : Fin N) : Tendsto (fun n => coulombComplexCoreValue hβ (ψ n b)) atTop
      (𝓝 ((EuclideanSpace.proj (𝕜 := ℂ) b).compLpL 2 (coulombMeasure N β)
        (coulombMetricCutoffL2L hR (CoulombConfig N) u))) := by
    have hi := (tendsto_pi_nhds.mp hconv.fst_nhds) b
    have ht := ((coulombDensityReturnL hβ hS hL hLΩ).continuous.tendsto
      (coulombAuxiliaryCompactInputVolume hβ hR u b)).comp hi
    have he (n : ℕ) : coulombDensityReturnL hβ hS hL hLΩ (dbarVolumeCoreValue (φ n b)) =
        coulombComplexCoreValue hβ (ψ n b) :=
      coulombDensityReturnL_core hβ hS hL hLS (φ n b) (hφ n b)
    have he₀ := coulombDensityReturnL_cutoff_input hβ hR hS hL hLS hKL u b
    simpa only [Function.comp_def, he, he₀] using ht
  have hvalue : Tendsto (fun n => coulombComplexVectorCoreValue hβ (ψ n)) atTop
      (𝓝 (coulombMetricCutoffL2L hR (CoulombConfig N) u)) := by
    apply dbarEuclideanLp_tendsto_of_coordinates
    intro b
    simpa only [coulombComplexVectorCoreValue_coordinate] using hin b
  have houtputs (q : CoulombAuxiliaryJointIndex N) :
      Tendsto (fun n => coulombAuxiliaryCoreJointOutput hβ (ψ n) q) atTop
        (𝓝 (coulombAuxiliaryCutoffJointValue hR u h q)) := by
    have hi := (tendsto_pi_nhds.mp hconv.snd_nhds) q
    have ht := ((dbarVolumeToCoulombCompactL hβ hL hLΩ ℂ).continuous.tendsto
      (coulombAuxiliaryCompactOutputVolume hβ hR u h q)).comp hi
    have he (n : ℕ) : dbarVolumeToCoulombCompactL hβ hL hLΩ ℂ
        (dbarVolumeCoreValue (dbarSystemCoreOutput (coulombAuxiliaryExtendedPrincipal N hβ hS)
          (coulombAuxiliaryExtendedLower N hβ hS) (dbarSystemDirection N) (φ n) q)) =
        coulombComplexCoreValue hβ (coulombAuxiliaryExtendedCoreOutput hβ hS hL.isClosed hLS
          (φ n) (hφ n) q) :=
      coulombCompactCore_volume_transfer hβ hL hLΩ _ (hout n q)
    have hidentify (n : ℕ) : coulombAuxiliaryCoreJointOutput hβ (ψ n) q =
        coulombComplexCoreValue hβ (coulombAuxiliaryExtendedCoreOutput hβ hS hL.isClosed hLS
          (φ n) (hφ n) q) :=
      congrFun (coulombAuxiliaryCoreJointOutput_div_eq_extended hβ hS hL.isClosed hLS (φ n) (hφ n)) q
    have he₀ := coulombCompactOutput_volume_transfer hβ hR hL hLΩ hKL u h q
    simpa only [Function.comp_def, he, ← hidentify, he₀] using ht
  refine ⟨ψ, hvalue, houtputs none, ?_⟩
  apply dbarEuclideanLp_tendsto_of_coordinates
  intro p
  exact houtputs (some p)

end RepulsiveCoulomb
