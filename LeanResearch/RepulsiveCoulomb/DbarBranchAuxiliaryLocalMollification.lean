module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCompactData

@[expose] public section

/-! Actual simultaneous local mollification of a genuine auxiliary adjoint
and compatibility-domain pair, after one fixed proper cutoff. The common
support margin and coefficient extension are constructed, not assumed. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped Topology BigOperators Pointwise LinearPMap
namespace RepulsiveCoulomb

def coulombAuxiliaryExtendedPrincipal (N : ℕ) {β S : ℝ} (hβ : 0 < β) (hS : 0 < S) :
    CoulombAuxiliaryJointIndex N → Fin N → (Fin N × Bool) →
      TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
  fun q b d => coulombCoefficientExtensionGlobal (coulombAuxiliaryJointPrincipal β q b d)
    (fun z hz => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hz) hS

def coulombAuxiliaryExtendedLower (N : ℕ) {β S : ℝ} (hβ : 0 < β) (hS : 0 < S) :
    CoulombAuxiliaryJointIndex N → Fin N → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
  fun q b => coulombCoefficientExtensionGlobal (coulombAuxiliaryJointLower β q b)
    (fun z hz => coulombAuxiliaryJointLower_contDiffAt hβ q b hz) hS

theorem coulombAuxiliaryCompactData_global_weakSystem {N : ℕ} {β R S : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hS : 0 < S)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ)
    (hKS : coulombMetricCutoffSupport N R ⊆ coulombGraphRadiusSublevel N S) :
    DbarVolumeWeakSystem (coulombAuxiliaryExtendedPrincipal N hβ hS)
      (coulombAuxiliaryExtendedLower N hβ hS) (dbarSystemDirection N)
      (coulombAuxiliaryCompactInputVolume hβ hR u) (coulombAuxiliaryCompactOutputVolume hβ hR u h) :=
  dbarLocalWeakSystem_compact_extension (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
    (fun q b d z hz => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hz)
    (fun q b z hz => coulombAuxiliaryJointLower_contDiffAt hβ q b hz)
    (dbarSystemDirection N) _ _ (coulombAuxiliaryCompactData_local_weakSystem hβ hR huh hu)
    hS hKS (coulombAuxiliaryCompactInputVolume_supported hβ hR u)
      (coulombAuxiliaryCompactOutputVolume_supported hβ hR u h)

theorem coulombAuxiliaryCutoff_local_joint_mollification {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    ∃ (S r : ℝ) (hS : 0 < S), 0 < r ∧
      closedBall 0 r + coulombMetricCutoffSupport N R ⊆ coulombGraphRadiusSublevel N S ∧
      ∃ φ : ℕ → Fin N → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤,
        (∀ n b, tsupport (φ n b : CoulombConfig N → ℂ) ⊆ closedBall 0 r + coulombMetricCutoffSupport N R) ∧
        (∀ n q, tsupport (dbarSystemCoreOutput (coulombAuxiliaryExtendedPrincipal N hβ hS)
          (coulombAuxiliaryExtendedLower N hβ hS) (dbarSystemDirection N) (φ n) q : CoulombConfig N → ℂ) ⊆
            closedBall 0 r + coulombMetricCutoffSupport N R) ∧
        Tendsto (fun n => ((fun b => dbarVolumeCoreValue (φ n b)),
          (fun q => dbarVolumeCoreValue (dbarSystemCoreOutput (coulombAuxiliaryExtendedPrincipal N hβ hS)
            (coulombAuxiliaryExtendedLower N hβ hS) (dbarSystemDirection N) (φ n) q))))
          atTop (𝓝 (coulombAuxiliaryCompactInputVolume hβ hR u, coulombAuxiliaryCompactOutputVolume hβ hR u h)) := by
  have hK := coulombMetricCutoffSupport_isCompact N hR
  have hKΩ := coulombMetricCutoffSupport_subset N hR
  obtain ⟨S, r, hS, hr, hmargin⟩ := coulombCompact_common_metric_margin hK hKΩ
  have hKS : coulombMetricCutoffSupport N R ⊆ coulombGraphRadiusSublevel N S := by
    intro z hz
    apply hmargin
    exact ⟨0, by simpa only [mem_closedBall, dist_self] using hr.le, z, hz, zero_add z⟩
  refine ⟨S, r, hS, hr, hmargin, ?_⟩
  exact dbarSystem_joint_approximation_with_support
    (coulombAuxiliaryExtendedPrincipal N hβ hS) (coulombAuxiliaryExtendedLower N hβ hS)
    (dbarSystemDirection N) (coulombAuxiliaryCompactInputFun hR u)
    (coulombAuxiliaryCompactInputFun_memLp hβ hR u) hK (fun _ => Set.support_indicator_subset)
    (coulombAuxiliaryCompactOutputVolume hβ hR u h)
    (coulombAuxiliaryCompactData_global_weakSystem hβ hR hS huh hu hKS)
    (coulombAuxiliaryCompactOutputVolume_integrable hβ hR u h) hr

end RepulsiveCoulomb
