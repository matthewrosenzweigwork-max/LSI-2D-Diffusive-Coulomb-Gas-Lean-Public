module

public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalSystemRepresentatives
public import LeanResearch.RepulsiveCoulomb.DbarBranchJointApproximationSupport

@[expose] public section

/-! Actual Lebesgue-L2 classes of compact indicator representatives of the
genuine cutoff input and both outputs. Their weak system and global L1
membership are proved here, ready for the local coefficient extension. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators LinearPMap
namespace RepulsiveCoulomb

def coulombAuxiliaryCompactInputFun {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) : CoulombConfig N → ℂ :=
  (coulombMetricCutoffSupport N R).indicator
    (coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u) b)

def coulombAuxiliaryCompactOutputFun {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) : CoulombConfig N → ℂ :=
  (coulombMetricCutoffSupport N R).indicator (coulombAuxiliaryCutoffJointOutput hR u h q)

theorem coulombAuxiliaryCompactInputFun_memLp {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    MemLp (coulombAuxiliaryCompactInputFun hR u b) 2 volume :=
  MemLp.indicator (coulombMetricCutoffSupport_isCompact N hR).measurableSet
    (coulombCutoffDensityInput_memLp_volume hβ hR u b)

theorem coulombAuxiliaryCompactOutputFun_memLp {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    MemLp (coulombAuxiliaryCompactOutputFun hR u h q) 2 volume :=
  MemLp.indicator (coulombMetricCutoffSupport_isCompact N hR).measurableSet
    (coulombAuxiliaryCutoffJointOutput_memLp_volume hβ hR u h q)

theorem coulombAuxiliaryCompactInputFun_hasCompactSupport {N : ℕ} {β R : ℝ}
    (hR : 0 < R) (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    HasCompactSupport (coulombAuxiliaryCompactInputFun hR u b) :=
  (coulombMetricCutoffSupport_isCompact N hR).of_isClosed_subset isClosed_closure
    (closure_minimal Set.support_indicator_subset (coulombMetricCutoffSupport_isCompact N hR).isClosed)

theorem coulombAuxiliaryCompactOutputFun_hasCompactSupport {N : ℕ} {β R : ℝ}
    (hR : 0 < R) (u : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (h : Lp ℂ 2 (coulombMeasure N β)) (q : CoulombAuxiliaryJointIndex N) :
    HasCompactSupport (coulombAuxiliaryCompactOutputFun hR u h q) :=
  (coulombMetricCutoffSupport_isCompact N hR).of_isClosed_subset isClosed_closure
    (closure_minimal Set.support_indicator_subset (coulombMetricCutoffSupport_isCompact N hR).isClosed)

def coulombAuxiliaryCompactInputVolume {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (coulombAuxiliaryCompactInputFun_memLp hβ hR u b).toLp (coulombAuxiliaryCompactInputFun hR u b)

def coulombAuxiliaryCompactOutputVolume {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) : Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (coulombAuxiliaryCompactOutputFun_memLp hβ hR u h q).toLp (coulombAuxiliaryCompactOutputFun hR u h q)

theorem coulombAuxiliaryCompactInputVolume_coe {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    coulombAuxiliaryCompactInputVolume hβ hR u b =ᵐ[volume] coulombAuxiliaryCompactInputFun hR u b :=
  MemLp.coeFn_toLp _

theorem coulombAuxiliaryCompactOutputVolume_coe {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    coulombAuxiliaryCompactOutputVolume hβ hR u h q =ᵐ[volume] coulombAuxiliaryCompactOutputFun hR u h q :=
  MemLp.coeFn_toLp _

theorem coulombAuxiliaryCompactOutputVolume_integrable {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    Integrable (coulombAuxiliaryCompactOutputVolume hβ hR u h q : CoulombConfig N → ℂ) volume :=
  (dbarCompactInput_integrable (coulombAuxiliaryCompactOutputFun_memLp hβ hR u h q)
    (coulombAuxiliaryCompactOutputFun_hasCompactSupport hR u h q)).congr
      (coulombAuxiliaryCompactOutputVolume_coe hβ hR u h q).symm

theorem coulombAuxiliaryCompactInputVolume_supported {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    ∀ᵐ z ∂volume, z ∉ coulombMetricCutoffSupport N R →
      coulombAuxiliaryCompactInputVolume hβ hR u b z = 0 := by
  filter_upwards [coulombAuxiliaryCompactInputVolume_coe hβ hR u b] with z hz
  intro hK
  rw [hz]
  exact indicator_of_notMem hK _

theorem coulombAuxiliaryCompactOutputVolume_supported {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    ∀ᵐ z ∂volume, z ∉ coulombMetricCutoffSupport N R →
      coulombAuxiliaryCompactOutputVolume hβ hR u h q z = 0 := by
  filter_upwards [coulombAuxiliaryCompactOutputVolume_coe hβ hR u h q] with z hz
  intro hK
  rw [hz]
  exact indicator_of_notMem hK _

theorem coulombAuxiliaryCompactData_local_weakSystem {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    DbarLocalWeakSystem (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
      (dbarSystemDirection N)
      (fun b => (coulombAuxiliaryCompactInputVolume hβ hR u b : CoulombConfig N → ℂ))
      (fun q => (coulombAuxiliaryCompactOutputVolume hβ hR u h q : CoulombConfig N → ℂ)) :=
  dbarLocalWeakSystem_congr_ae (coulombAuxiliaryCutoff_joint_indicator_weakSystem hβ hR huh hu)
    (coulombAuxiliaryCompactInputVolume_coe hβ hR u)
    (coulombAuxiliaryCompactOutputVolume_coe hβ hR u h)

end RepulsiveCoulomb
