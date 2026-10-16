module

public import LeanResearch.RepulsiveCoulomb.DbarBranchOutputWeakSystem

@[expose] public section

/-! Local weak systems depend only on Lebesgue-a.e. representatives. Actual
compact cutoff data therefore have indicator representatives with literal
compact support, as required by the common-support mollifier construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem dbarLocalWeakSystem_congr_ae {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    {A : κ → ι → δ → CoulombConfig N → ℂ} {B : κ → ι → CoulombConfig N → ℂ}
    {v : δ → CoulombConfig N} {u u' : ι → CoulombConfig N → ℂ}
    {g g' : κ → CoulombConfig N → ℂ}
    (hweak : DbarLocalWeakSystem A B v u g)
    (hu : ∀ b, u' b =ᵐ[volume] u b) (hg : ∀ a, g' a =ᵐ[volume] g a) :
    DbarLocalWeakSystem A B v u' g' := by
  intro a φ
  have hleft : (∫ z, φ z • g' a z) = ∫ z, φ z • g a z :=
    integral_congr_ae ((hg a).mono fun z hz => by
      dsimp only
      rw [hz])
  have hfirst (b : ι) (d : δ) :
      (∫ z, ((fderiv ℝ (φ : CoulombConfig N → ℝ) z (v d)) • A a b d z +
        φ z • fderiv ℝ (A a b d) z (v d)) * u' b z) =
      ∫ z, ((fderiv ℝ (φ : CoulombConfig N → ℝ) z (v d)) • A a b d z +
        φ z • fderiv ℝ (A a b d) z (v d)) * u b z :=
    integral_congr_ae ((hu b).mono fun z hz => by
      dsimp only
      rw [hz])
  have hzero (b : ι) : (∫ z, φ z • (B a b z * u' b z)) =
      ∫ z, φ z • (B a b z * u b z) :=
    integral_congr_ae ((hu b).mono fun z hz => by
      dsimp only
      rw [hz])
  simp_rw [hleft, hfirst, hzero]
  exact hweak a φ

theorem coulombCutoffDensityInput_supported {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    ∀ᵐ z ∂volume, z ∉ coulombMetricCutoffSupport N R →
      coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u) b z = 0 := by
  filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombMetricCutoffL2L_supported hR u)] with z hz
  intro hK
  change (coulombDensity N β z : ℂ) * (coulombMetricCutoffL2L hR (CoulombConfig N) u z) b = 0
  rw [hz hK]
  simp

theorem coulombAuxiliaryCutoffJointOutput_supported {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    ∀ᵐ z ∂volume, z ∉ coulombMetricCutoffSupport N R →
      coulombAuxiliaryCutoffJointOutput hR u h q z = 0 := by
  cases q with
  | none => exact (coulombMeasure_ae_iff hβ).mp (coulombCutoffAdjointOutput_supported hR u h)
  | some p =>
      filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombCutoffExteriorError_supported hR u)] with z hz
      intro hK
      change coulombCutoffExteriorError β hR u z p = 0
      rw [hz hK]
      rfl

theorem dbarIndicator_eq_of_ae_supported {N : ℕ} {K : Set (CoulombConfig N)}
    {f : CoulombConfig N → ℂ} (hf : ∀ᵐ z ∂volume, z ∉ K → f z = 0) :
    K.indicator f =ᵐ[volume] f := by
  filter_upwards [hf] with z hz
  by_cases h : z ∈ K
  · exact indicator_of_mem h f
  · rw [indicator_of_notMem h, hz h]

theorem coulombAuxiliaryCutoff_joint_indicator_weakSystem {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    DbarLocalWeakSystem (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
      (dbarSystemDirection N)
      (fun b => (coulombMetricCutoffSupport N R).indicator
        (coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u) b))
      (fun q => (coulombMetricCutoffSupport N R).indicator (coulombAuxiliaryCutoffJointOutput hR u h q)) :=
  dbarLocalWeakSystem_congr_ae (coulombAuxiliaryCutoff_joint_weakSystem hβ hR huh hu)
    (fun b => dbarIndicator_eq_of_ae_supported (coulombCutoffDensityInput_supported hβ hR u b))
    (fun q => dbarIndicator_eq_of_ae_supported (coulombAuxiliaryCutoffJointOutput_supported hβ hR u h q))

end RepulsiveCoulomb
