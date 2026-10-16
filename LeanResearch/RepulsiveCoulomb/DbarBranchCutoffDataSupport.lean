import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryAdjointCutoff
import LeanResearch.RepulsiveCoulomb.DbarBranchCutoffExteriorError
import LeanResearch.RepulsiveCoulomb.DbarBranchCompactL2Support

/-! The cutoff value and both actual operator outputs have one common compact
collision-free support. Their global Lebesgue L2 and L1 membership follows
from the checked local density comparison, rather than an extra assumption. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombMetricCutoffSupport (N : ℕ) (R : ℝ) : Set (CoulombConfig N) :=
  tsupport (coulombMetricCutoff (N := N) R)

theorem coulombMetricCutoffSupport_isCompact (N : ℕ) {R : ℝ} (hR : 0 < R) :
    IsCompact (coulombMetricCutoffSupport N R) := coulombMetricCutoff_hasCompactSupport hR

theorem coulombMetricCutoffSupport_subset (N : ℕ) {R : ℝ} (hR : 0 < R) :
    coulombMetricCutoffSupport N R ⊆ coulombDomain N := (coulombMetricCutoffTest hR).tsupport_subset

theorem coulombMetricCutoff_eq_zero_off_support {N : ℕ} {R : ℝ} {z : CoulombConfig N}
    (hz : z ∉ coulombMetricCutoffSupport N R) : coulombMetricCutoff R z = 0 :=
  image_eq_zero_of_notMem_tsupport hz

theorem coulombMetricCutoffSymbolCore_zero_off_support {N : ℕ} {R : ℝ} (hR : 0 < R)
    {z : CoulombConfig N} (hz : z ∉ coulombMetricCutoffSupport N R) :
    dbarCoreVector (coulombMetricCutoffSymbolCore hR) z = 0 := by
  have he : (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with x hx
    change (coulombMetricCutoff R x : ℂ) = 0
    rw [hx, Pi.zero_apply, Complex.ofReal_zero]
  have hd : fderiv ℝ (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z = 0 := by
    simpa using he.fderiv_eq (𝕜 := ℝ)
  have hb : coulombDbar (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z = 0 := by
    ext i
    change ((fderiv ℝ (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z)
      (coulombCoordinateInjection N i 1) + Complex.I *
      (fderiv ℝ (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z)
      (coulombCoordinateInjection N i Complex.I)) / 2 = 0
    rw [hd]
    simp
  rw [coulombMetricCutoffSymbolCore_vector, hb, map_zero]

theorem coulombMetricCutoffL2L_supported {N : ℕ} {β R : ℝ} (hR : 0 < R)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β)) :
    ∀ᵐ z ∂coulombMeasure N β, z ∉ coulombMetricCutoffSupport N R →
      coulombMetricCutoffL2L hR F f z = 0 := by
  filter_upwards [coulombMetricCutoffL2L_coe hR f] with z hz
  intro hK
  rw [hz, coulombMetricCutoff_eq_zero_off_support hK, zero_smul]

theorem coulombCutoffAdjointOutput_supported {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    ∀ᵐ z ∂coulombMeasure N β, z ∉ coulombMetricCutoffSupport N R →
      (coulombMetricCutoffL2L hR ℂ h - coulombCutoffAdjointErrorL β hR u) z = 0 := by
  filter_upwards [Lp.coeFn_sub (coulombMetricCutoffL2L hR ℂ h) (coulombCutoffAdjointErrorL β hR u),
    coulombMetricCutoffL2L_coe hR h, coulombCutoffAdjointErrorL_coe β hR u] with z hs hθ hZ
  intro hK
  rw [hs, Pi.sub_apply, hθ, hZ, coulombMetricCutoff_eq_zero_off_support hK,
    coulombMetricCutoffSymbolCore_zero_off_support hR hK, zero_smul, inner_zero_left, sub_self]

theorem coulombCutoffExteriorError_supported {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    ∀ᵐ z ∂coulombMeasure N β, z ∉ coulombMetricCutoffSupport N R →
      coulombCutoffExteriorError β hR u z = 0 := by
  filter_upwards [coulombCutoffExteriorError_coe β hR u] with z hz
  intro hK
  rw [hz, coulombMetricCutoffSymbolCore_zero_off_support hR hK]
  ext p
  simp [dbarWedgeTwoForm, dbarVectorWedge]

theorem coulombCutoffData_integrable_volume {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    Integrable (coulombMetricCutoffL2L hR (CoulombConfig N) u : CoulombConfig N → CoulombConfig N) volume ∧
      Integrable (coulombMetricCutoffL2L hR ℂ h - coulombCutoffAdjointErrorL β hR u : CoulombConfig N → ℂ) volume ∧
      Integrable (coulombCutoffExteriorError β hR u : CoulombConfig N → CoulombAuxiliaryTwoForm N) volume := by
  have hK := coulombMetricCutoffSupport_isCompact N hR
  have hKΩ := coulombMetricCutoffSupport_subset N hR
  exact ⟨coulombCompactL2_integrable_volume hβ hK hKΩ _ (coulombMetricCutoffL2L_supported hR u),
    (coulombCompactL2_integrable_volume hβ hK hKΩ _ (coulombCutoffAdjointOutput_supported hR u h)).congr
      ((coulombMeasure_ae_iff hβ).mp
        (Lp.coeFn_sub (coulombMetricCutoffL2L hR ℂ h) (coulombCutoffAdjointErrorL β hR u))),
    coulombCompactL2_integrable_volume hβ hK hKΩ _ (coulombCutoffExteriorError_supported hR u)⟩

theorem coulombCutoffData_memLp_volume {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    MemLp (coulombMetricCutoffL2L hR (CoulombConfig N) u : CoulombConfig N → CoulombConfig N) 2 volume ∧
      MemLp (coulombMetricCutoffL2L hR ℂ h - coulombCutoffAdjointErrorL β hR u : CoulombConfig N → ℂ) 2 volume ∧
      MemLp (coulombCutoffExteriorError β hR u : CoulombConfig N → CoulombAuxiliaryTwoForm N) 2 volume := by
  have hK := coulombMetricCutoffSupport_isCompact N hR
  have hKΩ := coulombMetricCutoffSupport_subset N hR
  exact ⟨coulombCompactL2_memLp_volume hβ hK hKΩ _ (coulombMetricCutoffL2L_supported hR u),
    (coulombCompactL2_memLp_volume hβ hK hKΩ _ (coulombCutoffAdjointOutput_supported hR u h)).ae_eq
      ((coulombMeasure_ae_iff hβ).mp
        (Lp.coeFn_sub (coulombMetricCutoffL2L hR ℂ h) (coulombCutoffAdjointErrorL β hR u))),
    coulombCompactL2_memLp_volume hβ hK hKΩ _ (coulombCutoffExteriorError_supported hR u)⟩

end RepulsiveCoulomb
