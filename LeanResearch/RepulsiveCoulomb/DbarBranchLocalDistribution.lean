import LeanResearch.RepulsiveCoulomb.CoulombLocalL2
import Mathlib.Analysis.Distribution.Distribution

/-! The actual weighted L2 space embeds injectively into Lebesgue distributions
on the collision complement. No distribution is formed from a non-locally-
integrable representative, and no Haar property is imposed on the Gibbs law. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombL2_locallyIntegrableOn {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β)) :
    LocallyIntegrableOn (f : CoulombConfig N → F) (coulombDomain N) volume := by
  apply (locallyIntegrableOn_iff (coulombDomain N).isOpen.isLocallyClosed).mpr
  intro K hKΩ hK
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  let fK := coulombL2RestrictToVolume hβ hK hKΩ (Subset.rfl : K ⊆ K) F f
  exact (MemLp.integrable (by norm_num) (Lp.memLp fK)).congr
    (coulombL2RestrictToVolume_coe hβ hK hKΩ (Subset.rfl : K ⊆ K) f)

def coulombL2Distribution {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β)) : Distribution (coulombDomain N) F ⊤ :=
  Distribution.ofFun (coulombDomain N) f volume ⊤

theorem coulombL2Distribution_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β)) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombL2Distribution hβ f φ = ∫ z, φ z • f z :=
  Distribution.ofFun_apply (coulombL2_locallyIntegrableOn hβ f)

theorem coulombL2Distribution_injective {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    Function.Injective (coulombL2Distribution (N := N) (F := F) hβ) := by
  intro f g h
  have hfg := Distribution.ofFun_injective
    (coulombL2_locallyIntegrableOn hβ f) (coulombL2_locallyIntegrableOn hβ g) h
  have hvol : f =ᵐ[volume] g := by
    have hfg' := (ae_restrict_iff' (coulombDomain N).isOpen.measurableSet).mp hfg
    filter_upwards [hfg', coulombDomain_ae N] with z hz hΩ
    exact hz hΩ
  exact Lp.ext ((coulombMeasure_ae_iff hβ).mpr hvol)

theorem coulombL2Distribution_add {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : Lp F 2 (coulombMeasure N β)) :
    coulombL2Distribution hβ (f + g) =
      coulombL2Distribution hβ f + coulombL2Distribution hβ g := by
  change Distribution.ofFun (coulombDomain N) (f + g) volume ⊤ = _
  rw [Distribution.ofFun_congr_ae (ae_restrict_of_ae
    ((coulombMeasure_ae_iff hβ).mp (Lp.coeFn_add f g)))]
  exact Distribution.ofFun_add (coulombL2_locallyIntegrableOn hβ f)
    (coulombL2_locallyIntegrableOn hβ g)

theorem coulombL2Distribution_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (f : Lp F 2 (coulombMeasure N β)) :
    coulombL2Distribution hβ (c • f) = c • coulombL2Distribution hβ f := by
  change Distribution.ofFun (coulombDomain N) (c • f) volume ⊤ = _
  rw [Distribution.ofFun_congr_ae (ae_restrict_of_ae
    ((coulombMeasure_ae_iff hβ).mp (Lp.coeFn_smul c f)))]
  exact Distribution.ofFun_smul c

def coulombL2DistributionLinear {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 (coulombMeasure N β) →ₗ[ℝ] Distribution (coulombDomain N) F ⊤ where
  toFun := coulombL2Distribution hβ
  map_add' := coulombL2Distribution_add hβ
  map_smul' := coulombL2Distribution_smul hβ

end RepulsiveCoulomb
