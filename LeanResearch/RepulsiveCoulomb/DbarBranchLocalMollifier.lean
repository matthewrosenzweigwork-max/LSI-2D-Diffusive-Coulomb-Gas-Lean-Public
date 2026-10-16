import LeanResearch.RepulsiveCoulomb.DbarBranchLocalDistribution
import LeanResearch.RepulsiveCoulomb.DbarBranchLpMollifier
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Localize an actual Gibbs L2 representative to a compact collision-free set,
then construct honest global smooth convolutions. Identification with the
norm-convergent L2 convolution class is not asserted in this module. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Convolution
namespace RepulsiveCoulomb

theorem coulombL2_indicator_memLp_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (f : Lp ℂ 2 (coulombMeasure N β)) : MemLp (K.indicator (f : CoulombConfig N → ℂ)) 2 volume := by
  apply (memLp_indicator_iff_restrict hK.isClosed.measurableSet).mpr
  exact (Lp.memLp (coulombL2RestrictToVolume hβ hK hKΩ Subset.rfl ℂ f)).ae_eq
    (coulombL2RestrictToVolume_coe hβ hK hKΩ Subset.rfl f)

theorem coulombL2_indicator_integrable_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (f : Lp ℂ 2 (coulombMeasure N β)) : Integrable (K.indicator (f : CoulombConfig N → ℂ)) volume := by
  apply (integrable_indicator_iff hK.isClosed.measurableSet).mpr
  exact (coulombL2_locallyIntegrableOn hβ f).integrableOn_compact_subset hKΩ hK

def coulombL2LocalizeVolume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (f : Lp ℂ 2 (coulombMeasure N β)) : Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (coulombL2_indicator_memLp_volume hβ hK hKΩ f).toLp (K.indicator (f : CoulombConfig N → ℂ))

theorem coulombL2LocalizeVolume_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombL2LocalizeVolume hβ hK hKΩ f =ᵐ[volume] K.indicator (f : CoulombConfig N → ℂ) :=
  MemLp.coeFn_toLp _

def coulombScalarMollify {N : ℕ} {β : ℝ} (K : Set (CoulombConfig N))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β)) : CoulombConfig N → ℂ :=
  ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K.indicator (f : CoulombConfig N → ℂ)

theorem coulombScalarMollify_contDiff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β)) :
    ContDiff ℝ (⊤ : ℕ∞) (coulombScalarMollify K ψ f) := by
  exact (ψ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (n := (⊤ : ℕ∞)) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ψ.contDiff_normed (μ := volume)) (coulombL2_indicator_integrable_volume hβ hK hKΩ f).locallyIntegrable

end RepulsiveCoulomb
