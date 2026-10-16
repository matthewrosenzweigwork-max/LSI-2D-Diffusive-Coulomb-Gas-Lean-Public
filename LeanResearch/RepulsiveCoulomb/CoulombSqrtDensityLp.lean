import LeanResearch.RepulsiveCoulomb.CoulombSqrtDensityContinuity
import LeanResearch.RepulsiveCoulomb.CoulombGroundStateL2

/-! A fixed ambient volume-L2 realization of normalized square-root Gibbs
weights and genuine strong continuity at every positive temperature.
The arbitrary zero branch outside positive temperatures is not used. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open PeriodicAttractiveLogGas
open scoped Topology
namespace RepulsiveCoulomb

def coulombSqrtDensityLp (N : ℕ) (β : ℝ) : Lp ℝ 2 (volume : Measure (CoulombConfig N)) :=
  if hβ : 0 < β then (coulombSqrtDensity_memLp N hβ).toLp (fun z => Real.sqrt (coulombDensity N β z))
  else 0

theorem coulombSqrtDensityLp_coe {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    coulombSqrtDensityLp N β =ᵐ[volume] fun z => Real.sqrt (coulombDensity N β z) := by
  rw [coulombSqrtDensityLp, dif_pos hβ]
  exact MemLp.coeFn_toLp _

theorem coulombSqrtDensityLp_sub_norm_sq {N : ℕ} {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    ‖coulombSqrtDensityLp N γ - coulombSqrtDensityLp N β‖ ^ 2 =
      ∫ z : CoulombConfig N,
        (Real.sqrt (coulombDensity N γ z) - Real.sqrt (coulombDensity N β z)) ^ 2 := by
  rw [← integral_sq_eq_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (coulombSqrtDensityLp N γ) (coulombSqrtDensityLp N β),
    coulombSqrtDensityLp_coe hγ, coulombSqrtDensityLp_coe hβ] with z hs hγz hβz
  simp only [hs, Pi.sub_apply, hγz, hβz]

theorem coulombSqrtDensityLp_continuousAt {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    ContinuousAt (coulombSqrtDensityLp N) β := by
  have he : (fun γ : ℝ => ‖coulombSqrtDensityLp N γ - coulombSqrtDensityLp N β‖ ^ 2) =ᶠ[𝓝 β]
      fun γ : ℝ => ∫ z : CoulombConfig N,
        (Real.sqrt (coulombDensity N γ z) - Real.sqrt (coulombDensity N β z)) ^ 2 := by
    filter_upwards [lt_mem_nhds hβ] with γ hγ
    exact coulombSqrtDensityLp_sub_norm_sq hβ hγ
  have hs := (coulombSqrtDensity_squareDifference_tendsto (N := N) hβ).congr' he.symm
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

theorem coulombGroundStateL2_mean_pairing {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) :
    inner ℝ (coulombGroundStateL2 hβ u) (coulombSqrtDensityLp N β) =
      ∫ z, u z ∂coulombMeasure N β := by
  letI := coulombMeasure_isProbability (N := N) hβ
  rw [L2.inner_def, coulombMeasure_integral_density_of_integrable hβ _
    (MemLp.integrable (by norm_num) (Lp.memLp u))]
  apply integral_congr_ae
  filter_upwards [coulombGroundStateL2_coe hβ u, coulombSqrtDensityLp_coe hβ] with z hg hs
  rw [hg, hs]
  simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
  calc
    _ = (Real.sqrt (coulombDensity N β z)) ^ 2 * u z := by ring
    _ = _ := by rw [Real.sq_sqrt (coulombDensity_nonneg β z)]

end RepulsiveCoulomb
